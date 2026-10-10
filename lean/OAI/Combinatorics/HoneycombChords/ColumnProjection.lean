import OAI.Combinatorics.HoneycombChords.ColumnExpansion

namespace OAI

/-! Column projection for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open scoped Matrix
lemma matrixPath_sum {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    {n : ℕ} (K : Fin n→β→Matrix α α ℂ) (a b : α) :
    matrixPath (fun i=>∑ q,K i q) a b=∑ qs : Fin n→β,matrixPath (fun i=>K i (qs i)) a b := by
  classical
  unfold matrixPath
  simp only [Matrix.sum_apply]
  simp_rw [Fintype.prod_sum,Finset.ite_sum_zero]
  rw [Finset.sum_comm]
lemma matrixPath_scale {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (K : Fin n→Matrix α α ℂ) (c : Fin n→ℂ) (a b : α) :
    matrixPath (fun i=>c i • K i) a b=(∏ i,c i)*matrixPath K a b := by
  classical
  unfold matrixPath
  simp only [Matrix.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  split_ifs <;> simp
lemma matrixPath_restrict {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (K : Fin n→Matrix α α ℂ) (P : Fin n→Prop) [DecidablePred P] (a b : α) :
    matrixPath (fun i=>if P i then K i else 0) a b=if ∀ i,P i then matrixPath K a b else 0 := by
  classical
  by_cases hp : ∀ i,P i
  · simp [hp]
  obtain ⟨i,hi⟩:=not_forall.mp hp
  simp only [ite_eq_right hp,matrixPath]
  apply Finset.sum_eq_zero
  intro τ hτ
  split_ifs
  · apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]
  · rfl
noncomputable def weightedColumn {H : ℕ} (q : Fin H→Shape) : Matrix (Column H) (Column H) ℂ :=
  (kappa:ℂ)^(∑ j,(q j).visits) • chosenColumnKernel q 1 1
lemma weighted_chosen_matrixPath {W H : ℕ} (cfg : Cell W H→Shape) (west east : Column H) :
    (kappa:ℂ)^(∑ t,(cfg t).visits)*chosenPartition cfg west east (fun _=>1) (fun _=>1)=
      matrixPath (fun i=>weightedColumn (fun j=>cfg (i,j))) west east := by
  rw [chosenPartition_eq_matrixPath]
  unfold weightedColumn
  rw [matrixPath_scale,Finset.prod_pow_eq_pow_sum,Fintype.sum_prod_type]

lemma chosen_column_sum (H : ℕ) :
    (∑ q : Fin H→Shape,weightedColumn q)=columnKernel H 1 1 := by
  classical
  ext west east
  simp only [Matrix.sum_apply,weightedColumn,Matrix.smul_apply,smul_eq_mul,chosenColumnKernel]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold columnKernel
  apply Finset.sum_congr rfl
  intro vertical hvertical
  by_cases hh : (Fin.snoc (α:=fun _=>Fin 3) vertical 1) 0=1
  · simp only [hh,ite_true]
    unfold columnProduct chosenColumnProduct
    simp_rw [physical_tile_expansion]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.prod_mul_distrib,←Finset.prod_pow_eq_pow_sum]
  · simp [hh]

lemma shape_columns_sum {W H : ℕ} (Q : Fin W→(Fin H→Shape)→Prop) [∀ i,DecidablePred (Q i)]
    (west east : Column H) :
    (∑ cfg : Cell W H→Shape,if ∀ i,Q i (fun j=>cfg (i,j)) then
      (kappa:ℂ)^(∑ t,(cfg t).visits)*chosenPartition cfg west east (fun _=>1) (fun _=>1) else 0)=
    matrixPath (fun i=>∑ q : Fin H→Shape,if Q i q then weightedColumn q else 0) west east := by
  classical
  rw [matrixPath_sum]
  let e : (Cell W H→Shape) ≃ (Fin W→Fin H→Shape) := Equiv.curry _ _ _
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro cfg hcfg
  have he (i : Fin W) : e cfg i=fun j=>cfg (i,j) := rfl
  simp only [he]
  rw [matrixPath_restrict,←weighted_chosen_matrixPath]
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open scoped Matrix
lemma empty_chosenColumn (H : ℕ) (west east : Column H) :
    chosenColumnKernel (fun _ : Fin H=>Shape.empty) 1 1 west east=
      if west=(fun _=>1) ∧ east=(fun _=>1) then 1 else 0 := by
  classical
  have hs : Fin.snoc (α:=fun _=>Fin 3) (fun _ : Fin H=>1) 1 = (fun _ : Fin (H+1)=>1) := by
    funext j
    simp [Fin.snoc]
  unfold chosenColumnKernel
  rw [Finset.sum_eq_single (fun _=>1)]
  · simp only [hs,ite_true]
    unfold chosenColumnProduct
    have hh (j : Fin H) : shapeTensor Shape.empty (west j) 1 1 (east j)=
        if west j=1 ∧ east j=1 then 1 else 0 := by
      simp only [shapeTensor,Planar.vacant,ite_and,mul_ite,mul_one,mul_zero]; split_ifs <;> rfl
    simp only [hs,hh]
    rw [Fintype.prod_ite_zero]
    have ht : (∀ j,west j=1 ∧ east j=1) ↔ west=(fun _=>1) ∧ east=(fun _=>1) := by
      constructor
      · intro h;exact ⟨funext (fun j=>(h j).1),funext (fun j=>(h j).2)⟩
      · rintro ⟨rfl,rfl⟩;simp
    simp [ht]
  · intro vertical hv hne
    split_ifs
    · unfold chosenColumnProduct
      have hn : ∃ j,vertical j≠1 := by
        by_contra h
        push Not at h
        exact hne (funext h)
      obtain ⟨j,hj⟩:=hn
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [shapeTensor,Planar.vacant,hj]
    · rfl
  · simp
lemma weighted_emptyColumn (H : ℕ) :
    weightedColumn (fun _ : Fin H=>Shape.empty)=
      fun west east=>if west=(fun _=>1) ∧ east=(fun _=>1) then 1 else 0 := by
  classical
  ext west east
  simp [weightedColumn,Shape.visits,empty_chosenColumn]

lemma constant_cut_product {α : Type*} [Monoid α] (A E : α) {n : ℕ} (k : Fin (n+1)) :
    (List.ofFn (fun i : Fin (n+1)=>if i=k then E else A)).prod=A^k.val*E*A^(n-k.val) := by
  classical
  induction n with
  | zero => simp [Fin.eq_zero k]
  | succ n ih =>
    refine Fin.cases ?_ (fun k=>?_) k
    · rw [List.ofFn_succ,List.prod_cons]
      simp [Fin.succ_ne_zero,List.ofFn_const,List.prod_replicate,pow_succ']
    · rw [List.ofFn_succ,List.prod_cons]
      simp only [(Fin.succ_ne_zero k).symm,ite_false,Fin.succ_inj]
      rw [ih]
      simp only [Fin.val_succ,Nat.add_sub_add_right,pow_succ']
      simp only [mul_assoc]
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open scoped Matrix

def transposeConfigurationEquiv (W H : ℕ) : (Cell W H→Shape) ≃ (Cell H W→Shape) where
  toFun := transposeConfiguration
  invFun := transposeConfiguration
  left_inv := by intro cfg;funext t;exact transposeShape_involutive _
  right_inv := by intro cfg;funext t;exact transposeShape_involutive _

open Classical in
lemma empty_column_shape_sum {W H : ℕ} (k : Fin (W+1)) (west east : Column H) :
    (∑ cfg : Cell (W+1) H→Shape,if ∀ j,cfg (k,j)=.empty then
      (kappa:ℂ)^(∑ t,(cfg t).visits)*chosenPartition cfg west east (fun _=>1) (fun _=>1) else 0)=
      (rowTransfer H^k.val * weightedColumn (H:=H) (fun _=>.empty) * rowTransfer H^(W-k.val)) west east := by
  classical
  have hQ (cfg : Cell (W+1) H→Shape) : (∀ j,cfg (k,j)=.empty) ↔
      ∀ i : Fin (W+1),i=k → (fun j=>cfg (i,j))=fun _=>.empty := by
    constructor
    · intro hh i hi;subst i;exact funext hh
    · intro hh j;exact congrFun (hh k rfl) j
  simp only [hQ]
  refine Eq.trans ?_ ((shape_columns_sum (fun i q=>i=k → q=(fun _=>.empty)) west east).trans ?_)
  · apply Finset.sum_congr rfl
    intro cfg hcfg
    by_cases hp : ∀ i : Fin (W+1),i=k → (fun j=>cfg (i,j))=fun _=>Shape.empty
    · simp only [ite_eq_left hp]
    · simp only [ite_eq_right hp]
  have hK (i : Fin (W+1)) : (∑ q : Fin H→Shape,if i=k → q=(fun _=>.empty) then weightedColumn q else 0)=
      if i=k then weightedColumn (H:=H) (fun _=>.empty) else rowTransfer H := by
    by_cases hi : i=k
    · simp [hi]
    · simp [hi,chosen_column_sum,rowTransfer]
  have hks : (fun i : Fin (W+1)=>∑ q : Fin H→Shape,if i=k → q=(fun _=>.empty) then weightedColumn q else 0)=
      (fun i=>if i=k then weightedColumn (H:=H) (fun _=>.empty) else rowTransfer H) := funext hK
  rw [hks,matrixPath_eq_prod]
  exact congrArg (fun A : Matrix (Column H) (Column H) ℂ=>A west east)
    (constant_cut_product (rowTransfer H) (weightedColumn (H:=H) (fun _=>.empty)) k)

lemma vacuum_cut_entry {H : ℕ} (A B : Matrix (Column H) (Column H) ℂ) (a b : Column H) :
    (A * weightedColumn (fun _ : Fin H=>.empty) * B) a b=A a (fun _=>1)*B (fun _=>1) b := by
  classical
  rw [weighted_emptyColumn]
  change (∑ j,(∑ i,A a i * (if i=(fun _=>1) ∧ j=(fun _=>1) then 1 else 0))*B j b)=_
  simp [ite_and,mul_ite,ite_mul]

open Classical in
lemma empty_row_shape_sum {W H : ℕ} (k : Fin (H+1)) (south north : Column W) :
    (∑ cfg : Cell W (H+1)→Shape,if ∀ i,cfg (i,k)=.empty then
      (kappa:ℂ)^(∑ t,(cfg t).visits)*chosenPartition cfg (fun _=>1) (fun _=>1) south north else 0)=
      (rowTransfer W^k.val) south (fun _=>1)*(rowTransfer W^(H-k.val)) (fun _=>1) north := by
  classical
  rw [←vacuum_cut_entry]
  rw [←empty_column_shape_sum]
  rw [←(transposeConfigurationEquiv W (H+1)).sum_comp]
  apply Finset.sum_congr rfl
  intro cfg hcfg
  have he : transposeConfigurationEquiv W (H+1) cfg=transposeConfiguration cfg := rfl
  simp only [he,transposeConfiguration,transposeShape_empty]
  rw [weighted_chosen_transpose]
  rfl
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology
open scoped Matrix
noncomputable def hardAssignment {W H : ℕ} (south north : Column W) : Assignment W (H+1) :=
  (Sum.elim (fun _=>1) (fun p=>if p.2=0 then south p.1 else if p.2=Fin.last (H+1) then north p.1 else 1),fun _=>1)
lemma hardAssignment_boundary {W H : ℕ} (south north : Column W) :
    (fun j=> (hardAssignment (H:=H) south north).1 (.inl (0,j)))=(fun _=>1) ∧
    (fun j=> (hardAssignment (H:=H) south north).1 (.inl (Fin.last W,j)))=(fun _=>1) ∧
    (fun i=> (hardAssignment (H:=H) south north).1 (.inr (i,0)))=south ∧
    (fun i=> (hardAssignment (H:=H) south north).1 (.inr (i,Fin.last (H+1))))=north := by
  have hn : (Fin.last (H+1) : Fin (H+1+1))≠0 := by intro h;have := congrArg Fin.val h;simp at this
  simp [hardAssignment,hn]
lemma hardAssignment_walls {W H : ℕ} (south north : Column (W+1)) :
    (∀ j,assignmentSpins (hardAssignment (H:=H) south north) (westPort W H j).wire=1) ∧
    (∀ j,assignmentSpins (hardAssignment (H:=H) south north) (eastPort W H j).wire=1) := by
  constructor <;> intro j
  · rw [westPort_wire]
    simp [assignmentSpins,spins_wire,hardAssignment]
  · rw [eastPort_wire]
    simp [assignmentSpins,spins_wire,hardAssignment]
lemma hardAssignment_shape {W H : ℕ} (south north : Column W) (cfg : Cell W (H+1)→Shape) :
    (∑ x,relativeTerm cfg (hardAssignment south north) x)=
      (kappa:ℂ)^(∑ t,(cfg t).visits)*chosenPartition cfg (fun _=>1) (fun _=>1) south north := by
  simp only [relativeTerm_eq_masked]
  rw [sum_maskedTerm]
  obtain ⟨hw,he,hs,hn⟩:=hardAssignment_boundary (H:=H) south north
  rw [hw,he,hs,hn]

lemma transfer_cut_difference {W H : ℕ} (south north : Column W) (k : Fin (H+1)) :
    (rowTransfer W^(H+1)) south north-
      (rowTransfer W^k.val) south (fun _=>1)*(rowTransfer W^(H-k.val)) (fun _=>1) north=
    restrictedPartition (hardAssignment south north) (fun cfg=>∃ i,cfg (i,k)≠.empty) := by
  classical
  rw [←prescribed_hard_transfer, prescribed_shape_expansion, ←empty_row_shape_sum]
  unfold restrictedPartition
  simp only [hardAssignment_shape]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro cfg hcfg
  by_cases h : ∀ i,cfg (i,k)=.empty
  · simp [h]
  · have hh : ∃ i,cfg (i,k)≠.empty := not_forall.mp h
    simp [h,hh]

theorem actual_transfer_cut_bound (W H : ℕ) (south north : Column (W+1)) :
    ‖(rowTransfer (W+1)^(H+1)) south north-
      (rowTransfer (W+1)^(H/2)) south (fun _=>1)*
      (rowTransfer (W+1)^(H-H/2)) (fun _=>1) north‖ ≤ middleErrorBound W H := by
  rw [transfer_cut_difference south north (⟨H/2,by omega⟩ : Fin (H+1))]
  obtain ⟨hw,he⟩:=hardAssignment_walls (H:=H) south north
  exact actual_middle_row_bound _ hw he
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology
lemma pool_cutrow_weight {W H k j : ℕ} (hk : k≤j) (hj : j+k≤H) (a : OnePathPool W H)
    (hm : ∃ v∈recoverTrace a,v.2.1=(j:ℤ)) :
    badPoolWeight k a=poolWeight a := by
  classical
  obtain ⟨v,hv,hy⟩:=hm
  rcases a with (a|a)|(a|a)
  · change archTailWeight k a=archPoolWeight a
    unfold archTailWeight
    rw [ite_eq_left]
    have hh:=poolArchHeight_ge a hv
    omega
  · change archTailWeight k a=archPoolWeight a
    unfold archTailWeight
    rw [ite_eq_left]
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hv
    have hh:=poolArchHeight_ge a hu
    change (H:ℤ)-u.2.1=(j:ℤ) at hy
    omega
  · rfl
  · rfl
lemma HardChord.cutrow_weight {W H k j : ℕ} (hk : k≤j) (hj : j+k≤H) (c : HardChord W H)
    (hm : ∃ v∈c.val.chord.val,v.2.1=(j:ℤ)) :
    badPoolWeight k c.encode=poolWeight c.encode := by
  apply pool_cutrow_weight hk hj
  simpa only [c.recover_encode] using hm
lemma markTotal_tendsto {U V : ℕ→ℝ} {u v : ℝ}
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 v)) (n : ℕ) :
    Tendsto (fun H=>ListBound.markTotal (U H) (V H) n) atTop (𝓝 (ListBound.markTotal u v n)) := by
  induction n with
  | zero => exact tendsto_const_nhds
  | succ n ih => exact (hV.mul (hU.pow n)).add (hU.mul ih)
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology
namespace AnyRow
noncomputable def badHardWeight (k : ℕ) {W H : ℕ} (c : BoundaryChord W H) : ℝ := by
  classical
  exact if hp : EndPort c.source ∧ EndPort c.target then
    badPoolWeight k (HardChord.encode ⟨c,hp⟩) else 0
lemma badHardWeight_nonnegative (k : ℕ) {W H : ℕ} (c : BoundaryChord W H) : 0≤badHardWeight k c := by
  unfold badHardWeight
  split_ifs
  · exact badPoolWeight_nonnegative _
  · exact le_refl _
lemma sum_badHardWeight_le (W H k : ℕ) :
    (∑ c : BoundaryChord W H,badHardWeight k c)≤badPoolMass W H k := by
  classical
  have he : (∑ c : BoundaryChord W H,badHardWeight k c)=
      ∑ c : HardChord W H,badPoolWeight k c.encode := by
    have hs : ∀ c : HardChord W H,badHardWeight k c.val=badPoolWeight k c.encode := by
      rintro ⟨c,hp⟩
      simp only [badHardWeight,dite_eq_left hp]
    calc
      _ = ∑ c : BoundaryChord W H,if EndPort c.source ∧ EndPort c.target then badHardWeight k c else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hp : EndPort c.source ∧ EndPort c.target <;> simp [badHardWeight,hp]
      _ = ∑ c : HardChord W H,badHardWeight k c.val :=
        by
          rw [←Finset.sum_filter]
          exact Finset.sum_subtype _ (by simp) _
      _ = _ := Finset.sum_congr rfl (fun c hc=>hs c)
  rw [he]
  calc
    _ = ∑ a∈Finset.univ.image (HardChord.encode (W:=W) (H:=H)),badPoolWeight k a :=
      (Finset.sum_image (HardChord.encode_injective W H).injOn).symm
    _ ≤ _ := (badPool_summable W H k).sum_le_tsum _ (fun a ha=>badPoolWeight_nonnegative a)
lemma hardWeight_le_bad {W H k j : ℕ} (hk : k≤j) (hj : j+k≤H) (c : BoundaryChord W H)
    (hp : EndPort c.source ∧ EndPort c.target)
    (hm : ∃ v∈c.chord.val,v.2.1=(j:ℤ)) : hardWeight c≤badHardWeight k c := by
  classical
  let a : HardChord W H:=⟨c,hp⟩
  have hh:=a.cutrow_weight hk hj hm
  unfold hardWeight badHardWeight
  rw [ite_eq_left hp,dite_eq_left hp]
  change kappa^c.chord.val.length≤badPoolWeight k a.encode
  rw [hh,poolWeight,a.encode_length]

noncomputable def rowErrorBound (W H k : ℕ) : ℝ :=
  ListBound.markTotal (1+poolMass W H) (badPoolMass W H k) (2*(W+1))

theorem actual_cutrow_bound {W H k j : ℕ} (hk : k≤j) (hj : j+k≤H) (x₀ : Assignment (W+1) (H+1))
    (hw : ∀ j,assignmentSpins x₀ (westPort W H j).wire=1)
    (he : ∀ j,assignmentSpins x₀ (eastPort W H j).wire=1) :
    ‖restrictedPartition x₀ (fun cfg=>∃ i,cfg (i,⟨j,by omega⟩)≠.empty)‖≤ rowErrorBound W H k := by
  classical
  let Q := fun cfg : Cell (W+1) (H+1)→Shape=>∃ i,cfg (i,⟨j,by omega⟩)≠.empty
  obtain ⟨S,hS,hB⟩:=actual_restricted_component_bound x₀ Q
  have walls : ∀ cs∈S,∃ x cfg,SelectedSystem x cs ∧ Matches cfg x.1 x.2 ∧ Q cfg ∧
      (∀ j,assignmentSpins x (westPort W H j).wire=1) ∧
      (∀ j,assignmentSpins x (eastPort W H j).wire=1) := by
    intro cs hc
    obtain ⟨x,cfg,hx,hm,hq,hs⟩:=hS cs hc
    exact ⟨x,cfg,hs,hm,hq,fun j=>(sameBoundary_port hx _).trans (hw j),
      fun j=>(sameBoundary_port hx _).trans (he j)⟩
  have hn : ∀ cs∈S,cs.length≤2*(W+1) := by
    intro cs hc
    obtain ⟨x,cfg,hx,hm,hq,hw,he⟩:=walls cs hc
    exact hx.length_le_width hw he
  have hp : ∀ cs∈S,kappa^(systemNodes cs).length=(cs.map hardWeight).prod := by
    intro cs hc
    obtain ⟨x,cfg,hx,hm,hq,hw,he⟩:=walls cs hc
    exact system_hardWeight (fun c hc=>hx.hard_endpoints hw he hc)
  have hb : ∀ cs∈S,∃ c∈cs,hardWeight c≤badHardWeight k c := by
    intro cs hc
    obtain ⟨x,cfg,hx,hm,hq,hw,he⟩:=walls cs hc
    obtain ⟨c,hc,hv⟩:=hx.nonempty_row hm hq
    exact ⟨c,hc,hardWeight_le_bad hk hj c (hx.hard_endpoints hw he hc) hv⟩
  calc
    _ ≤ ∑ cs∈S,kappa^(systemNodes cs).length := hB
    _ = ∑ cs∈S,(cs.map hardWeight).prod := Finset.sum_congr rfl (fun cs hc=>hp cs hc)
    _ ≤ ListBound.markTotal (1+∑ c : BoundaryChord W H,hardWeight c)
        (∑ c : BoundaryChord W H,badHardWeight k c) (2*(W+1)) :=
      ListBound.finite_marked_system_bound hardWeight (badHardWeight k) hardWeight_nonnegative (badHardWeight_nonnegative k) S _ hn hb
    _ ≤ _ := by
      apply markTotal_mono
      · have hh := Finset.sum_nonneg (fun c (_ : c∈(Finset.univ : Finset (BoundaryChord W H)))=>hardWeight_nonnegative c)
        linarith
      · exact Finset.sum_nonneg (fun c hc=>badHardWeight_nonnegative k c)
      · rw [sum_hardWeight]
        exact add_le_add (le_refl 1) (singleSystemMass_le W H)
      · exact sum_badHardWeight_le W H k
end AnyRow
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology
namespace AnyRow
noncomputable def rowLimitError (W k : ℕ) : ℝ :=
  ListBound.markTotal (1+2*archPoolMass W) (2*archTailMass W k) (2*(W+1))
lemma rowErrorBound_limit (W k : ℕ) : Tendsto (fun H=>rowErrorBound W H k) atTop (𝓝 (rowLimitError W k)) := by
  apply markTotal_tendsto (tendsto_const_nhds.add (poolMass_limit W))
  simp_rw [badPoolMass_eq]
  simpa using tendsto_const_nhds.add ((bridgePoolMass_limit W).const_mul 2)
lemma rowLimitError_limit (W : ℕ) : Tendsto (rowLimitError W) atTop (𝓝 0) :=
  ListBound.markTotal_limit tendsto_const_nhds (by simpa using (archTailMass_limit W).const_mul 2) _

lemma cauchy_of_cut_approximation (u v : ℕ→ℂ) (E : ℕ→ℕ→ℝ) (e : ℕ→ℝ)
    (hE : ∀ k,Tendsto (E k) atTop (𝓝 (e k))) (he : Tendsto e atTop (𝓝 0))
    (hB : ∀ k,∀ᶠ H in atTop,‖u H-v k‖≤E k H) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hex : ∀ᶠ k in atTop,e k<ε/4 := he.eventually (gt_mem_nhds (by linarith))
  obtain ⟨k,hk⟩:=hex.exists
  have hsmall : ∀ᶠ H in atTop,E k H<ε/2 := (hE k).eventually (gt_mem_nhds (by linarith))
  have hdist : ∀ᶠ H in atTop,‖u H-v k‖<ε/2 := by
    filter_upwards [hB k,hsmall] with H h1 h2
    exact h1.trans_lt h2
  obtain ⟨N,hN⟩:=eventually_atTop.mp hdist
  refine ⟨N,fun m hm n hn=>?_⟩
  have h1:=hN m hm
  have h2:=hN n hn
  have hh:=dist_triangle (u m) (v k) (u n)
  rw [dist_comm (v k) (u n)] at hh
  simp only [dist_eq_norm] at hh ⊢
  linarith
end AnyRow
end CriticalHoneycomb.Transfer.RasterGrid

end

end OAI
