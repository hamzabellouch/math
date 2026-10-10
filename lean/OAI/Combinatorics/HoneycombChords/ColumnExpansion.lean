import OAI.Combinatorics.HoneycombChords.ChordMass

namespace OAI

/-! Column expansion for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.ListBound
open Filter Topology

noncomputable def marked {α : Type*} (w v : α→ℝ) : {n : ℕ}→Pad α n→ℝ
  | 0,_=>0
  | _+1,(a,p)=>a.elim 0 v*weight w p+a.elim 1 w*marked w v p
lemma marked_nonnegative {α : Type*} {w v : α→ℝ}
    (hw : ∀ a,0≤ w a) (hv : ∀ a,0≤ v a) {n : ℕ} (p : Pad α n) : 0≤ marked w v p := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    rcases p with ⟨a,p⟩
    apply add_nonneg
    · exact mul_nonneg (by cases a <;> simp_all) (weight_nonnegative hw p)
    · exact mul_nonneg (by cases a <;> simp_all) (ih p)
lemma weight_le_marked_encode {α : Type*} {w v : α→ℝ}
    (hw : ∀ a,0≤ w a) (hv : ∀ a,0≤ v a) (n : ℕ) (as : List α)
    (hl : as.length≤ n) (hb : ∃ a∈as,w a≤ v a) :
    weight w (encode n as)≤ marked w v (encode n as) := by
  induction n generalizing as with
  | zero =>
    have he : as=[]:=List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
    subst as
    simp at hb
  | succ n ih =>
    cases as with
    | nil => simp at hb
    | cons a as =>
      obtain ⟨b,hb,hbv⟩:=hb
      rcases List.mem_cons.mp hb with hba|hb
      · subst b
        change w a*weight w (encode n as)≤ v a*weight w (encode n as)+w a*marked w v (encode n as)
        exact (mul_le_mul_of_nonneg_right hbv (weight_nonnegative hw _)).trans
          (le_add_of_nonneg_right (mul_nonneg (hw a) (marked_nonnegative hw hv _)))
      · change w a*weight w (encode n as)≤ v a*weight w (encode n as)+w a*marked w v (encode n as)
        exact (mul_le_mul_of_nonneg_left (ih as (Nat.le_of_succ_le_succ hl) ⟨b,hb,hbv⟩) (hw a)).trans
          (le_add_of_nonneg_left (mul_nonneg (hv a) (weight_nonnegative hw _)))

noncomputable def markTotal (U V : ℝ) : ℕ→ℝ
  | 0=>0
  | n+1=>V*U^n+U*markTotal U V n
lemma sum_marked {α : Type*} [Fintype α] (w v : α→ℝ) (n : ℕ) :
    (∑ p : Pad α n,marked w v p)=markTotal (1+∑ a,w a) (∑ a,v a) n := by
  induction n with
  | zero => change (∑ _ : PUnit,(0:ℝ))=0; simp
  | succ n ih =>
    change (∑ p : Option α × Pad α n,(p.1.elim 0 v*weight w p.2+p.1.elim 1 w*marked w v p.2))=_
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    rw [sum_weight,ih,←Finset.sum_mul,←Finset.sum_mul,Fintype.sum_option,Fintype.sum_option]
    simp only [Option.elim_none,Option.elim_some,zero_add,markTotal]
lemma finite_marked_system_bound {α : Type*} [Fintype α] (w v : α→ℝ)
    (hw : ∀ a,0≤ w a) (hv : ∀ a,0≤ v a) (S : Finset (List α)) (n : ℕ)
    (hlen : ∀ as∈S,as.length≤ n) (hbad : ∀ as∈S,∃ a∈as,w a≤ v a) :
    (∑ as∈S,(as.map w).prod)≤ markTotal (1+∑ a,w a) (∑ a,v a) n := by
  classical
  calc
    _ ≤ ∑ as∈S,marked w v (encode n as) := by
      apply Finset.sum_le_sum
      intro as ha
      rw [←weight_encode w n as (hlen as ha)]
      exact weight_le_marked_encode hw hv n as (hlen as ha) (hbad as ha)
    _ = ∑ p∈S.image (encode n),marked w v p := by
      symm
      apply Finset.sum_image
      intro as has bs hbs he
      have hh:=congrArg decode he
      simpa only [decode_encode n as (hlen as has),decode_encode n bs (hlen bs hbs)] using hh
    _ ≤ ∑ p : Pad α n,marked w v p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p hp hn
      exact marked_nonnegative hw hv p
    _ = _ := sum_marked w v n
lemma markTotal_limit {U V : ℕ→ℝ} {u : ℝ}
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun H=>markTotal (U H) (V H) n) atTop (𝓝 0) := by
  induction n with
  | zero => exact tendsto_const_nhds
  | succ n ih =>
    simpa only [markTotal,zero_mul,mul_zero,add_zero] using (hV.mul (hU.pow n)).add (hU.mul ih)
end CriticalHoneycomb.Transfer.ListBound

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology
lemma SelectedSystem.node_of_incident {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs) {v : Center}
    (hv : v∈domain (W+1) (H+1)) {k : Fin 3}
    (hs : assignmentSpins x (incidentWire v k)≠1) : v∈systemNodes cs := by
  obtain ⟨c,hc,he⟩:=(h.edge_union _).mp hs
  have hm : v∈Set.range c.path.center := by
    by_contra hm
    apply c.path.incident_off v _ _ hm k he
    · rw [BoundaryChord.path,ofChord_first]
      exact fun hh=>c.source.outside_not_mem (hh ▸ hv)
    · rw [BoundaryChord.path,ofChord_last]
      exact fun hh=>c.target.outside_not_mem (hh ▸ hv)
  exact List.mem_flatMap.mpr ⟨c,hc,(c.nodes_mem v).mpr hm⟩
lemma Matches.nonempty_selected {W H : ℕ} {cfg : Cell W H→Shape}
    {x : Assignment W H} (hm : Matches cfg x.1 x.2) {t : Cell W H}
    (hn : cfg t≠.empty) : ∃ b k,assignmentSpins x (incidentWire (cellCenter t b) k)≠1 := by
  obtain ⟨hw,hn',hs,he,hm'⟩:=hm t
  have west (hh : (cfg t).selection.west=true) :
      assignmentSpins x (incidentWire (cellCenter t true) 2)≠1 := by
    rw [assignmentSpins,(up_wires t).2.2,spins_wire]
    simpa only [hh,spinOccupied,decide_eq_true_eq,Sum.elim_inl] using hw
  have south (hh : (cfg t).selection.south=true) :
      assignmentSpins x (incidentWire (cellCenter t true) 1)≠1 := by
    rw [assignmentSpins,(up_wires t).2.1,spins_wire]
    simpa only [hh,spinOccupied,decide_eq_true_eq,Sum.elim_inl] using hs
  have north (hh : (cfg t).selection.north=true) :
      assignmentSpins x (incidentWire (cellCenter t false) 1)≠1 := by
    rw [assignmentSpins,(down_wires t).2.1,spins_wire]
    simpa only [hh,spinOccupied,decide_eq_true_eq,Sum.elim_inl] using hn'
  cases hq : cfg t with
  | empty => exact (hn hq).elim
  | westSouth => exact ⟨true,2,west (by rw [hq];rfl)⟩
  | northEast => exact ⟨false,1,north (by rw [hq];rfl)⟩
  | both => exact ⟨true,2,west (by rw [hq];rfl)⟩
  | westNorth => exact ⟨true,2,west (by rw [hq];rfl)⟩
  | southEast => exact ⟨true,1,south (by rw [hq];rfl)⟩
  | westEast => exact ⟨true,2,west (by rw [hq];rfl)⟩
  | northSouth => exact ⟨true,1,south (by rw [hq];rfl)⟩
lemma SelectedSystem.nonempty_row {W H : ℕ} {x : Assignment (W+1) (H+1)}
    {cs : List (BoundaryChord W H)} (h : SelectedSystem x cs)
    {cfg : Cell (W+1) (H+1)→Shape} (hm : Matches cfg x.1 x.2)
    {j : Fin (H+1)} (hn : ∃ i,cfg (i,j)≠.empty) :
    ∃ c∈cs,∃ v∈c.chord.val,v.2.1=(j.val:ℤ) := by
  obtain ⟨i,hi⟩:=hn
  obtain ⟨b,k,hk⟩:=hm.nonempty_selected hi
  obtain ⟨c,hc,hv⟩:=List.mem_flatMap.mp (h.node_of_incident (cellCenter_mem (i,j) b) hk)
  exact ⟨c,hc,cellCenter (i,j) b,hv,rfl⟩
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations
noncomputable def restrictedPartition {W H : ℕ} (x₀ : Assignment W H)
    (Q : (Cell W H→Shape)→Prop) : ℂ := by
  classical
  exact ∑ cfg : Cell W H→Shape,if Q cfg then ∑ x,relativeTerm cfg x₀ x else 0

theorem actual_restricted_component_bound {W H : ℕ} (x₀ : Assignment (W+1) (H+1))
    (Q : (Cell (W+1) (H+1)→Shape)→Prop) :
    ∃ S : Finset (List (BoundaryChord W H)),
      (∀ cs∈S,∃ x cfg,SameBoundary x x₀ ∧ Matches cfg x.1 x.2 ∧ Q cfg ∧ SelectedSystem x cs) ∧
      ‖restrictedPartition x₀ Q‖
        ≤∑ cs∈S,kappa^(systemNodes cs).length := by
  classical
  let F := fun cfg : Cell (W+1) (H+1)→Shape=>∑ x,relativeTerm cfg x₀ x
  let A := {cfg : Cell (W+1) (H+1)→Shape // Q cfg ∧ F cfg≠0}
  have hd : ∀ a : A,∃ x cs,SameBoundary x x₀ ∧ Matches a.val x.1 x.2 ∧
      SelectedSystem x cs ∧ F a.val=systemAmplitude x cs := fun a=>
    active_shape_decomposition x₀ a.val a.property.2
  choose x cs hb hm hs hc using hd
  have hi : Function.Injective cs := by
    intro a b he
    apply Subtype.ext
    exact SelectedSystem.shape_unique (hs a) (he ▸ hs b) (hm a) (hm b)
  let S := Finset.univ.image cs
  refine ⟨S,?_,?_⟩
  · intro z hz
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hz
    exact ⟨x a,a.val,hb a,hm a,a.property.1,hs a⟩
  · have hsum : (∑ cfg,if Q cfg then F cfg else 0)=∑ a : A,F a.val := by
      rw [←sum_subtype_indicator (fun cfg=>Q cfg ∧ F cfg≠0) F]
      apply Finset.sum_congr rfl
      intro cfg hcfg
      by_cases hh : F cfg=0 <;> by_cases hq : Q cfg <;> simp [hh,hq]
    change ‖∑ cfg,if Q cfg then F cfg else 0‖≤_
    rw [hsum]
    calc
      _ ≤ ∑ a : A,‖F a.val‖ := norm_sum_le _ _
      _ = ∑ a : A,kappa^(systemNodes (cs a)).length := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hc a,(hs a).amplitude_norm]
      _ = _ := by
        change (∑ a : A,kappa^(systemNodes (cs a)).length)=
          ∑ z∈Finset.univ.image cs,kappa^(systemNodes z).length
        symm
        exact Finset.sum_image (f:=fun z : List (BoundaryChord W H)=>kappa^(systemNodes z).length)
          (s:=(Finset.univ : Finset A)) hi.injOn
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open Filter Topology
noncomputable def badHardWeight {W H : ℕ} (c : BoundaryChord W H) : ℝ := by
  classical
  exact if hp : EndPort c.source ∧ EndPort c.target then
    badPoolWeight (H/2) (HardChord.encode ⟨c,hp⟩) else 0
lemma badHardWeight_nonnegative {W H : ℕ} (c : BoundaryChord W H) : 0≤badHardWeight c := by
  unfold badHardWeight
  split_ifs
  · exact badPoolWeight_nonnegative _
  · exact le_refl _
lemma sum_badHardWeight_le (W H : ℕ) :
    (∑ c : BoundaryChord W H,badHardWeight c)≤badPoolMass W H (H/2) := by
  classical
  have he : (∑ c : BoundaryChord W H,badHardWeight c)=
      ∑ c : HardChord W H,badPoolWeight (H/2) c.encode := by
    have hs : ∀ c : HardChord W H,badHardWeight c.val=badPoolWeight (H/2) c.encode := by
      rintro ⟨c,hp⟩
      simp only [badHardWeight,dite_eq_left hp]
    calc
      _ = ∑ c : BoundaryChord W H,if EndPort c.source ∧ EndPort c.target then badHardWeight c else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hp : EndPort c.source ∧ EndPort c.target <;> simp [badHardWeight,hp]
      _ = ∑ c : HardChord W H,badHardWeight c.val :=
        by
          rw [←Finset.sum_filter]
          exact Finset.sum_subtype _ (by simp) _
      _ = _ := Finset.sum_congr rfl (fun c hc=>hs c)
  rw [he]
  calc
    _ = ∑ a∈Finset.univ.image (HardChord.encode (W:=W) (H:=H)),badPoolWeight (H/2) a :=
      (Finset.sum_image (HardChord.encode_injective W H).injOn).symm
    _ ≤ _ := (badPool_summable W H (H/2)).sum_le_tsum _ (fun a ha=>badPoolWeight_nonnegative a)
lemma hardWeight_le_bad {W H : ℕ} (c : BoundaryChord W H)
    (hp : EndPort c.source ∧ EndPort c.target)
    (hm : ∃ v∈c.chord.val,v.2.1=(H/2:ℕ)) : hardWeight c≤badHardWeight c := by
  classical
  let a : HardChord W H:=⟨c,hp⟩
  have hh:=a.midrow_weight hm
  unfold hardWeight badHardWeight
  rw [ite_eq_left hp,dite_eq_left hp]
  change kappa^c.chord.val.length≤badPoolWeight (H/2) a.encode
  rw [hh,poolWeight,a.encode_length]

lemma markTotal_nonnegative {U V : ℝ} (hU : 0≤U) (hV : 0≤V) (n : ℕ) :
    0≤ListBound.markTotal U V n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact add_nonneg (mul_nonneg hV (pow_nonneg hU _)) (mul_nonneg hU ih)
lemma markTotal_mono {U U' V V' : ℝ} (hnU : 0≤U) (hnV : 0≤V)
    (hU : U≤U') (hV : V≤V') (n : ℕ) :
    ListBound.markTotal U V n≤ListBound.markTotal U' V' n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    exact add_le_add (mul_le_mul hV (pow_le_pow_left₀ hnU hU n) (pow_nonneg hnU _) (hnV.trans hV))
      (mul_le_mul hU ih (markTotal_nonnegative hnU hnV n) (hnU.trans hU))

noncomputable def middleErrorBound (W H : ℕ) : ℝ :=
  ListBound.markTotal (1+poolMass W H) (badPoolMass W H (H/2)) (2*(W+1))
lemma middleErrorBound_limit (W : ℕ) : Tendsto (middleErrorBound W) atTop (𝓝 0) :=
  ListBound.markTotal_limit (tendsto_const_nhds.add (poolMass_limit W)) (badPoolMass_limit W) _

theorem actual_middle_row_bound {W H : ℕ} (x₀ : Assignment (W+1) (H+1))
    (hw : ∀ j,assignmentSpins x₀ (westPort W H j).wire=1)
    (he : ∀ j,assignmentSpins x₀ (eastPort W H j).wire=1) :
    ‖restrictedPartition x₀ (fun cfg=>∃ i,cfg (i,⟨H/2,by omega⟩)≠.empty)‖≤ middleErrorBound W H := by
  classical
  let Q := fun cfg : Cell (W+1) (H+1)→Shape=>∃ i,cfg (i,⟨H/2,by omega⟩)≠.empty
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
  have hb : ∀ cs∈S,∃ c∈cs,hardWeight c≤badHardWeight c := by
    intro cs hc
    obtain ⟨x,cfg,hx,hm,hq,hw,he⟩:=walls cs hc
    obtain ⟨c,hc,hv⟩:=hx.nonempty_row hm hq
    exact ⟨c,hc,hardWeight_le_bad c (hx.hard_endpoints hw he hc) hv⟩
  calc
    _ ≤ ∑ cs∈S,kappa^(systemNodes cs).length := hB
    _ = ∑ cs∈S,(cs.map hardWeight).prod := Finset.sum_congr rfl (fun cs hc=>hp cs hc)
    _ ≤ ListBound.markTotal (1+∑ c : BoundaryChord W H,hardWeight c)
        (∑ c : BoundaryChord W H,badHardWeight c) (2*(W+1)) :=
      ListBound.finite_marked_system_bound hardWeight badHardWeight hardWeight_nonnegative badHardWeight_nonnegative S _ hn hb
    _ ≤ _ := by
      apply markTotal_mono
      · have hh := Finset.sum_nonneg (fun c (_ : c∈(Finset.univ : Finset (BoundaryChord W H)))=>hardWeight_nonnegative c)
        linarith
      · exact Finset.sum_nonneg (fun c hc=>badHardWeight_nonnegative c)
      · rw [sum_hardWeight]
        exact add_le_add (le_refl 1) (singleSystemMass_le W H)
      · exact sum_badHardWeight_le W H
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open scoped Matrix
lemma sourceR_PT (a h v c d : ℂ) (w n s e : Fin 3) :
    Planar.sourceR a h v c d (n,w) (s,e)=Planar.sourceR a h v c d (e,s) (w,n) := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;> rfl

def transposeWire (W H : ℕ) : GridWire W H ≃ GridWire H W where
  toFun := Sum.elim (fun p=>.inr (p.2,p.1)) (fun p=>.inl (p.2,p.1))
  invFun := Sum.elim (fun p=>.inr (p.2,p.1)) (fun p=>.inl (p.2,p.1))
  left_inv := by rintro (⟨i,j⟩|⟨i,j⟩) <;> rfl
  right_inv := by rintro (⟨i,j⟩|⟨i,j⟩) <;> rfl
def transposeSpins {W H : ℕ} (σ : GridWire W H→Fin 3) : GridWire H W→Fin 3 :=
  σ ∘ (transposeWire W H).symm
lemma physical_transpose {W H : ℕ} (σ : GridWire W H→Fin 3) :
    (network W H).physical σ=(network H W).physical (transposeSpins σ) := by
  unfold TileNetwork.physical
  rw [Fintype.prod_prod_type]
  rw [Fintype.prod_prod_type,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  exact sourceR_PT _ _ _ _ _ _ _ _ _
noncomputable def allGridPartition (W H : ℕ) (west east : Column H)
    (south north : Column W) : ℂ := by
  classical
  exact ∑ σ : GridWire W H→Fin 3,if
    (∀ j,σ (.inl (0,j))=west j) ∧ (∀ j,σ (.inl (Fin.last W,j))=east j) ∧
    (∀ i,σ (.inr (i,0))=south i) ∧ (∀ i,σ (.inr (i,Fin.last H))=north i)
    then (network W H).physical σ else 0
lemma prescribed_eq_allGrid (W H : ℕ) (west east : Column H) (south north : Column W) :
    prescribedPartition W H west east south north=allGridPartition W H west east south north := by
  classical
  rw [prescribedPartition_eq_grid_sum]
  unfold allGridPartition
  trans ∑ σ : GridWire W H→Fin 3,if HasWestNorth west north σ then
    (if (∀ j,σ (.inl (Fin.last W,j))=east j) ∧ (∀ i,σ (.inr (i,0))=south i)
    then (network W H).physical σ else 0) else 0
  · convert (sum_subtype_indicator (HasWestNorth west north) (fun σ=>
      if (∀ j,σ (.inl (Fin.last W,j))=east j) ∧ (∀ i,σ (.inr (i,0))=south i)
      then (network W H).physical σ else 0)).symm using 1
    congr 1
    ext x
    simp
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [HasWestNorth,ite_and]
  split_ifs <;> simp_all
lemma allGrid_transpose (W H : ℕ) (west east : Column H) (south north : Column W) :
    allGridPartition W H west east south north=allGridPartition H W south north west east := by
  classical
  unfold allGridPartition
  let e := Equiv.arrowCongr (transposeWire W H) (Equiv.refl (Fin 3))
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro σ hσ
  have he : e σ=transposeSpins σ := rfl
  rw [he]
  have hb : ((∀ j,σ (.inl (0,j))=west j) ∧ (∀ j,σ (.inl (Fin.last W,j))=east j) ∧
      (∀ i,σ (.inr (i,0))=south i) ∧ (∀ i,σ (.inr (i,Fin.last H))=north i)) ↔
      ((∀ j,transposeSpins σ (.inl (0,j))=south j) ∧
      (∀ j,transposeSpins σ (.inl (Fin.last H,j))=north j) ∧
      (∀ i,transposeSpins σ (.inr (i,0))=west i) ∧
      (∀ i,transposeSpins σ (.inr (i,Fin.last W))=east i)) := by
    dsimp [transposeSpins,transposeWire]
    tauto
  simp only [←hb,physical_transpose σ]
lemma prescribed_transpose (W H : ℕ) (west east : Column H) (south north : Column W) :
    prescribedPartition W H west east south north=prescribedPartition H W south north west east := by
  rw [prescribed_eq_allGrid,allGrid_transpose,←prescribed_eq_allGrid]
noncomputable def rowTransfer (W : ℕ) : Matrix (Column W) (Column W) ℂ := columnKernel W 1 1
lemma prescribed_hard_transfer (W H : ℕ) (south north : Column W) :
    prescribedPartition W H (fun _=>1) (fun _=>1) south north=(rowTransfer W^H) south north := by
  rw [prescribed_transpose,prescribedPartition_eq_transfer]
  simp only [rowTransfer,List.ofFn_const,List.prod_replicate]
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles CenterPartition ChordOrientations FiniteConfigurations FiniteContinuation
open scoped Matrix

def transposeShape : Shape→Shape
  | .westNorth=>.southEast
  | .southEast=>.westNorth
  | .westEast=>.northSouth
  | .northSouth=>.westEast
  | q=>q
lemma transposeShape_involutive : Function.Involutive transposeShape := by intro q;cases q<;>rfl
lemma transposeShape_visits (q : Shape) : (transposeShape q).visits=q.visits := by cases q<;>rfl
lemma transposeShape_empty (q : Shape) : transposeShape q=.empty ↔ q=.empty := by cases q<;>simp [transposeShape]
lemma occupied_symm (x y : Fin 3) : Planar.occupied x y=Planar.occupied y x := by
  have h : (x=y ∧ x≠1) ↔ (y=x ∧ y≠1) := by
    constructor <;> rintro ⟨rfl,h⟩ <;> exact ⟨rfl,h⟩
  simp only [Planar.occupied,h]
lemma vacant_symm (x y : Fin 3) : Planar.vacant x y=Planar.vacant y x := by
  simp [Planar.vacant,and_comm]
lemma shapeTensor_PT (q : Shape) (w n s e : Fin 3) :
    shapeTensor q w n s e=shapeTensor (transposeShape q) s e w n := by
  cases q
  all_goals simp only [shapeTensor,transposeShape]
  case empty => rw [vacant_symm w s,vacant_symm n e]
  case westSouth => rw [occupied_symm w s,vacant_symm n e]
  case northEast => rw [vacant_symm w s,occupied_symm n e]
  case both => rw [occupied_symm w s,occupied_symm n e]
  case westNorth => ring
  case southEast => ring
  case westEast => rw [occupied_symm w e]; ring
  case northSouth => rw [occupied_symm n s]; ring

def transposeConfiguration {W H : ℕ} (cfg : Cell W H→Shape) : Cell H W→Shape :=
  fun t=>transposeShape (cfg (t.2,t.1))
lemma orientation_transpose {W H : ℕ} (cfg : Cell W H→Shape) (σ : GridWire W H→Fin 3) :
    (network W H).orientation cfg σ=
      (network H W).orientation (transposeConfiguration cfg) (transposeSpins σ) := by
  unfold TileNetwork.orientation
  rw [Fintype.prod_prod_type,Fintype.prod_prod_type,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  exact shapeTensor_PT _ _ _ _ _

noncomputable def allChosenGrid {W H : ℕ} (cfg : Cell W H→Shape) (west east : Column H)
    (south north : Column W) : ℂ := by
  classical
  exact ∑ σ : GridWire W H→Fin 3,if
    (∀ j,σ (.inl (0,j))=west j) ∧ (∀ j,σ (.inl (Fin.last W,j))=east j) ∧
    (∀ i,σ (.inr (i,0))=south i) ∧ (∀ i,σ (.inr (i,Fin.last H))=north i)
    then (network W H).orientation cfg σ else 0
lemma chosen_eq_allGrid {W H : ℕ} (cfg : Cell W H→Shape) (west east : Column H) (south north : Column W) :
    chosenPartition cfg west east south north=allChosenGrid cfg west east south north := by
  classical
  rw [chosenPartition_eq_grid_sum]
  unfold allChosenGrid
  trans ∑ σ : GridWire W H→Fin 3,if HasWestNorth west north σ then
    (if (∀ j,σ (.inl (Fin.last W,j))=east j) ∧ (∀ i,σ (.inr (i,0))=south i)
    then (network W H).orientation cfg σ else 0) else 0
  · convert (sum_subtype_indicator (HasWestNorth west north) (fun σ=>
      if (∀ j,σ (.inl (Fin.last W,j))=east j) ∧ (∀ i,σ (.inr (i,0))=south i)
      then (network W H).orientation cfg σ else 0)).symm using 1
    congr 1
    ext x
    simp
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [HasWestNorth,ite_and]
  split_ifs <;> simp_all
lemma chosen_transpose {W H : ℕ} (cfg : Cell W H→Shape) (west east : Column H) (south north : Column W) :
    chosenPartition cfg west east south north=
      chosenPartition (transposeConfiguration cfg) south north west east := by
  classical
  rw [chosen_eq_allGrid,chosen_eq_allGrid]
  unfold allChosenGrid
  let e := Equiv.arrowCongr (transposeWire W H) (Equiv.refl (Fin 3))
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro σ hσ
  have he : e σ=transposeSpins σ := rfl
  rw [he]
  have hb : ((∀ j,σ (.inl (0,j))=west j) ∧ (∀ j,σ (.inl (Fin.last W,j))=east j) ∧
      (∀ i,σ (.inr (i,0))=south i) ∧ (∀ i,σ (.inr (i,Fin.last H))=north i)) ↔
      ((∀ j,transposeSpins σ (.inl (0,j))=south j) ∧
      (∀ j,transposeSpins σ (.inl (Fin.last H,j))=north j) ∧
      (∀ i,transposeSpins σ (.inr (i,0))=west i) ∧
      (∀ i,transposeSpins σ (.inr (i,Fin.last W))=east i)) := by
    dsimp [transposeSpins,transposeWire]
    tauto
  simp only [←hb,orientation_transpose cfg σ]
lemma sum_visits_transpose {W H : ℕ} (cfg : Cell W H→Shape) :
    (∑ t,(transposeConfiguration cfg t).visits)=∑ t,(cfg t).visits := by
  simp only [transposeConfiguration,transposeShape_visits]
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.sum_comm]
lemma weighted_chosen_transpose {W H : ℕ} (cfg : Cell W H→Shape)
    (west east : Column H) (south north : Column W) :
    (kappa:ℂ)^(∑ t,(cfg t).visits)*chosenPartition cfg west east south north=
    (kappa:ℂ)^(∑ t,(transposeConfiguration cfg t).visits)*
      chosenPartition (transposeConfiguration cfg) south north west east := by
  rw [sum_visits_transpose,chosen_transpose]
end CriticalHoneycomb.Transfer.RasterGrid

end

end OAI
