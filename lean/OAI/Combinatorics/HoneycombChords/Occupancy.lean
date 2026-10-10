import OAI.Combinatorics.HoneycombChords.ColumnTransfer

namespace OAI

/-!
# Resolved occupancy contractions

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

/-- Local occupancy projection. Unlike an entire frontier mask this fixes
only the two wires touched by one actual lozenge. -/
noncomputable def pairMask : ℕ → Bool → Bool → DiluteState → DiluteState
  | 0,a,b,f,x::y::xs => if x.isSome=a ∧ y.isSome=b then f (x::y::xs) else 0
  | 0,_,_,_,_ => 0
  | i+1,a,b,f,x::xs => pairMask i a b (fun ys => f (x::ys)) xs
  | _+1,_,_,_,[] => 0

lemma pairMask_zero (i : ℕ) (a b : Bool) :
    pairMask i a b (fun _=>0) = fun _=>0 := by
  induction i with
  | zero => funext xs; cases xs with
    | nil => rfl
    | cons x xs => cases xs <;> simp [pairMask]
  | succ i ih =>
    funext xs; cases xs with
    | nil => rfl
    | cons x xs => exact congrFun ih xs

lemma pairMask_add (i : ℕ) (a b : Bool) (f g : DiluteState) :
    pairMask i a b (fun xs => f xs+g xs) = fun xs => pairMask i a b f xs+pairMask i a b g xs := by
  induction i generalizing f g with
  | zero => funext xs; cases xs with
    | nil => simp [pairMask]
    | cons x xs => cases xs <;> simp [pairMask]; split_ifs <;> simp
  | succ i ih =>
    funext xs; cases xs with
    | nil => simp [pairMask]
    | cons x xs => exact congrFun (ih _ _) xs

lemma pairMask_smul (i : ℕ) (a b : Bool) (z : ℂ) (f : DiluteState) :
    pairMask i a b (fun xs => z*f xs) = fun xs => z*pairMask i a b f xs := by
  induction i generalizing f with
  | zero => funext xs; cases xs with
    | nil => simp [pairMask]
    | cons x xs => cases xs <;> simp [pairMask] 
  | succ i ih =>
    funext xs; cases xs with
    | nil => simp [pairMask]
    | cons x xs => exact congrFun (ih _) xs

lemma pairMask_embed (pre post : List Bool) (a b c d : Bool) (f : State) :
    pairMask pre.length a b (embed (pre++c::d::post) f) =
      if c=a ∧ d=b then embed (pre++c::d::post) f else fun _=>0 := by
  induction pre generalizing f with
  | nil =>
    funext xs
    cases xs with
    | nil => simp [pairMask,embed,occupancy,ite_apply]
    | cons x xs => cases xs with
      | nil => simp [pairMask,embed,occupancy,ite_apply]
      | cons y xs =>
        cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;>
          simp [pairMask,embed,occupancy]
  | cons p pre ih =>
    funext xs
    cases xs with
    | nil => simp [pairMask,embed,occupancy,ite_apply]
    | cons x xs =>
      cases p <;> cases x <;>
        simp only [List.length_cons,List.cons_append,pairMask,embed_false,embed_true,
          embed_false_some,embed_true_none,ite_apply,pairMask_zero]
      · simpa only [ite_apply] using congrFun (ih f) xs
      · simp
      · simp
      · rename_i z
        simpa only [ite_apply] using congrFun (ih (fun ys=>f (z::ys))) xs

lemma pairMask_resolved {b n i : ℕ} {root : State} {f : DiluteState}
    (hi : i+1<n) (a c : Bool) (hf : Resolved b n root f) :
    Resolved b n root (pairMask i a c f) := by
  cases hf with
  | zero => rw [pairMask_zero]; exact .zero
  | basis o k w hl hc =>
    obtain ⟨pre,x,y,post,rfl,hpre⟩ := two_at o i (by omega)
    subst i
    rw [pairMask_embed]
    split_ifs
    · exact .basis _ k w hl hc
    · exact .zero

lemma pairMask_two_choices (pre post : List Bool) (a b c d x y : Bool)
    (f g : State) (h : (a,b)≠(c,d)) :
    pairMask pre.length x y (fun xs => embed (pre++a::b::post) f xs +
        embed (pre++c::d::post) g xs) = (fun _=>0) ∨
    pairMask pre.length x y (fun xs => embed (pre++a::b::post) f xs +
        embed (pre++c::d::post) g xs) = embed (pre++a::b::post) f ∨
    pairMask pre.length x y (fun xs => embed (pre++a::b::post) f xs +
        embed (pre++c::d::post) g xs) = embed (pre++c::d::post) g := by
  rw [pairMask_add,pairMask_embed,pairMask_embed]
  by_cases hab : a=x ∧ b=y
  · rcases hab with ⟨rfl,rfl⟩
    have hcd : ¬(c=a ∧ d=b) := by intro hh; exact h (Prod.ext hh.1.symm hh.2.symm)
    simp [hcd]
  · by_cases hcd : c=x ∧ d=y
    · simp [hab,hcd]
    · simp [hab,hcd]

lemma pairMask_two_resolved {b n : ℕ} {root : State}
    (pre post : List Bool) (a c d e x y : Bool) (f g : State)
    (h : (a,c)≠(d,e))
    (hf : Resolved b n root (embed (pre++a::c::post) f))
    (hg : Resolved b n root (embed (pre++d::e::post) g)) :
    Resolved b n root (pairMask pre.length x y
      (fun xs => embed (pre++a::c::post) f xs + embed (pre++d::e::post) g xs)) := by
  rcases pairMask_two_choices pre post a c d e x y f g h with hh|hh|hh <;> rw [hh]
  · exact .zero
  · exact hf
  · exact hg

/-- A specified local output pair selects at most one of the source's two
allowed physical connectivities; no superposition of planar words remains. -/
lemma pair_resolved_step {b n i : ℕ} (hb : b≤1) (hi : i+1<n) (x y : Bool)
    {root : State} {f : DiluteState} (hf : Resolved b n root f) :
    Resolved b n root (pairMask i x y (act resolvedWeights i f)) := by
  cases hf with
  | zero => rw [act_zero,pairMask_zero]; exact .zero
  | basis o k w hl hc =>
    obtain ⟨pre,a,c,post,rfl,hpre⟩ := two_at o i (by omega)
    subst i
    cases a <;> cases c
    · rw [act_empty_at]
      simp only [resolvedWeights,one_mul]
      apply pairMask_two_resolved
      · decide
      · exact .basis _ k w hl hc
      · have hip : pre.count true ≤ b+2*k := by simp [List.count_append] at hc; omega
        exact .basis _ (k+1) (.insert w (pre.count true) hip)
          (by simpa using hl) (by simp_all [List.count_append]; omega)
    · rw [act_right_at]
      simp only [resolvedWeights,one_mul]
      apply pairMask_two_resolved
      · decide
      · exact .basis _ k w hl hc
      · exact .basis _ k w (by simpa using hl) (by simpa [List.count_append,List.count_cons] using hc)
    · rw [act_left_at]
      simp only [resolvedWeights,one_mul]
      apply pairMask_two_resolved
      · decide
      · exact .basis _ k w hl hc
      · exact .basis _ k w (by simpa using hl) (by simpa [List.count_append,List.count_cons] using hc)
    · have hk : 0<k := by simp [List.count_append] at hc; omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      have hip : pre.count true ≤ b+2*k := by simp [List.count_append] at hc ⊢; omega
      rw [act_full_at]
      simp only [resolvedWeights,one_mul,zero_mul,add_zero]
      apply pairMask_two_resolved
      · decide
      · exact .basis _ (k+1) w hl hc
      · exact .basis _ k (.erase w (pre.count true) hip) (by simpa using hl)
          (by simp [List.count_append] at hc ⊢; omega)

/-- Exact chosen physical lozenge connectivity, before restoring κ^visits. -/
noncomputable def shapeAction (q : PhysicalTiles.Shape) (i : ℕ) (f : DiluteState) : DiluteState :=
  pairMask i q.selection.west q.selection.north
    (act resolvedWeights i (pairMask i q.selection.south q.selection.east f))

lemma shapeAction_resolved {b n i : ℕ} (hb : b≤1) (hi : i+1<n)
    (q : PhysicalTiles.Shape) {root : State} {f : DiluteState} (hf : Resolved b n root f) :
    Resolved b n root (shapeAction q i f) := by
  exact pair_resolved_step hb hi _ _ (pairMask_resolved hi _ _ hf)

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

lemma chosen_tile_eq_shape (q : PhysicalTiles.Shape) (w n s e : Spin) :
    (if w.isSome=q.selection.west ∧ n.isSome=q.selection.north ∧
        s.isSome=q.selection.south ∧ e.isSome=q.selection.east then
      tile resolvedWeights w n s e else 0) =
      PhysicalTiles.shapeTensor q (spinIndex w) (spinIndex n) (spinIndex s) (spinIndex e) := by
  have hp : Planar.phase = phase := sourcePhase_eq
  cases q <;> fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp [PhysicalTiles.shapeTensor,PhysicalTiles.Shape.selection,Planar.cup,Planar.occupied,
      Planar.vacant,Planar.empty,spinIndex,tile,resolvedWeights,cup,hp]

/-- A chosen shape operation is the literal source orientation tensor,
not merely an abstraction with the same support. -/
lemma shapeAction_zero (q : PhysicalTiles.Shape) (f : DiluteState) (w n : Spin) (xs : List Spin) :
    shapeAction q 0 f (w::n::xs) =
      ∑ s : Spin, ∑ e : Spin,
        PhysicalTiles.shapeTensor q (spinIndex w) (spinIndex n) (spinIndex s) (spinIndex e) *
          f (s::e::xs) := by
  unfold shapeAction
  simp only [pairMask,act]
  by_cases ho : w.isSome=q.selection.west ∧ n.isSome=q.selection.north
  · rw [ite_eq_left ho]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro e he
    rw [←chosen_tile_eq_shape]
    by_cases hi : s.isSome=q.selection.south ∧ e.isSome=q.selection.east
    · simp [ho.1,ho.2,hi.1,hi.2]
    · simp only [ite_eq_right hi]
      have h : ¬(w.isSome=q.selection.west ∧ n.isSome=q.selection.north ∧
          s.isSome=q.selection.south ∧ e.isSome=q.selection.east) := by tauto
      simp [h]
  · rw [ite_eq_right ho]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.sum_eq_zero
    intro e he
    rw [←chosen_tile_eq_shape]
    have h : ¬(w.isSome=q.selection.west ∧ n.isSome=q.selection.north ∧
        s.isSome=q.selection.south ∧ e.isSome=q.selection.east) := by tauto
    simp [h]

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

noncomputable def addOne (f : DiluteState) : DiluteState
  | none::xs => f xs
  | _ => 0

noncomputable def removeOne (f : DiluteState) : DiluteState := fun xs => f (xs++[none])

lemma addOne_embed (o : List Bool) (f : State) :
    addOne (embed o f) = embed (false::o) f := by
  funext xs
  cases xs with
  | nil => simp [addOne,embed,occupancy]
  | cons x xs => cases x <;> simp [addOne,embed,occupancy,orientations]

lemma removeOne_embed (o : List Bool) (a : Bool) (f : State) :
    removeOne (embed (o++[a]) f) = if a=false then embed o f else fun _ => 0 := by
  funext xs
  have heq : occupancy (xs++[none])=o++[a] ↔ occupancy xs=o ∧ a=false := by
    simp only [occupancy,List.map_append]
    constructor
    · intro h
      have hh := List.append_inj' h (by simp)
      simpa using hh
    · rintro ⟨rfl,rfl⟩; rfl
  simp only [removeOne,embed,heq,orientations,List.filterMap_append]
  cases a <;> simp [embed,orientations]


lemma addOne_resolved {b n : ℕ} {root : State} {f : DiluteState}
    (hf : Resolved b n root f) : Resolved b (n+1) root (addOne f) := by
  cases hf with
  | zero =>
    have h : addOne (fun _=>0) = fun _=>0 := by
      funext xs; cases xs with
      | nil => rfl
      | cons x xs => cases x <;> rfl
    rw [h]; exact .zero
  | basis o k w hl hc =>
    rw [addOne_embed]
    exact .basis _ k w (by simp [hl]) (by simpa using hc)

lemma removeOne_resolved {b n : ℕ} {root : State} {f : DiluteState}
    (hf : Resolved b (n+1) root f) : Resolved b n root (removeOne f) := by
  cases hf with
  | zero => exact .zero
  | basis o k w hl hc =>
    cases o using List.reverseRecOn with
    | nil => simp at hl
    | append_singleton pre a =>
      rw [removeOne_embed]
      cases a
      · simp only [ite_true]
        exact .basis _ k w (by simp at hl; omega) (by simpa using hc)
      · simp only [Bool.true_eq_false,ite_false]
        exact .zero

noncomputable def shapeRow : ℕ → List PhysicalTiles.Shape → DiluteState → DiluteState
  | _,[],f => f
  | i,q::qs,f => shapeRow (i+1) qs (shapeAction q i f)

lemma shapeRow_resolved {b n i : ℕ} (hb : b≤1) (qs : List PhysicalTiles.Shape)
    (hi : i+qs.length<n) {root : State} {f : DiluteState} (hf : Resolved b n root f) :
    Resolved b n root (shapeRow i qs f) := by
  induction qs generalizing i f with
  | nil => exact hf
  | cons q qs ih =>
    exact ih (by simp at hi; omega) (shapeAction_resolved hb (by simp at hi; omega) q hf)

noncomputable def shapeColumn (qs : List PhysicalTiles.Shape) (f : DiluteState) : DiluteState :=
  removeOne (shapeRow 0 qs (addOne f))

lemma shapeColumn_resolved {b n : ℕ} (hb : b≤1) (qs : List PhysicalTiles.Shape)
    (hn : qs.length=n) {root : State} {f : DiluteState} (hf : Resolved b n root f) :
    Resolved b n root (shapeColumn qs f) := by
  exact removeOne_resolved (shapeRow_resolved hb qs (by simp [hn]) (addOne_resolved hf))

/-- A specified lozenge-shape configuration in a literal finite rectangle,
scanned east-to-west with unmarked north/south boundaries. -/
noncomputable def shapeRectangle (cfg : List (List PhysicalTiles.Shape))
    (f : DiluteState) : DiluteState := cfg.foldl (fun f qs=>shapeColumn qs f) f

lemma shapeRectangle_resolved {b n : ℕ} (hb : b≤1) (cfg : List (List PhysicalTiles.Shape))
    (hn : ∀ qs∈cfg, qs.length=n) {root : State} {f : DiluteState} (hf : Resolved b n root f) :
    Resolved b n root (shapeRectangle cfg f) := by
  induction cfg generalizing f with
  | nil => exact hf
  | cons qs cfg ih =>
    exact ih (by aesop) (shapeColumn_resolved hb qs (hn _ (by simp)) hf)

/-- Endpointwise normalized orientation coefficient for a fixed finite
physical configuration. This is 0 or the identity, without assuming
nonnegativity of the complex local tensor entries. -/
theorem shapeRectangle_one_strand {n : ℕ} (cfg : List (List PhysicalTiles.Shape))
    (hn : ∀ qs∈cfg, qs.length=n) (input out : List Bool) (hi : input.length=n)
    (hc : input.count true=1) (hout : out.count true=1) (root : State) :
    (∀ a : Bool, shapeRectangle cfg (embed input root) (arrowState out a)=0) ∨
    (∀ a : Bool, shapeRectangle cfg (embed input root) (arrowState out a)=root [a]) := by
  apply resolved_one_strand (shapeRectangle_resolved (by omega : 1≤1) cfg hn _) out hout
  exact .basis input 0 .start hi (by simpa using hc)

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

lemma pairMask_prefix (pre : List Spin) (i : ℕ) (a b : Bool) (f : DiluteState) (xs : List Spin) :
    pairMask (pre.length+i) a b f (pre++xs) =
      pairMask i a b (fun ys=>f (pre++ys)) xs := by
  induction pre generalizing f with
  | nil => simp
  | cons x pre ih =>
    simpa [pairMask,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (fun ys=>f (x::ys))

lemma shapeAction_prefix (q : PhysicalTiles.Shape) (pre : List Spin) (i : ℕ)
    (f : DiluteState) (xs : List Spin) :
    shapeAction q (pre.length+i) f (pre++xs) =
      shapeAction q i (fun ys=>f (pre++ys)) xs := by
  unfold shapeAction
  rw [pairMask_prefix]
  congr 1
  funext ys
  rw [act_prefix]
  congr 1
  funext zs
  exact pairMask_prefix pre i _ _ f zs

lemma shapeRow_prefix (pre : List Spin) (i : ℕ) (qs : List PhysicalTiles.Shape)
    (f : DiluteState) (xs : List Spin) :
    shapeRow (pre.length+i) qs f (pre++xs) =
      shapeRow i qs (fun ys=>f (pre++ys)) xs := by
  induction qs generalizing i f with
  | nil => rfl
  | cons q qs ih =>
    simp only [shapeRow]
    rw [show pre.length+i+1=pre.length+(i+1) by omega,ih]
    congr 1
    funext ys
    exact shapeAction_prefix q pre i f ys

noncomputable def shapeContraction {n : ℕ} (q : Fin n → PhysicalTiles.Shape) (f : DiluteState)
    (west : Fin n → Spin) (north : Spin) : ℂ :=
  ∑ east : Fin n → Spin, ∑ vertical : Fin n → Spin,
    (∏ j : Fin n, PhysicalTiles.shapeTensor (q j) (spinIndex (west j))
      (spinIndex ((Fin.snoc (α:=fun _=>Spin) vertical north) j.succ))
      (spinIndex (vertical j)) (spinIndex (east j))) *
      f (((Fin.snoc (α:=fun _=>Spin) vertical north) 0) :: List.ofFn east)

lemma shapeContraction_zero (q : Fin 0 → PhysicalTiles.Shape) (f : DiluteState)
    (west : Fin 0 → Spin) (north : Spin) : shapeContraction q f west north=f [north] := by
  simp [shapeContraction,Fin.snoc_zero]

lemma shapeContraction_succ {n : ℕ} (q : Fin (n+1) → PhysicalTiles.Shape) (f : DiluteState)
    (west : Fin (n+1) → Spin) (north : Spin) :
    shapeContraction q f west north =
      shapeContraction (fun j=>q j.succ) (fun ys=>shapeAction (q 0) 0 f (west 0::ys))
        (fun j=>west j.succ) north := by
  unfold shapeContraction
  rw [sum_spin_vectors_succ]
  simp_rw [sum_spin_vectors_succ,Fin.prod_univ_succ,
    ←Fin.cons_snoc_eq_snoc_cons,Fin.cons_succ,Fin.cons_zero,List.ofFn_succ]
  simp only [shapeAction_zero,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro east heast
  conv_lhs =>
    arg 2
    ext firstEast
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro vertical hvertical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro south hsouth
  apply Finset.sum_congr rfl
  intro firstEast hfirstEast
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

/-- Every internal vertical variable of the normalized physical shape
column is summed exactly once by the literal planar raster scan. -/
theorem shapeRow_eq_contraction {n : ℕ} (q : Fin n → PhysicalTiles.Shape) (f : DiluteState)
    (west : Fin n → Spin) (north : Spin) :
    shapeRow 0 (List.ofFn q) f (List.ofFn west++[north]) = shapeContraction q f west north := by
  induction n generalizing f with
  | zero => simp [shapeRow,shapeContraction_zero]
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.cons_append,shapeRow]
    rw [show 0+1=([west 0] : List Spin).length+0 by rfl]
    change shapeRow (([west 0] : List Spin).length+0) (List.ofFn (fun j=>q j.succ))
      (shapeAction (q 0) 0 f) ([west 0]++(List.ofFn (fun j=>west j.succ)++[north])) = _
    rw [shapeRow_prefix,ih,shapeContraction_succ]
    rfl

noncomputable def shapeKernel {n : ℕ} (q : Fin n → PhysicalTiles.Shape)
    (south north : Spin) (west east : Fin n → Spin) : ℂ :=
  ∑ vertical : Fin n → Spin,
    if (Fin.snoc (α:=fun _=>Spin) vertical north) 0=south then
      ∏ j : Fin n, PhysicalTiles.shapeTensor (q j) (spinIndex (west j))
        (spinIndex ((Fin.snoc (α:=fun _=>Spin) vertical north) j.succ))
        (spinIndex (vertical j)) (spinIndex (east j)) else 0

lemma shapeColumn_eq_kernel {n : ℕ} (q : Fin n → PhysicalTiles.Shape) (f : DiluteState)
    (west : Fin n → Spin) :
    shapeColumn (List.ofFn q) f (List.ofFn west) =
      ∑ east : Fin n → Spin, shapeKernel q none none west east * f (List.ofFn east) := by
  classical
  unfold shapeColumn removeOne
  rw [shapeRow_eq_contraction]
  unfold shapeContraction shapeKernel
  apply Finset.sum_congr rfl
  intro east heast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro vertical hvertical
  have h : ∀ (x : Spin) (xs : List Spin), addOne f (x::xs) = if x=none then f xs else 0 := by
    intro x xs; cases x <;> rfl
  rw [h]
  split_ifs <;> simp

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.RasterGrid
open scoped BigOperators Matrix
open PhysicalTiles PlanarNormalization

noncomputable def chosenColumnProduct {H : ℕ} (q : Fin H → Shape)
    (west east vertical : Column H) (north : Fin 3) : ℂ :=
  ∏ j : Fin H, shapeTensor (q j) (west j)
    ((Fin.snoc (α:=fun _=>Fin 3) vertical north) j.succ) (vertical j) (east j)

noncomputable def chosenColumnKernel {H : ℕ} (q : Fin H → Shape) (south north : Fin 3) :
    Matrix (Column H) (Column H) ℂ := fun west east =>
  ∑ vertical : Column H, if (Fin.snoc (α:=fun _=>Fin 3) vertical north) 0=south then
    chosenColumnProduct q west east vertical north else 0

lemma orientation_columns {W H : ℕ} (cfg : Cell W H → Shape)
    (west : Column H) (north : Fin W → Fin 3) (horizontal vertical : Fin W → Column H) :
    (network W H).orientation cfg (spinsFromColumns west north horizontal vertical) =
      ∏ i : Fin W, chosenColumnProduct (fun j=>cfg (i,j))
        ((Fin.cons (α:=fun _=>Column H) west horizontal) i.castSucc)
        (horizontal i) (vertical i) (north i) := by
  unfold TileNetwork.orientation chosenColumnProduct
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  simp [network,spinsFromColumns]

/-- The finite prescribed-boundary orientation coefficient of one exact
unoriented honeycomb configuration. -/
noncomputable def chosenPartition {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3) : ℂ :=
  ∑ horizontal : Fin W → Column H, ∑ vertical : Fin W → Column H,
    if (Fin.cons (α:=fun _=>Column H) west horizontal) (Fin.last W)=east ∧
        (∀ i, (Fin.snoc (α:=fun _=>Fin 3) (vertical i) (north i)) 0=south i) then
      (network W H).orientation cfg (spinsFromColumns west north horizontal vertical) else 0

lemma chosenPartition_eq_matrixPath {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3) :
    chosenPartition cfg west east south north =
      matrixPath (fun i=>chosenColumnKernel (fun j=>cfg (i,j)) (south i) (north i)) west east := by
  classical
  unfold chosenPartition matrixPath
  apply Finset.sum_congr rfl
  intro horizontal hhorizontal
  by_cases he : (Fin.cons (α:=fun _=>Column H) west horizontal) (Fin.last W)=east
  · simp only [he,true_and,ite_true]
    simp_rw [orientation_columns]
    unfold chosenColumnKernel
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro vertical hvertical
    rw [Fintype.prod_ite_zero]
    split_ifs <;> rfl
  · simp [he]

lemma chosenPartition_eq_transfer {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3) :
    chosenPartition cfg west east south north =
      (List.ofFn (fun i=>chosenColumnKernel (fun j=>cfg (i,j)) (south i) (north i))).prod west east := by
  rw [chosenPartition_eq_matrixPath,matrixPath_eq_prod]

lemma chosenPartition_eq_grid_sum {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) (south north : Fin W → Fin 3) :
    chosenPartition cfg west east south north =
      ∑ σ : {σ : GridWire W H → Fin 3 // HasWestNorth west north σ},
        if (∀ j, σ.val (.inl (Fin.last W,j))=east j) ∧
            (∀ i, σ.val (.inr (i,0))=south i) then
          (network W H).orientation cfg σ.val else 0 := by
  classical
  rw [←(gridSpinsEquiv west north).sum_comp,Fintype.sum_prod_type]
  unfold chosenPartition
  apply Finset.sum_congr rfl
  intro horizontal hh
  apply Finset.sum_congr rfl
  intro vertical hv
  change (if (Fin.cons (α:=fun _=>Column H) west horizontal) (Fin.last W)=east ∧
      (∀ i, (Fin.snoc (α:=fun _=>Fin 3) (vertical i) (north i)) 0=south i) then
      (network W H).orientation cfg (spinsFromColumns west north horizontal vertical) else 0) =
    (if (∀ j, (Fin.cons (α:=fun _=>Column H) west horizontal) (Fin.last W) j=east j) ∧
      (∀ i, (Fin.snoc (α:=fun _=>Fin 3) (vertical i) (north i)) 0=south i) then
      (network W H).orientation cfg (spinsFromColumns west north horizontal vertical) else 0)
  congr 1
  exact propext (and_congr funext_iff Iff.rfl)

lemma chosenColumnKernel_eq_spin {H : ℕ} (q : Fin H → Shape) (south north : Spin)
    (west east : Fin H → Spin) :
    chosenColumnKernel q (spinEquiv south) (spinEquiv north)
      (columnSpinEquiv H west) (columnSpinEquiv H east) = shapeKernel q south north west east := by
  classical
  unfold chosenColumnKernel shapeKernel
  rw [←(columnSpinEquiv H).sum_comp]
  apply Finset.sum_congr rfl
  intro vertical hv
  have hs : ∀ j : Fin (H+1),
      Fin.snoc (α:=fun _=>Fin 3) (columnSpinEquiv H vertical) (spinEquiv north) j =
      spinEquiv (Fin.snoc (α:=fun _=>Spin) vertical north j) := by
    intro j
    cases j using Fin.lastCases <;> simp
  simp only [hs,Equiv.apply_eq_iff_eq]
  split_ifs
  · unfold chosenColumnProduct
    apply Finset.prod_congr rfl
    intro j hj
    rw [hs]
    rfl
  · rfl

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

lemma occupancy_orientations_injective {xs ys : List Spin}
    (ho : occupancy xs=occupancy ys) (hs : orientations xs=orientations ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [occupancy]
  | cons x xs ih =>
    cases ys with
    | nil => simp [occupancy] at ho
    | cons y ys =>
      cases x with
      | none =>
        cases y with
        | none =>
          have ho' : occupancy xs=occupancy ys := by simpa [occupancy] using ho
          have hs' : orientations xs=orientations ys := by simpa [orientations] using hs
          exact congrArg (List.cons none) (ih ho' hs')
        | some b => simp [occupancy] at ho
      | some a =>
        cases y with
        | none => simp [occupancy] at ho
        | some b =>
          have ho' : occupancy xs=occupancy ys := by simpa [occupancy] using ho
          have hs' : a=b ∧ orientations xs=orientations ys := by simpa [orientations] using hs
          rcases hs' with ⟨rfl,hs'⟩
          exact congrArg (List.cons (some a)) (ih ho' hs')

lemma orientations_length (xs : List Spin) :
    (orientations xs).length=(occupancy xs).count true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simpa [orientations,occupancy,List.count_cons] using ih

lemma embed_delta (xs : List Spin) :
    embed (occupancy xs) (fun ys=>if ys=orientations xs then (1:ℂ) else 0) =
      (fun ys=>if ys=xs then 1 else 0) := by
  funext ys
  unfold embed
  by_cases ho : occupancy ys=occupancy xs
  · rw [ite_eq_left ho]
    by_cases hs : orientations ys=orientations xs
    · simp [occupancy_orientations_injective ho hs]
    · have hne : ys≠xs := by intro h; subst ys; exact hs rfl
      simp [hs,hne]
  · have hne : ys≠xs := by intro h; subst ys; exact ho rfl
    simp [ho,hne]

lemma eq_arrowState (xs : List Spin) (a : Bool) (hc : (occupancy xs).count true=1)
    (hs : orientations xs=[a]) : xs=arrowState (occupancy xs) a := by
  apply occupancy_orientations_injective
  · rw [occupancy_arrowState]
  · rw [orientations_arrowState,hc,hs]
    rfl

noncomputable def shapeFold {n : ℕ} (cs : List (Fin n → PhysicalTiles.Shape)) (f : DiluteState) : DiluteState :=
  cs.foldr (fun q f=>shapeColumn (List.ofFn q) f) f

lemma shapeFold_resolved {b n : ℕ} (hb : b≤1) (cs : List (Fin n → PhysicalTiles.Shape))
    {root : State} {f : DiluteState} (hf : Resolved b n root f) :
    Resolved b n root (shapeFold cs f) := by
  induction cs with
  | nil => exact hf
  | cons q cs ih => exact shapeColumn_resolved hb _ (by simp) ih

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization PhysicalTiles
open scoped BigOperators Matrix

noncomputable def columnVector (H : ℕ) (f : DiluteState) : Column H → ℂ :=
  fun east => f (List.ofFn (fun j=>spinEquiv.symm (east j)))

lemma chosenColumn_mulVec {H : ℕ} (q : Fin H → Shape) (f : DiluteState) :
    (chosenColumnKernel q 1 1).mulVec (columnVector H f) =
      columnVector H (shapeColumn (List.ofFn q) f) := by
  classical
  funext w
  obtain ⟨west,rfl⟩ := (columnSpinEquiv H).surjective w
  simp only [columnVector,columnSpinEquiv_apply,Equiv.symm_apply_apply]
  rw [shapeColumn_eq_kernel]
  unfold Matrix.mulVec dotProduct
  rw [←(columnSpinEquiv H).sum_comp]
  apply Finset.sum_congr rfl
  intro east heast
  change chosenColumnKernel q (spinEquiv none) (spinEquiv none)
    (columnSpinEquiv H west) (columnSpinEquiv H east) * _ = _
  rw [chosenColumnKernel_eq_spin]
  change _ * f (List.ofFn (fun j=>spinEquiv.symm (spinEquiv (east j)))) = _
  simp only [Equiv.symm_apply_apply]

lemma chosenProduct_mulVec {H : ℕ} (cs : List (Fin H → Shape)) (f : DiluteState) :
    (cs.map (fun q=>chosenColumnKernel q 1 1)).prod.mulVec (columnVector H f) =
      columnVector H (shapeFold cs f) := by
  induction cs generalizing f with
  | nil => simp [shapeFold]
  | cons q cs ih =>
    rw [List.map_cons,List.prod_cons,←Matrix.mulVec_mulVec,ih,chosenColumn_mulVec]
    rfl

lemma vector_delta {H : ℕ} (east : Column H) :
    columnVector H (fun xs=>if xs=List.ofFn (fun j=>spinEquiv.symm (east j)) then (1:ℂ) else 0) =
      fun e=>if e=east then 1 else 0 := by
  classical
  funext e
  change (if List.ofFn (fun j=>spinEquiv.symm (e j)) =
    List.ofFn (fun j=>spinEquiv.symm (east j)) then (1:ℂ) else 0) = _
  have heq : List.ofFn (fun j=>spinEquiv.symm (e j)) =
      List.ofFn (fun j=>spinEquiv.symm (east j)) ↔ e=east := by
    constructor
    · intro hh
      have hf := List.ofFn_injective hh
      funext j
      exact spinEquiv.symm.injective (congrFun hf j)
    · rintro rfl; rfl
  simp only [heq]

/-- Fixed-shape normalized crossing coefficients on the exact source grid
are 0 or 1, endpointwise. No positivity of local complex phases is assumed. -/
theorem chosenPartition_zero_or_one {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H)
    (hi : (occupancy (List.ofFn (fun j=>spinEquiv.symm (east j)))).count true=1)
    (ho : (occupancy (List.ofFn (fun j=>spinEquiv.symm (west j)))).count true=1) :
    chosenPartition cfg west east (fun _=>1) (fun _=>1)=0 ∨
    chosenPartition cfg west east (fun _=>1) (fun _=>1)=1 := by
  classical
  let xs := List.ofFn (fun j=>spinEquiv.symm (east j))
  let ys := List.ofFn (fun j=>spinEquiv.symm (west j))
  let root : State := fun zs=>if zs=orientations xs then 1 else 0
  let cs := List.ofFn (fun i : Fin W => fun j : Fin H => cfg (i,j))
  have hf : Resolved 1 H root (embed (occupancy xs) root) :=
    .basis (occupancy xs) 0 .start (by simp [xs,occupancy]) (by simpa using hi)
  have hylen : (orientations ys).length=1 := (orientations_length ys).trans ho
  obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp hylen
  have hy : ys=arrowState (occupancy ys) a := eq_arrowState ys a ho ha
  have hv := congrFun (chosenProduct_mulVec cs (embed (occupancy xs) root)) west
  have hemb : embed (occupancy xs) root = fun zs=>if zs=xs then 1 else 0 := embed_delta xs
  rw [hemb,vector_delta] at hv
  simp only [Matrix.mulVec,dotProduct,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hv
  have hmat : chosenPartition cfg west east (fun _=>1) (fun _=>1) =
      shapeFold cs (embed (occupancy xs) root) ys := by
    rw [chosenPartition_eq_transfer]
    have hcs : List.ofFn (fun i=>chosenColumnKernel (fun j=>cfg (i,j)) 1 1) =
        cs.map (fun q=>chosenColumnKernel q 1 1) := by
      rw [List.map_ofFn]
      rfl
    rw [hcs]
    simpa only [columnVector,xs,ys,hemb] using hv
  rw [hmat,hy]
  rcases resolved_one_strand (shapeFold_resolved (by omega : 1≤1) cs hf)
    (occupancy ys) ho with hzero|hone
  · exact Or.inl (hzero a)
  · rw [hone a]
    unfold root
    split_ifs <;> simp

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

lemma resolved_vacuum {n : ℕ} {root : State} {f : DiluteState}
    (hf : Resolved 0 n root f) :
    f (List.replicate n none)=0 ∨ f (List.replicate n none)=root [] := by
  cases hf with
  | zero => exact Or.inl rfl
  | basis o k w hl hc =>
    by_cases ho : List.replicate n false=o
    · subst o
      have hk : k=0 := by simp [List.count_replicate] at hc; omega
      subst k
      by_cases hw : w=.start
      · subst w
        right
        simp [embed,occupancy,orientations,PlanarWord.eval]
      · left
        simpa [embed,occupancy,orientations] using closed_word_zero w hw root
    · left
      simp [embed,occupancy,ho]

lemma vacuum_delta_resolved (n : ℕ) :
    Resolved 0 n (fun _=>1)
      (fun zs=>if zs=List.replicate n none then (1:ℂ) else 0) := by
  have hf : Resolved 0 n (fun _=>1)
      (embed (List.replicate n false) (fun _=>1)) :=
    .basis _ 0 .start (by simp) (by simp [List.count_replicate])
  convert hf using 1
  funext zs
  simp only [embed]
  have heq : occupancy zs=List.replicate n false ↔ zs=List.replicate n none := by
    constructor
    · intro hz
      apply occupancy_orientations_injective
      · simpa [occupancy] using hz
      · have hh := orientations_length zs
        rw [hz] at hh
        have hcnt : (List.replicate n false).count true=0 := by simp [List.count_replicate]
        rw [hcnt] at hh
        have hn : orientations zs=[] := List.length_eq_zero_iff.mp hh
        rw [hn]
        simp [orientations]
    · rintro rfl; simp [occupancy]
  simp only [heq]

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization PhysicalTiles
open scoped BigOperators Matrix

lemma chosenPartition_eq_shapeFold {W H : ℕ} (cfg : Cell W H → Shape)
    (west east : Column H) :
    chosenPartition cfg west east (fun _=>1) (fun _=>1) =
      shapeFold (List.ofFn (fun i : Fin W => fun j : Fin H=>cfg (i,j)))
        (fun xs=>if xs=List.ofFn (fun j=>spinEquiv.symm (east j)) then (1:ℂ) else 0)
        (List.ofFn (fun j=>spinEquiv.symm (west j))) := by
  classical
  let cs := List.ofFn (fun i : Fin W => fun j : Fin H=>cfg (i,j))
  have hv := congrFun (chosenProduct_mulVec cs
    (fun xs=>if xs=List.ofFn (fun j=>spinEquiv.symm (east j)) then (1:ℂ) else 0)) west
  rw [vector_delta] at hv
  simp only [Matrix.mulVec,dotProduct,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hv
  rw [chosenPartition_eq_transfer]
  have hcs : List.ofFn (fun i=>chosenColumnKernel (fun j=>cfg (i,j)) 1 1) =
      cs.map (fun q=>chosenColumnKernel q 1 1) := by
    rw [List.map_ofFn]
    rfl
  rw [hcs]
  exact hv

/-- Actual finite-grid orientation coefficient with fixed unoriented
configuration and vacant boundary. It is real and nonnegative, despite
its complex local factors. -/
theorem chosen_vacuum_zero_or_one {W H : ℕ} (cfg : Cell W H → Shape) :
    chosenPartition cfg (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1)=0 ∨
    chosenPartition cfg (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1)=1 := by
  rw [chosenPartition_eq_shapeFold]
  have hn : List.ofFn (fun _ : Fin H=>spinEquiv.symm (1:Fin 3)) =
      List.replicate H none := by simp [spinEquiv]
  simp only [hn]
  exact resolved_vacuum (shapeFold_resolved (by omega : 0≤1) _ (vacuum_delta_resolved H))

lemma prescribed_shape_expansion {W H : ℕ} (west east : Column H)
    (south north : Fin W → Fin 3) :
    prescribedPartition W H west east south north =
      ∑ cfg : Cell W H → Shape, (kappa:ℂ)^(∑ t, (cfg t).visits) *
        chosenPartition cfg west east south north := by
  classical
  rw [prescribedPartition_eq_grid_sum]
  simp_rw [physical_network_expansion,Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cfg hcfg
  rw [chosenPartition_eq_grid_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  split_ifs <;> simp

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators
lemma addOne_span {n : ℕ} {f : DiluteState} (hf : PlanarSpan n f) :
    PlanarSpan (n+1) (addOne f) := by
  induction hf with
  | zero =>
    have h : addOne (fun _ => 0) = fun _ => 0 := by
      funext xs; cases xs with
      | nil => rfl
      | cons x xs => cases x <;> rfl
    rw [h]; exact .zero
  | basis o k w hl hc =>
    rw [addOne_embed]
    exact .basis _ k w (by simp [hl]) (by simpa using hc)
  | add hf hg ihf ihg =>
    have h : ∀ f g, addOne (fun xs => f xs + g xs) =
        fun xs => addOne f xs + addOne g xs := by
      intro f g; funext xs; cases xs with
      | nil => simp [addOne]
      | cons x xs => cases x <;> simp [addOne]
    rw [h]; exact .add ihf ihg
  | smul z hf ihf =>
    have h : ∀ f, addOne (fun xs => z * f xs) = fun xs => z * addOne f xs := by
      intro f; funext xs; cases xs with
      | nil => simp [addOne]
      | cons x xs => cases x <;> simp [addOne]
    rw [h]; exact .smul z ihf

lemma removeOne_span {n : ℕ} {f : DiluteState} (hf : PlanarSpan (n+1) f) :
    PlanarSpan n (removeOne f) := by
  induction hf with
  | zero => exact .zero
  | add hf hg ihf ihg => exact .add ihf ihg
  | smul z hf ihf => exact .smul z ihf
  | basis o k w hl hc =>
    cases o using List.reverseRecOn with
    | nil => simp at hl
    | append_singleton pre a =>
      rw [removeOne_embed]
      split_ifs with ha
      · subst a
        exact .basis _ k w (by simpa using hl) (by simpa using hc)
      · exact .zero

lemma planarRow_span {n i : ℕ} (ts : List TileWeights) (hi : i+ts.length<n)
    {f : DiluteState} (hf : PlanarSpan n f) : PlanarSpan n (planarRow i ts f) := by
  induction ts generalizing i f with
  | nil => exact hf
  | cons t ts ih =>
    apply ih (by simp at hi; omega)
    exact act_span t (by simp at hi; omega) hf

lemma planarRow_vacuum {n i : ℕ} (ts : List TileWeights) (hi : i+ts.length<n)
    {f : DiluteState} (hf : PlanarSpan n f) :
    planarRow i ts f (List.replicate n none) = f (List.replicate n none) := by
  induction ts generalizing i f with
  | nil => rfl
  | cons t ts ih =>
    have hstep : i+1<n := by simp at hi; omega
    rw [planarRow,ih (by simp at hi; omega) (act_span t hstep hf),act_vacuum t hstep hf]

/-- A literal column with unmarked top and bottom ports. -/
noncomputable def vacuumColumn (t : TileWeights) (n : ℕ) (f : DiluteState) : DiluteState :=
  removeOne (planarRow 0 (List.replicate n t) (addOne f))

lemma vacuumColumn_span (t : TileWeights) {n : ℕ} {f : DiluteState} (hf : PlanarSpan n f) :
    PlanarSpan n (vacuumColumn t n f) := by
  apply removeOne_span
  apply planarRow_span (List.replicate n t) (by simp)
  exact addOne_span hf

lemma vacuumColumn_vacuum (t : TileWeights) {n : ℕ} {f : DiluteState} (hf : PlanarSpan n f) :
    vacuumColumn t n f (List.replicate n none) = f (List.replicate n none) := by
  unfold vacuumColumn removeOne
  change planarRow 0 (List.replicate n t) (addOne f)
    (List.replicate n none ++ List.replicate 1 none) = _
  rw [←List.replicate_add,planarRow_vacuum (List.replicate n t) (by simp) (addOne_span hf)]
  simp [List.replicate_succ,addOne]

/-- Finite physical columns cannot create an unmarked closed contribution:
all such closed loops cancel exactly at the manuscript parameter. -/
theorem vacuumRectangle (t : TileWeights) (n m : ℕ) :
    ((vacuumColumn t n)^[m]) (embed (List.replicate n false) (fun _ => 1))
      (List.replicate n none) = 1 := by
  have gen : ∀ m {f : DiluteState}, PlanarSpan n f →
      ((vacuumColumn t n)^[m]) f (List.replicate n none) = f (List.replicate n none) := by
    intro m
    induction m with
    | zero => intro f hf; rfl
    | succ m ih =>
      intro f hf
      rw [Function.iterate_succ_apply,ih (vacuumColumn_span t hf),vacuumColumn_vacuum t hf]
  have hf : PlanarSpan n (embed (List.replicate n false) (fun _ => 1)) :=
    PlanarSpan.basis (List.replicate n false) 0 .start
      (by simp) (by simp [List.count_replicate])
  rw [gen m hf]
  simp [embed,occupancy]

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators Matrix

lemma addOne_cons (f : DiluteState) (x : Spin) (xs : List Spin) :
    addOne f (x::xs) = if x=none then f xs else 0 := by cases x <;> rfl

/-- The finite orientation sum and the column operator agree also for a
general boundary state, so that consecutive columns compose exactly. -/
lemma vacuumColumn_eq_kernel (t : TileWeights) (n : ℕ) (f : DiluteState)
    (west : Fin n → Spin) :
    vacuumColumn t n f (List.ofFn west) =
      ∑ east : Fin n → Spin, columnKernelSpin t n none none west east * f (List.ofFn east) := by
  classical
  unfold vacuumColumn removeOne
  rw [planarRow_eq_columnContraction]
  unfold columnContraction columnKernelSpin
  apply Finset.sum_congr rfl
  intro east heast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro vertical hvertical
  rw [addOne_cons]
  split_ifs <;> simp

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization
open scoped BigOperators Matrix

lemma column_mulVec (H : ℕ) (f : DiluteState) :
    (columnKernel H 1 1).mulVec (columnVector H f) =
      columnVector H (vacuumColumn physicalWeights H f) := by
  classical
  funext w
  obtain ⟨west,rfl⟩ := (columnSpinEquiv H).surjective w
  simp only [columnVector,columnSpinEquiv_apply,Equiv.symm_apply_apply]
  rw [vacuumColumn_eq_kernel]
  unfold Matrix.mulVec dotProduct
  rw [←(columnSpinEquiv H).sum_comp]
  apply Finset.sum_congr rfl
  intro east heast
  change columnKernel H (spinEquiv none) (spinEquiv none)
    (columnSpinEquiv H west) (columnSpinEquiv H east) * _ = _
  rw [columnKernel_eq_spin]
  change _ * f (List.ofFn (fun j => spinEquiv.symm (spinEquiv (east j)))) = _
  simp only [Equiv.symm_apply_apply]

lemma column_pow_mulVec (H W : ℕ) (f : DiluteState) :
    ((columnKernel H 1 1)^W).mulVec (columnVector H f) =
      columnVector H (((vacuumColumn physicalWeights H)^[W]) f) := by
  induction W generalizing f with
  | zero => simp
  | succ W ih =>
    rw [pow_succ,←Matrix.mulVec_mulVec,column_mulVec,ih,Function.iterate_succ_apply]

lemma vector_vacuum (H : ℕ) :
    columnVector H (embed (List.replicate H false) (fun _=>1)) =
      fun east => if east=(fun _=>1) then 1 else 0 := by
  classical
  funext east
  have he : occupancy (List.ofFn (fun j => spinEquiv.symm (east j))) =
      List.replicate H false ↔ east=fun _=>1 := by
    rw [occupancy,List.map_ofFn,←List.ofFn_const, List.ofFn_injective.eq_iff]
    constructor
    · intro h
      funext j
      have hh := congrFun h j
      simpa [Function.comp_def,spinEquiv] using hh
    · rintro rfl
      rfl
  simp only [columnVector,embed,he]

/-- The actual finite strip transfer has unmarked empty-empty entry one.
This is a literal honeycomb-grid identity, not an assumed loop pairing. -/
theorem physical_vacuum_entry (H W : ℕ) :
    ((columnKernel H 1 1)^W) (fun _=>1) (fun _=>1) = 1 := by
  classical
  have hm := congrFun (column_pow_mulVec H W (embed (List.replicate H false) (fun _=>1)))
    (fun _=>1)
  rw [vector_vacuum] at hm
  simp only [Matrix.mulVec,dotProduct,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hm
  rw [hm]
  change ((vacuumColumn physicalWeights H)^[W]) _ (List.ofFn (fun _ : Fin H => none))=1
  simpa using vacuumRectangle physicalWeights H W

/-- Equivalent four-wall statement for the finite physical tensor partition. -/
theorem prescribed_vacuum_partition (W H : ℕ) :
    prescribedPartition W H (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1) = 1 := by
  rw [prescribedPartition_eq_transfer]
  simp only [List.ofFn_const,List.prod_replicate]
  exact physical_vacuum_entry H W

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization PhysicalTiles
open scoped BigOperators Matrix

lemma shapeTensor_empty_ne_zero (w n s e : Fin 3) :
    shapeTensor .empty w n s e ≠ 0 ↔ w=1 ∧ n=1 ∧ s=1 ∧ e=1 := by
  simp only [shapeTensor,Planar.vacant,mul_ne_zero_iff]
  split_ifs <;> simp_all

lemma chosenColumnProduct_empty {H : ℕ} (west east vertical : Column H) :
    chosenColumnProduct (fun _=>.empty) west east vertical 1 =
      if west=(fun _=>1) ∧ east=(fun _=>1) ∧ vertical=(fun _=>1) then 1 else 0 := by
  classical
  split_ifs with he
  · rcases he with ⟨rfl,rfl,rfl⟩
    unfold chosenColumnProduct
    have hv : Fin.snoc (α:=fun _=>Fin 3) (fun _ : Fin H=>1) 1=(fun _=>1) := by
      funext i; cases i using Fin.lastCases <;> simp
    simp [hv,shapeTensor,Planar.vacant]
  · by_contra hn
    apply he
    have hp (j : Fin H) := shapeTensor_empty_ne_zero (west j)
      ((Fin.snoc (α:=fun _=>Fin 3) vertical 1) j.succ) (vertical j) (east j)
    have hh (j : Fin H) : west j=1 ∧
        (Fin.snoc (α:=fun _=>Fin 3) vertical 1) j.succ=1 ∧ vertical j=1 ∧ east j=1 :=
      (hp j).mp ((Finset.prod_ne_zero_iff.mp hn) j (Finset.mem_univ j))
    exact ⟨funext (fun j=>(hh j).1),funext (fun j=>(hh j).2.2.2),
      funext (fun j=>(hh j).2.2.1)⟩

lemma chosenColumnKernel_empty {H : ℕ} (west east : Column H) :
    chosenColumnKernel (fun _=>.empty) 1 1 west east =
      if west=(fun _=>1) ∧ east=(fun _=>1) then 1 else 0 := by
  classical
  unfold chosenColumnKernel
  rw [Finset.sum_eq_single (fun _=>1)]
  · rw [chosenColumnProduct_empty]
    have hv : Fin.snoc (α:=fun _=>Fin 3) (fun _ : Fin H=>1) 1=(fun _=>1) := by
      funext i; cases i using Fin.lastCases <;> simp
    simp [hv]
  · intro v hv hne
    rw [chosenColumnProduct_empty]
    simp [hne]
  · simp

lemma chosenProduct_empty_vacuum (H W : ℕ) :
    ((chosenColumnKernel (fun _ : Fin H=>.empty) 1 1)^W)
        (fun _=>1) (fun _=>1) = 1 := by
  classical
  induction W with
  | zero => simp
  | succ W ih =>
    rw [pow_succ,Matrix.mul_apply]
    simp_rw [chosenColumnKernel_empty]
    simpa using ih

lemma chosen_empty_partition (W H : ℕ) :
    chosenPartition (fun _ : Cell W H=>.empty)
      (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1) = 1 := by
  rw [chosenPartition_eq_transfer]
  simp only [List.ofFn_const,List.prod_replicate]
  exact chosenProduct_empty_vacuum H W

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization PhysicalTiles
open scoped BigOperators Matrix

/-- Every nonempty fixed unoriented configuration with vacant boundary has
vanishing orientation sum on the actual finite honeycomb grid. No turning
lemma or assumed graphical cancellation is being invoked. -/
theorem chosen_nonempty_vacuum_zero {W H : ℕ} (cfg : Cell W H → Shape)
    (hne : cfg ≠ fun _=>.empty) :
    chosenPartition cfg (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1)=0 := by
  classical
  let F : (Cell W H → Shape) → ℝ := fun q=>
    kappa^(∑ t, (q t).visits) *
      (chosenPartition q (fun _=>1) (fun _=>1) (fun _=>1) (fun _=>1)).re
  have hk : 0<kappa := Real.rpow_pos_of_pos (by positivity) _
  have hnonneg (q : Cell W H → Shape) : 0≤F q := by
    rcases chosen_vacuum_zero_or_one q with hz|hone
    · simp [F,hz]
    · simp only [F,hone,Complex.one_re,mul_one]
      exact (pow_pos hk _).le
  have hsum : (∑ q, F q)=1 := by
    have hh := prescribed_shape_expansion (fun _ : Fin H=>1) (fun _=>1)
      (fun _ : Fin W=>1) (fun _=>1)
    rw [prescribed_vacuum_partition] at hh
    have hs := congrArg Complex.re hh
    simpa only [F,Complex.re_sum,←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,Complex.one_re] using hs.symm
  have he : F (fun _=>.empty)=1 := by
    simp [F,chosen_empty_partition,Shape.visits]
  rcases chosen_vacuum_zero_or_one cfg with hz|hone
  · exact hz
  · have hq : F cfg=kappa^(∑ t, (cfg t).visits) := by simp [F,hone]
    have hle : (∑ q ∈ ({(fun _=>.empty),cfg} : Finset (Cell W H → Shape)),F q) ≤
        ∑ q, F q :=
      Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by intros; exact hnonneg _)
    rw [Finset.sum_pair (Ne.symm hne),he,hq,hsum] at hle
    have hp := pow_pos hk (∑ t, (cfg t).visits)
    linarith

end CriticalHoneycomb.Transfer.RasterGrid

end OAI
