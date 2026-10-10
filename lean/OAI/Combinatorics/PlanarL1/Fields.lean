import OAI.Combinatorics.PlanarL1.Distance

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)
/-- A scalar field on the whole band, including all its components. Its only
compatibility condition is equality at actual allowed switch heights. -/
structure Field (J : Set ℝ) (L : NNReal) where
  value : Fin n → J → ℝ
  vertical : ∀ i, LipschitzWith L (value i)
  switch : ∀ i j (H : J), H.val ∈ M.heights i j → value i H = value j H

namespace Field

variable {M} {J : Set ℝ} {L : NNReal}

lemma path_bound (F : M.Field J L) {i j : Fin n} (p : M.Path J i j)
    (a b : J) : |F.value i a - F.value j b| ≤ L * p.length a.val b.val := by
  induction p generalizing a b with
  | nil i =>
    simpa only [Path.length, Real.dist_eq, Subtype.dist_eq] using (F.vertical i).dist_le_mul a b
  | @cons i j k H hH hs p ih =>
    have ht := abs_sub_le (F.value i a) (F.value i ⟨H,hH⟩) (F.value k b)
    rw [F.switch i j ⟨H,hH⟩ hs] at ht
    have hv := (F.vertical i).dist_le_mul a ⟨H,hH⟩
    rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq, F.switch i j ⟨H,hH⟩ hs] at hv
    have hi := ih ⟨H,hH⟩ b
    change _ ≤ L * (|a.val - H| + p.length H b.val)
    nlinarith

/-- Vertical Lipschitz bounds and switch equality imply the intrinsic bound,
by summing on an actual attaining shortest path. -/
lemma lipschitz (F : M.Field J L) (hJ : IsClosed J) (root : Fin n) :
    LipschitzWith L (fun x : M.Point J root => F.value x.column ⟨x.height,x.inBand⟩) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  rw [Real.dist_eq]
  simpa only [hp] using F.path_bound p ⟨x.height,x.inBand⟩ ⟨y.height,y.inBand⟩

end Field

namespace Point

variable {M} {J : Set ℝ} {root : Fin n}

/-- Truncated point distance on EVERY column. Columns outside the metric
component have the constant ceiling. -/
noncomputable def truncated (o : M.Point J root) (D : ℝ) (i : Fin n) (H : J) : ℝ := by
  classical
  exact if hi : (M.activeGraph J).Reachable root i then
    min (dist o (⟨i,H.val,H.property,hi⟩ : M.Point J root)) D else D

lemma truncated_of_reachable (o : M.Point J root) (D : ℝ) (i : Fin n) (H : J)
    (hi : (M.activeGraph J).Reachable root i) :
    o.truncated D i H = min (dist o (⟨i,H.val,H.property,hi⟩ : M.Point J root)) D := by
  simp only [truncated, dite_eq_left hi]

lemma truncated_le (o : M.Point J root) (D : ℝ) (i : Fin n) (H : J) :
    o.truncated D i H ≤ D := by
  unfold truncated
  split
  · exact min_le_right _ _
  · exact le_rfl

lemma truncated_vertical (o : M.Point J root) (D : ℝ) (i : Fin n) :
    LipschitzWith 1 (o.truncated D i) := by
  by_cases hi : (M.activeGraph J).Reachable root i
  · have hp : LipschitzWith 1 (fun H : J => (⟨i,H.val,H.property,hi⟩ : M.Point J root)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Point.dist_same_column (⟨i,x.val,x.property,hi⟩ : M.Point J root)
        (⟨i,y.val,y.property,hi⟩ : M.Point J root) rfl]
      simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq]
      exact le_rfl
    have ho : LipschitzWith 1 (fun x : M.Point J root => dist o x) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [NNReal.coe_one,one_mul] using dist_dist_dist_le_right o x y
    have hd := ho.comp hp
    have he : o.truncated D i = (fun H : J => min (dist o
        (⟨i,H.val,H.property,hi⟩ : M.Point J root)) D) :=
      funext (fun H => o.truncated_of_reachable D i H hi)
    rw [he]
    simpa only [mul_one,Function.comp_apply] using hd.min_const D
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [truncated,dite_eq_right hi,dist_self,NNReal.coe_one,one_mul]
    exact dist_nonneg

lemma truncated_switch (o : M.Point J root) (D : ℝ) (i j : Fin n) (H : J)
    (hs : H.val ∈ M.heights i j) : o.truncated D i H = o.truncated D j H := by
  have ha : (M.activeGraph J).Adj i j := ⟨H.val,H.property,hs⟩
  by_cases hi : (M.activeGraph J).Reachable root i
  · have hj := hi.trans ha.reachable
    rw [truncated_of_reachable _ _ _ _ hi, truncated_of_reachable _ _ _ _ hj]
    congr 1
    let x : M.Point J root := ⟨i,H.val,H.property,hi⟩
    let y : M.Point J root := ⟨j,H.val,H.property,hj⟩
    have hz : dist x y = 0 := by
      apply le_antisymm _ dist_nonneg
      simpa only [x,y,sub_self,abs_zero,add_zero] using x.dist_le_switch y H.property hs
    exact PseudoMetricSpace.dist_eq_of_dist_zero o hz
  · have hj : ¬(M.activeGraph J).Reachable root j := by
      intro hj
      exact hi (hj.trans ha.symm.reachable)
    simp only [truncated,dite_eq_right hi,dite_eq_right hj]

noncomputable def truncatedField (o : M.Point J root) (D : ℝ) : M.Field J 1 where
  value := o.truncated D
  vertical := o.truncated_vertical D
  switch := o.truncated_switch D

lemma truncated_root (o : M.Point J root) (D : ℝ) (H : J) :
    o.truncated D o.column H = min |o.height - H.val| D := by
  rw [truncated_of_reachable _ _ _ _ o.reachable,
    Point.dist_same_column o (⟨o.column,H.val,H.property,o.reachable⟩ : M.Point J root) rfl]

lemma truncated_minimum (o : M.Point J root) (D : ℝ) (i : Fin n) (H : J) :
    o.truncated D o.column H ≤ o.truncated D i H := by
  rw [truncated_root]
  by_cases hi : (M.activeGraph J).Reachable root i
  · rw [truncated_of_reachable _ _ _ _ hi]
    exact min_le_min_right D (o.height_change_le (⟨i,H.val,H.property,hi⟩ : M.Point J root))
  · simp only [truncated,dite_eq_right hi]
    exact min_le_right _ _

/-- The strict sublevel connects to the root by a real shortest switching
path; every visited column remains in the same strict sublevel. -/
lemma truncated_sublevel_path (hJ : IsClosed J) (o : M.Point J root) (D t : ℝ)
    (ht : t ≤ D) (i : Fin n) (H : J) (hi : o.truncated D i H < t) :
    ∃ w : (M.activeGraph J).Walk i o.column,
      ∀ z ∈ w.support, o.truncated D z H < t := by
  have hir : (M.activeGraph J).Reachable root i := by
    by_contra hn
    simp only [truncated,dite_eq_right hn] at hi
    exact (not_lt_of_ge ht) hi
  rw [truncated_of_reachable _ _ _ _ hir] at hi
  have hdist : dist o (⟨i,H.val,H.property,hir⟩ : M.Point J root) < t := by
    rcases (min_lt_iff).mp hi with hi | hi
    · exact hi
    · exact False.elim ((not_lt_of_ge ht) hi)
  obtain ⟨p, _, hp⟩ := o.shortest_sublevel hJ (⟨i,H.val,H.property,hir⟩ : M.Point J root)
  refine ⟨p.word.reverse, ?_⟩
  intro z hz
  obtain ⟨hzr, hdz⟩ := hp z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)
  rw [truncated_of_reachable _ _ _ _ hzr]
  exact (min_le_left _ _).trans_lt (hdz.trans_lt hdist)

/-- The literal running-minimum projection of point distance, after cutting
at the chosen representative of the root. -/
noncomputable def supportValue {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) (i : Fin (k + 1)) (H : J) : ℝ :=
  Ordered.running ((finCycle o.column).symm w.column)
    (fun j => o.truncated (dist o w) (finCycle o.column j) H)
    ((finCycle o.column).symm i)

lemma supportValue_vertical {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) (i : Fin (k + 1)) : LipschitzWith 1 (o.supportValue w i) := by
  exact Ordered.running_lipschitz _ _ _ 1 (fun j => o.truncated_vertical _ _)

lemma supportValue_switch {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (hJ : IsClosed J) (o w : M.Point J r) (i j : Fin (k + 1)) (H : J)
    (hs : H.val ∈ M.heights i j) : o.supportValue w i H = o.supportValue w j H := by
  let e := finCycle o.column
  let f := fun z => o.truncated (dist o w) (e z) H
  have hzero : e 0 = o.column := by simp [e,finCycle_apply]
  have hmin : ∀ z, f 0 ≤ f z := by
    intro z
    simpa only [f,hzero] using o.truncated_minimum (dist o w) (e z) H
  have hpath : ∀ t ≤ dist o w, ∀ z, f z < t →
      ∃ p : ((M.activeGraph J).comap e).Walk z 0, ∀ v ∈ p.support, f v < t := by
    intro t ht z hz
    obtain ⟨p,hp⟩ := o.truncated_sublevel_path hJ (dist o w) t ht (e z) H hz
    obtain ⟨q,hq⟩ := ColumnOrder.walk_comap_equiv e (p.copy rfl hzero.symm)
    refine ⟨q,fun v hv => ?_⟩
    exact hp (e v) (by simpa only [SimpleGraph.Walk.support_copy] using hq v hv)
  have hnc := ColumnOrder.noncrossing_comap_cycle (M.active_noncrossing J) o.column
  have heq : f (e.symm i) = f (e.symm j) := by
    simpa only [f,Equiv.apply_symm_apply] using o.truncated_switch (dist o w) i j H hs
  have hadj : ((M.activeGraph J).comap e).Adj (e.symm i) (e.symm j) := by
    simpa only [SimpleGraph.comap_adj,Equiv.apply_symm_apply] using
      (show (M.activeGraph J).Adj i j from ⟨H.val,H.property,hs⟩)
  change Ordered.running (e.symm w.column) f (e.symm i) =
    Ordered.running (e.symm w.column) f (e.symm j)
  rcases lt_trichotomy (e.symm i) (e.symm j) with hij | hij | hij
  · apply Ordered.running_switch _ _ hmin hij heq
    exact ColumnOrder.collision hnc f (dist o w) (fun z => o.truncated_le _ _ _) hpath hij hadj heq
  · rw [hij]
  · symm
    apply Ordered.running_switch _ _ hmin hij heq.symm
    exact ColumnOrder.collision hnc f (dist o w) (fun z => o.truncated_le _ _ _) hpath hij hadj.symm heq.symm

/-- Ordered support, with actual vertical and switch proofs. -/
noncomputable def supportField {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (hJ : IsClosed J) (o w : M.Point J r) : M.Field J 1 where
  value := o.supportValue w
  vertical := o.supportValue_vertical w
  switch := o.supportValue_switch hJ w

lemma supportValue_root {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) (H : J) :
    o.supportValue w o.column H = min |o.height - H.val| (dist o w) := by
  simp only [supportValue,finCycle_symm_apply,sub_self,Ordered.running_zero,
    finCycle_apply,zero_add,truncated_root]

lemma supportValue_target {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) : o.supportValue w w.column ⟨w.height,w.inBand⟩ = dist o w := by
  rw [supportValue,Ordered.running_target,Equiv.apply_symm_apply,
    truncated_of_reachable _ _ _ _ w.reachable]
  exact min_self _

lemma supportValue_bounds {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (o w : M.Point J r) (i : Fin (k + 1)) (H : J) :
    0 ≤ o.supportValue w i H ∧ o.supportValue w i H ≤ o.truncated (dist o w) i H := by
  let e := finCycle o.column
  let f := fun j => o.truncated (dist o w) (e j) H
  have hzero : e 0 = o.column := by simp [e,finCycle_apply]
  have hmin : ∀ z, f 0 ≤ f z := by
    intro z
    simpa only [f,hzero] using o.truncated_minimum (dist o w) (e z) H
  have hnonneg : 0 ≤ f 0 := by
    dsimp only [f]
    rw [hzero,truncated_root]
    exact le_min (abs_nonneg _) dist_nonneg
  exact ⟨hnonneg.trans (Ordered.le_running _ _ hmin _),
    by simpa only [supportValue,f,e,Equiv.apply_symm_apply] using
      Ordered.running_le (e.symm w.column) f (e.symm i)⟩

end Point

/-- Monotonicity on the two arcs, expressed in the circle cut at `a`.
The separate minimum condition records the wrap-around step to index zero. -/
def Field.OrderedFrom {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b : Fin (k + 1)) : Prop :=
  (∀ (H : J) i, F.value a H ≤ F.value i H) ∧
  (∀ (H : J) (i j : Fin (k + 1)), i ≤ j → j ≤ (finCycle a).symm b →
    F.value (finCycle a i) H ≤ F.value (finCycle a j) H) ∧
  (∀ (H : J) (i j : Fin (k + 1)), (finCycle a).symm b ≤ i → i ≤ j →
    F.value (finCycle a j) H ≤ F.value (finCycle a i) H)

namespace Point

lemma supportField_ordered {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (hJ : IsClosed J) (o w : M.Point J r) :
    (o.supportField hJ w).OrderedFrom o.column w.column := by
  have hmin (H : J) : ∀ z, o.truncated (dist o w) (finCycle o.column 0) H ≤
      o.truncated (dist o w) (finCycle o.column z) H := by
    simp only [finCycle_apply,zero_add]
    intro z
    exact o.truncated_minimum _ _ _
  refine ⟨?_,?_,?_⟩
  · intro H i
    change o.supportValue w o.column H ≤ o.supportValue w i H
    unfold supportValue
    simp only [finCycle_symm_apply,sub_self,Ordered.running_zero]
    simpa only [finCycle_symm_apply] using
      Ordered.le_running ((finCycle o.column).symm w.column)
        (fun z => o.truncated (dist o w) (finCycle o.column z) H) (hmin H)
        ((finCycle o.column).symm i)
  · intro H i j hij hjb
    change o.supportValue w (finCycle o.column i) H ≤ o.supportValue w (finCycle o.column j) H
    simp only [supportValue,Equiv.symm_apply_apply]
    exact Ordered.running_mono_left _ _ (hmin H) hij hjb
  · intro H i j hbi hij
    change o.supportValue w (finCycle o.column j) H ≤ o.supportValue w (finCycle o.column i) H
    simp only [supportValue,Equiv.symm_apply_apply]
    exact Ordered.running_mono_right _ _ hbi hij

/-- Lemma ord:support, on every representative of the whole band. No
connectivity of the whole band is assumed. The upper distance bound is on the
chosen finite-distance component, just as the source's infinite convention. -/
theorem exists_ordered_support {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {r : Fin (k + 1)}
    (hJ : IsClosed J) (o w : M.Point J r) :
    ∃ F : M.Field J 1, F.OrderedFrom o.column w.column ∧
      (∀ i H, 0 ≤ F.value i H ∧ F.value i H ≤ dist o w) ∧
      F.value o.column ⟨o.height,o.inBand⟩ = 0 ∧
      F.value w.column ⟨w.height,w.inBand⟩ = dist o w ∧
      ∀ x : M.Point J r, F.value x.column ⟨x.height,x.inBand⟩ ≤ dist o x := by
  refine ⟨o.supportField hJ w, o.supportField_ordered hJ w, ?_, ?_, ?_, ?_⟩
  · intro i H
    exact ⟨(o.supportValue_bounds w i H).1,
      (o.supportValue_bounds w i H).2.trans (o.truncated_le _ _ _)⟩
  · change o.supportValue w o.column ⟨o.height,o.inBand⟩ = 0
    rw [supportValue_root,sub_self,abs_zero,min_eq_left dist_nonneg]
  · exact o.supportValue_target w
  · intro x
    have h := (o.supportValue_bounds w x.column ⟨x.height,x.inBand⟩).2
    rw [truncated_of_reachable _ _ _ _ x.reachable] at h
    exact h.trans (min_le_left _ _)

end Point

namespace Field

/-- Signed open-arc membership. Boundary columns have sign zero. -/
def arcSign {k : ℕ} (a b i : Fin (k + 1)) : ℝ :=
  if i = a ∨ i = b then 0 else if (finCycle a).symm i < (finCycle a).symm b then 1 else -1

lemma arcSign_cases {k : ℕ} (a b i : Fin (k + 1)) :
    arcSign a b i = 0 ∨ arcSign a b i = 1 ∨ arcSign a b i = -1 := by
  unfold arcSign
  split_ifs <;> simp

lemma arcSign_zero_iff {k : ℕ} (a b i : Fin (k + 1)) :
    arcSign a b i = 0 ↔ i = a ∨ i = b := by
  unfold arcSign
  split_ifs <;> simp_all

lemma abs_arcSign_le {k : ℕ} (a b i : Fin (k + 1)) : |arcSign a b i| ≤ 1 := by
  rcases arcSign_cases a b i with h | h | h <;> simp [h]

/-- Source Z_s in the max metric on R x R: the two boundary images and the
images of actual switches between opposite OPEN arcs. -/
def wall {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b : Fin (k + 1)) : Set (ℝ × ℝ) :=
  {z | (∃ H : J, z = (F.value a H,H.val)) ∨
    (∃ H : J, z = (F.value b H,H.val)) ∨
    ∃ (i j : Fin (k + 1)) (H : J), H.val ∈ M.heights i j ∧
      arcSign a b i = 1 ∧ arcSign a b j = -1 ∧ z = (F.value i H,H.val)}

lemma wall_nonempty {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b : Fin (k + 1)) (H : J) : (F.wall a b).Nonempty := by
  exact ⟨(F.value a H,H.val),Or.inl ⟨H,rfl⟩⟩

lemma wall_of_boundary {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i : Fin (k + 1)) (H : J) (hi : arcSign a b i = 0) :
    (F.value i H,H.val) ∈ F.wall a b := by
  rcases (arcSign_zero_iff a b i).mp hi with hi | hi
  · exact Or.inl ⟨H,by rw [hi]⟩
  · exact Or.inr (Or.inl ⟨H,by rw [hi]⟩)

lemma wall_of_switch {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i j : Fin (k + 1)) (H : J) (hs : H.val ∈ M.heights i j)
    (hneq : arcSign a b i ≠ arcSign a b j) : (F.value i H,H.val) ∈ F.wall a b := by
  by_cases hi : arcSign a b i = 0
  · exact F.wall_of_boundary a b i H hi
  by_cases hj : arcSign a b j = 0
  · rw [F.switch i j H hs]
    exact F.wall_of_boundary a b j H hj
  rcases arcSign_cases a b i with hi' | hi' | hi'
  · exact False.elim (hi hi')
  · rcases arcSign_cases a b j with hj' | hj' | hj'
    · exact False.elim (hj hj')
    · exact False.elim (hneq (hi'.trans hj'.symm))
    · exact Or.inr (Or.inr ⟨i,j,H,hs,hi',hj',rfl⟩)
  · rcases arcSign_cases a b j with hj' | hj' | hj'
    · exact False.elim (hj hj')
    · exact Or.inr (Or.inr ⟨j,i,H,by rwa [M.symm j i],hj',hi',by rw [F.switch i j H hs]⟩)
    · exact False.elim (hneq (hi'.trans hj'.symm))

noncomputable def transverseValue {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i : Fin (k + 1)) (H : J) : ℝ :=
  arcSign a b i * Metric.infDist (F.value i H,H.val) (F.wall a b)

lemma coordinate_lipschitz {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (hL : 1 ≤ L) (i : Fin (k + 1)) :
    LipschitzWith L (fun H : J => (F.value i H,H.val)) := by
  apply LipschitzWith.of_dist_le_mul
  intro H T
  rw [Prod.dist_eq]
  refine max_le ((F.vertical i).dist_le_mul H T) ?_
  change dist H T ≤ L * dist H T
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith [dist_nonneg (x := H) (y := T)]

lemma transverse_vertical {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (hL : 1 ≤ L) (a b i : Fin (k + 1)) :
    LipschitzWith L (F.transverseValue a b i) := by
  have hd := (Metric.lipschitz_infDist_pt (F.wall a b)).comp (F.coordinate_lipschitz hL i)
  apply LipschitzWith.of_dist_le_mul
  intro H T
  have hh := hd.dist_le_mul H T
  simp only [one_mul,Function.comp_apply,Real.dist_eq] at hh
  rw [Real.dist_eq,transverseValue,transverseValue,← mul_sub,abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (abs_arcSign_le a b i)).trans hh

lemma transverse_switch {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i j : Fin (k + 1)) (H : J) (hs : H.val ∈ M.heights i j) :
    F.transverseValue a b i H = F.transverseValue a b j H := by
  by_cases he : arcSign a b i = arcSign a b j
  · simp only [transverseValue,he,F.switch i j H hs]
  · have hz := Metric.infDist_zero_of_mem (F.wall_of_switch a b i j H hs he)
    unfold transverseValue
    rw [F.switch i j H hs] at hz ⊢
    rw [hz,mul_zero,mul_zero]

/-- The transverse field. Its slope bound is inherited
from the original field (and at least one), with the switch identity proved. -/
noncomputable def transverse {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (hL : 1 ≤ L) (a b : Fin (k + 1)) : M.Field J L where
  value := F.transverseValue a b
  vertical := F.transverse_vertical hL a b
  switch := F.transverse_switch a b

lemma transverse_abs {k : ℕ} {M : Model (k + 1)} {J : Set ℝ} {L : NNReal}
    (F : M.Field J L) (a b i : Fin (k + 1)) (H : J) (hi : arcSign a b i ≠ 0) :
    |F.transverseValue a b i H| = Metric.infDist (F.value i H,H.val) (F.wall a b) := by
  rw [transverseValue,abs_mul,abs_of_nonneg Metric.infDist_nonneg]
  rcases arcSign_cases a b i with he | he | he
  · exact False.elim (hi he)
  · simp [he]
  · simp [he]

end Field

namespace Path

variable {M} {J : Set ℝ}

/-- The actual set of representatives visited by a finite switching path,
including every point of its vertical segments. -/
def trace : {i j : Fin n} → M.Path J i j → ℝ → ℝ → Set (Fin n × ℝ)
  | i, _, .nil _, a, b => {z | z.1 = i ∧ z.2 ∈ Set.uIcc a b}
  | i, _, .cons H _ _ p, a, b => {z | z.1 = i ∧ z.2 ∈ Set.uIcc a H} ∪ p.trace H b

lemma trace_column {i j : Fin n} (p : M.Path J i j) {a b : ℝ} {z : Fin n × ℝ}
    (hz : z ∈ p.trace a b) : z.1 ∈ p.word.support := by
  induction p generalizing a with
  | nil i =>
    simpa only [word,SimpleGraph.Walk.support_nil,List.mem_singleton] using hz.1
  | cons H hH hs p ih =>
    rcases hz with hz | hz
    · exact List.mem_cons.mpr (Or.inl hz.1)
    · exact List.mem_cons_of_mem _ (ih hz)

lemma trace_height (hJ : Set.OrdConnected J) {i j : Fin n} (p : M.Path J i j)
    {a b : ℝ} (ha : a ∈ J) (hb : b ∈ J) {z : Fin n × ℝ} (hz : z ∈ p.trace a b) : z.2 ∈ J := by
  induction p generalizing a with
  | nil i => exact hJ.uIcc_subset ha hb hz.2
  | cons H hH hs p ih =>
    rcases hz with hz | hz
    · exact hJ.uIcc_subset ha hH hz.2
    · exact ih hH hz

lemma abs_split {a b T : ℝ} (hT : T ∈ Set.uIcc a b) : |a - T| + |T - b| = |a - b| := by
  rcases le_total a b with hab | hab
  · have ht : a ≤ T ∧ T ≤ b := by
      rcases Set.mem_uIcc.mp hT with ht | ht <;> constructor <;> linarith
    rw [abs_of_nonpos (sub_nonpos.mpr ht.1),abs_of_nonpos (sub_nonpos.mpr ht.2),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · have ht : b ≤ T ∧ T ≤ a := by
      rcases Set.mem_uIcc.mp hT with ht | ht <;> constructor <;> linarith
    rw [abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_nonneg (sub_nonneg.mpr ht.1),
      abs_of_nonneg (sub_nonneg.mpr hab)]
    ring

/-- A visit admits an exact-length prefix and suffix, not just an unrelated
path to the same column. -/
lemma trace_split {i j : Fin n} (p : M.Path J i j) {a b : ℝ} {z : Fin n × ℝ}
    (hz : z ∈ p.trace a b) : ∃ (q : M.Path J i z.1) (r : M.Path J z.1 j),
      q.length a z.2 + r.length z.2 b = p.length a b := by
  induction p generalizing a with
  | nil i =>
    obtain ⟨hz,hT⟩ := hz
    subst i
    exact ⟨.nil _,.nil _,abs_split hT⟩
  | @cons i v j H hH hs p ih =>
    rcases hz with hz | hz
    · obtain ⟨hz,hT⟩ := hz
      subst i
      exact ⟨.nil _,.cons H hH hs p,by dsimp only [length]; linarith [abs_split hT]⟩
    · obtain ⟨q,r,hqr⟩ := ih hz
      refine ⟨.cons H hH hs q,r,?_⟩
      dsimp only [length]
      linarith

end Path

namespace Field

variable {M} {J : Set ℝ} {L : NNReal}

lemma vertical_intermediate (F : M.Field J L) (hJ : Set.OrdConnected J) (i : Fin n)
    (a b : J) {c : ℝ} (ha : F.value i a ≤ c) (hb : c ≤ F.value i b) :
    ∃ T ∈ Set.uIcc a.val b.val, ∃ hT : T ∈ J, F.value i ⟨T,hT⟩ = c := by
  let K := Set.uIcc a.val b.val
  let f : K → J := fun T => ⟨T.val,hJ.uIcc_subset a.property b.property T.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have : PreconnectedSpace K := Subtype.preconnectedSpace (isPreconnected_uIcc : IsPreconnected K)
  have hc := (F.vertical i).continuous.comp hf
  obtain ⟨T,hT⟩ := intermediate_value_univ
    (⟨a.val,Set.left_mem_uIcc⟩ : K) (⟨b.val,Set.right_mem_uIcc⟩ : K) hc ⟨ha,hb⟩
  exact ⟨T.val,T.property,(f T).property,hT⟩

/-- Every intermediate scalar value on a switching path is attained on its
actual trace. Switch compatibility supplies continuity across the joins. -/
lemma path_intermediate (F : M.Field J L) (hJ : Set.OrdConnected J) {i j : Fin n}
    (p : M.Path J i j) (a b : J) {c : ℝ} (ha : F.value i a ≤ c) (hb : c ≤ F.value j b) :
    ∃ (v : Fin n) (T : J), (v,T.val) ∈ p.trace a.val b.val ∧ F.value v T = c := by
  induction p generalizing a with
  | nil i =>
    obtain ⟨T,hT,hTJ,he⟩ := F.vertical_intermediate hJ i a b ha hb
    exact ⟨i,⟨T,hTJ⟩,⟨rfl,hT⟩,he⟩
  | @cons i v j H hH hs p ih =>
    by_cases hc : c ≤ F.value i ⟨H,hH⟩
    · obtain ⟨T,hT,hTJ,he⟩ := F.vertical_intermediate hJ i a ⟨H,hH⟩ ha hc
      exact ⟨i,⟨T,hTJ⟩,Or.inl ⟨rfl,hT⟩,he⟩
    · have hh : F.value v ⟨H,hH⟩ ≤ c := by
        rw [← F.switch i v ⟨H,hH⟩ hs]
        exact (lt_of_not_ge hc).le
      obtain ⟨z,T,hT,he⟩ := ih ⟨H,hH⟩ hh hb
      exact ⟨z,T,Or.inr hT,he⟩

end Field

/-- The metric component is precisely the separation quotient of the
intrinsic pseudometric on representatives. No additional edges are inserted. -/
abbrev Component (J : Set ℝ) (root : Fin n) := SeparationQuotient (M.Point J root)


end Model
end Columns

end PlanarL1

end

section

namespace PlanarL1.Columns.Model.Point
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}

/-- A Lipschitz scalar on one intrinsic component, continued constantly on the
other components, is a genuine vertical/switch-compatible field. -/
noncomputable def extendValue (f : M.Point J root → ℝ) (i : Fin n) (H : J) : ℝ := by
  classical
  exact if h : (M.activeGraph J).Reachable root i then f ⟨i,H.val,H.property,h⟩ else 0

lemma extendValue_point (f : M.Point J root → ℝ) (x : M.Point J root) :
    extendValue f x.column ⟨x.height,x.inBand⟩ = f x := by
  simp only [extendValue,dite_eq_left x.reachable]

lemma extendValue_vertical {K : ℝ≥0} (f : M.Point J root → ℝ) (hf : LipschitzWith K f)
    (i : Fin n) : LipschitzWith K (extendValue f i) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  by_cases hi : (M.activeGraph J).Reachable root i
  · simp only [extendValue,dite_eq_left hi]
    have h := hf.dist_le_mul (⟨i,a.val,a.property,hi⟩ : M.Point J root)
      (⟨i,b.val,b.property,hi⟩ : M.Point J root)
    rw [Point.dist_same_column (⟨i,a.val,a.property,hi⟩ : M.Point J root)
      (⟨i,b.val,b.property,hi⟩ : M.Point J root) rfl] at h
    simpa only [Subtype.dist_eq,Real.dist_eq] using h
  · simp only [extendValue,dite_eq_right hi,dist_self]
    positivity

lemma extendValue_switch {K : ℝ≥0} (f : M.Point J root → ℝ) (hf : LipschitzWith K f)
    (i j : Fin n) (H : J) (hs : H.val ∈ M.heights i j) :
    extendValue f i H = extendValue f j H := by
  have ha : (M.activeGraph J).Adj i j := ⟨H.val,H.property,hs⟩
  by_cases hi : (M.activeGraph J).Reachable root i
  · have hj := hi.trans ha.reachable
    simp only [extendValue,dite_eq_left hi,dite_eq_left hj]
    let x : M.Point J root := ⟨i,H.val,H.property,hi⟩
    let y : M.Point J root := ⟨j,H.val,H.property,hj⟩
    have hd : dist x y = 0 := by
      apply le_antisymm _ dist_nonneg
      simpa only [x,y,sub_self,abs_zero,add_zero] using x.dist_le_switch y H.property hs
    have h := hf.dist_le_mul x y
    rw [hd,mul_zero] at h
    exact dist_le_zero.mp h
  · have hj : ¬ (M.activeGraph J).Reachable root j := fun h => hi (h.trans ha.symm.reachable)
    simp only [extendValue,dite_eq_right hi,dite_eq_right hj]

noncomputable def extendField {K : ℝ≥0} (f : M.Point J root → ℝ) (hf : LipschitzWith K f) :
    M.Field J K where
  value := extendValue f
  vertical := extendValue_vertical f hf
  switch := extendValue_switch f hf

/-- A continuous scalar intermediate value is attained on an actual shortest
switching path, with the exact metric betweenness identity. -/
lemma intermediate_between {K : ℝ≥0} (f : M.Point J root → ℝ) (hf : LipschitzWith K f)
    (hJ : IsClosed J) (hI : Set.OrdConnected J) (x y : M.Point J root) {c : ℝ}
    (hx : f x ≤ c) (hy : c ≤ f y) :
    ∃ z : M.Point J root, f z=c ∧ dist x z+dist z y=dist x y := by
  obtain ⟨p,_,hp⟩ := x.exists_shortest hJ y
  have hx' : (extendField f hf).value x.column ⟨x.height,x.inBand⟩ ≤ c := by
    simpa only [extendField,extendValue_point] using hx
  have hy' : c ≤ (extendField f hf).value y.column ⟨y.height,y.inBand⟩ := by
    simpa only [extendField,extendValue_point] using hy
  obtain ⟨i,H,hT,hF⟩ := (extendField f hf).path_intermediate hI p
    ⟨x.height,x.inBand⟩ ⟨y.height,y.inBand⟩ hx' hy'
  obtain ⟨q,r,hqr⟩ := p.trace_split hT
  let z : M.Point J root := ⟨i,H.val,H.property,x.reachable.trans q.word.reachable⟩
  have hz : f z=c := by
    change extendValue f z.column ⟨z.height,z.inBand⟩=c at hF
    rwa [extendValue_point] at hF
  refine ⟨z,hz,le_antisymm ?_ (dist_triangle x z y)⟩
  have hq := x.distance_le z q
  have hr := z.distance_le y r
  change dist x z ≤ q.length x.height H.val at hq
  change dist z y ≤ r.length H.val y.height at hr
  rw [← hp]
  linarith

end PlanarL1.Columns.Model.Point


end

end OAI
