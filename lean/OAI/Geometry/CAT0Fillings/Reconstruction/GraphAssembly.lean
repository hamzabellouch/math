import Mathlib
import OAI.Geometry.CAT0Fillings.Calculus.LipschitzFTC
import OAI.Geometry.CAT0Fillings.Reconstruction.Slices
import OAI.Geometry.CAT0Fillings.Reconstruction.AtomGraphs

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelRestriction BorelCoefficients

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedLip_of_lipschitz_compact {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : BoundedLip f := by
  refine ⟨⟨K, hf⟩, ?_⟩
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuous.continuousOn
  exact ⟨M, fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩

noncomputable def outerCutoff (p : X) (r : ℝ) (x : X) : ℝ :=
  min 1 (max 0 ((dist x p - r) / r))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma outerCutoff_lipschitz (p : X) (r : ℝ) :
    LipschitzWith (Real.nnabs (1 / r)) (outerCutoff p r) := by
  have h' : LipschitzWith (Real.nnabs (1/r)) (fun x : X => (dist x p-r)/r) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((dist x p-r)/r) ((dist y p-r)/r) ≤ |1/r| * dist x y
    calc
      _ = |1/r| * |dist x p - dist y p| := by
        rw [Real.dist_eq, show (dist x p-r)/r - (dist y p-r)/r =
          (1/r)*(dist x p-dist y p) by ring, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y p) (abs_nonneg _)
  exact (h'.const_max 0).const_min 1

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma outerCutoff_eq_one (p : X) {r : ℝ} (hr : 0 < r) {x : X}
    (hx : 2*r ≤ dist x p) : outerCutoff p r x = 1 := by
  have h : 1 ≤ (dist x p - r) / r := (le_div_iff₀ hr).mpr (by linarith)
  simp only [outerCutoff, min_eq_left (h.trans (le_max_right _ _))]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma outerCutoff_support (p : X) {r : ℝ} (hr : 0 < r) :
    Function.support (outerCutoff p r) ⊆ {x | r < dist x p} := by
  intro x hx
  by_contra h
  have hd : dist x p ≤ r := le_of_not_gt h
  have hv : (dist x p - r) / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hd) hr.le
  exact hx (by simp only [outerCutoff, max_eq_left hv, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)])

lemma restrict_zero_separated {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E)
    {p : X} {r : ℝ} (hr : 0 < r) (hEr : ∀ x ∈ E, 2*r ≤ dist x p)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    (hb : ∀ x, r ≤ dist x p → b x = 0) :
    restrictCurrent hT E b π = 0 := by
  rw [restrictCurrent_apply hT E hab]
  have he : E.indicator b = (0 : X → ℝ) := by
    funext x
    by_cases hx : x ∈ E
    · simp [hx, hb x (by linarith [hEr x hx])]
    · simp [hx]
  rw [borelAction_of_integrable _ hT
    ((integrable_boundedLip _ hab.1).indicator hE) π hab.2]
  simp [he]

lemma boundary_restrict_zero_separated {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E)
    {p : X} {r : ℝ} (hr : 0 < r) (hEr : ∀ x ∈ E, 2*r ≤ dist x p)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    (hb : ∀ x, r ≤ dist x p → b x = 0) :
    boundarySucc (restrictCurrent hT E) b π = 0 := by
  have hπ : ∀ i, ∃ K, LipschitzWith K (Matrix.vecCons b π i) :=
    fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i
  rw [boundarySucc, ite_eq_left hab, restrictCurrent_apply hT E ⟨BoundedLip.const 1, hπ⟩]
  have he : E.indicator (fun _ : X => (1 : ℝ)) =
      (fun x => E.indicator (fun _ : X => (1 : ℝ)) x * outerCutoff p r x) := by
    funext x
    by_cases hx : x ∈ E
    · simp only [indicator_of_mem hx, one_mul, outerCutoff_eq_one p hr (hEr x hx)]
    · simp only [indicator_of_notMem hx, zero_mul]
  rw [he]
  apply borelAction_locality_mul _ hT (currentMassMeasure_controls hT)
    ((integrable_const (1 : ℝ)).indicator hE)
    (boundedLip_of_lipschitz_compact (outerCutoff_lipschitz p r)) _ hπ
  refine ⟨0, {x | r < dist x p}, 0,
    isOpen_lt continuous_const (continuous_id.dist continuous_const),
    outerCutoff_support p hr, ?_⟩
  intro x hx
  exact hb x hx.le

lemma superlevelSlice_zero_separated {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    {p : X} {r : ℝ} (hr : 0 < r)
    (hside : (∀ x, t < u x → 2*r ≤ dist x p) ∨
      (∀ x, u x ≤ t → 2*r ≤ dist x p))
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    (hb : ∀ x, r ≤ dist x p → b x = 0) :
    superlevelSlice hT hB u t b π = 0 := by
  have hE : MeasurableSet {x | t < u x} :=
    measurableSet_lt measurable_const hu.measurable
  rcases hside with hside | hside
  · change restrictCurrent hB _ b π - boundarySucc (restrictCurrent hT _) b π = 0
    rw [restrict_zero_separated hB hE hr hside hab hb,
      boundary_restrict_zero_separated hT hE hr hside hab hb, sub_self]
  · have hside' : ∀ x ∈ {x | t < u x}ᶜ, 2*r ≤ dist x p := by
      intro x hx
      exact hside x (le_of_not_gt hx)
    have hCB := restrictCurrent_complement_sum hB hE b π
    rw [restrict_zero_separated hB hE.compl hr hside' hab hb, add_zero] at hCB
    have hCT := restrictCurrent_complement_sum hT hE (fun _ => 1) (Matrix.vecCons b π)
    have hπ : Admissible (fun _ : X => (1 : ℝ)) (Matrix.vecCons b π) :=
      ⟨BoundedLip.const 1, fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩
    have hcz := boundary_restrict_zero_separated hT hE.compl hr hside' hab hb
    rw [boundarySucc, ite_eq_left hab] at hcz
    rw [hcz, add_zero] at hCT
    change restrictCurrent hB _ b π - boundarySucc (restrictCurrent hT _) b π = 0
    rw [hCB]
    simp only [boundarySucc, ite_eq_left hab]
    rw [hCT, sub_self]

end CAT0Fillings.Slicing

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelRestriction BorelCoefficients SliceReconstruction

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma unitRepresentation_atoms_on_level {T : Functional X 1}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    {m : ℕ} {a : Fin m → ℤ} {x : Fin m → X}
    (ha : ∀ i, a i ≠ 0) (hx : Function.Injective x)
    (hS : UnitRepresentation (superlevelSlice hT hB u t) a x) (i : Fin m) :
    u (x i) = t := by
  classical
  by_contra hne
  have hside : ∃ δ > 0, (∀ y, t < u y → δ ≤ dist y (x i)) ∨
      (∀ y, u y ≤ t → δ ≤ dist y (x i)) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
        (isOpen_lt hu continuous_const) (x i) hlt
      refine ⟨δ, hδ, Or.inl ?_⟩
      intro y hy
      apply le_of_not_gt
      intro hyd
      have : u y < t := hball (by simpa only [mem_ball] using hyd)
      exact (lt_trans hy this).false
    · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
        (isOpen_lt continuous_const hu) (x i) hgt
      refine ⟨δ, hδ, Or.inr ?_⟩
      intro y hy
      apply le_of_not_gt
      intro hyd
      have : t < u y := hball (by simpa only [mem_ball] using hyd)
      exact (not_lt_of_ge hy) this
  obtain ⟨δ, hδ, hside⟩ := hside
  have he : ∀ᶠ r : ℝ in 𝓝 0, r < 1 ∧ 2*r < δ ∧
      ∀ j : Fin m, j ≠ i → r < dist (x j) (x i) := by
    refine (eventually_lt_nhds zero_lt_one).and ?_
    have hδ' : ∀ᶠ r : ℝ in 𝓝 0, 2*r < δ := by
      filter_upwards [eventually_lt_nhds (half_pos hδ)] with r hr
      linarith
    refine hδ'.and ?_
    simp only [Filter.eventually_all]
    intro j hji
    exact eventually_lt_nhds (dist_pos.mpr (fun h => hji (hx h)))
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp he
  let r := ε/2
  have hr0 : 0 < r := half_pos hε
  have hr := hεball (show r ∈ ball (0 : ℝ) ε by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr0] using half_lt_self hε)
  let b : X → ℝ := fun y => max 0 (r - dist y (x i))
  have hb : LipschitzWith 1 b := by
    have hs : LipschitzWith 1 (fun y : X => r - dist y (x i)) := by
      simpa only [zero_add] using (LipschitzWith.const r).sub (LipschitzWith.dist_left (x i))
    exact hs.const_max 0
  have hb1 : ∀ y, |b y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (by linarith [@dist_nonneg X _ y (x i), hr.1])
  have hbfar : ∀ y, r ≤ dist y (x i) → b y = 0 := by
    intro y hy
    exact max_eq_left (sub_nonpos.mpr hy)
  have hsz : superlevelSlice hT hB u t b (fun j => Fin.elim0 j) = 0 := by
    apply superlevelSlice_zero_separated hT hB hu t hr0 _
      ⟨⟨⟨1,hb⟩,1,hb1⟩, fun j => Fin.elim0 j⟩ hbfar
    rcases hside with hside | hside
    · exact Or.inl fun y hy => hr.2.1.le.trans (hside y hy)
    · exact Or.inr fun y hy => hr.2.1.le.trans (hside y hy)
  have hsum : (∑ j, (a j : ℝ) * b (x j)) = (a i : ℝ) * r := by
    rw [Finset.sum_eq_single i]
    · simp only [b, dist_self, sub_zero, max_eq_right hr0.le]
    · intro j _ hji
      rw [hbfar _ (hr.2.2 j hji).le, mul_zero]
    · simp
  have heq := hS b hb hb1
  rw [hsz, hsum] at heq
  have hai : (a i : ℝ) ≠ 0 := by exact_mod_cast ha i
  exact (mul_ne_zero hai hr0.ne') heq.symm

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
open Slicing

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomCode_atoms_injective (c : AtomCode) (hc : c.Valid (X := X))
    (x : Fin c.size → X)
    (hx : ∀ i, dist (x i) (denseSeq X (c.centers i)) ≤ c.radius) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  have hsep := hc.2.2.2 i j hne
  have htri := dist_triangle (denseSeq X (c.centers i)) (x i) (denseSeq X (c.centers j))
  rw [dist_comm (denseSeq X (c.centers i)) (x i), hij] at htri
  have hi := hx i
  rw [hij] at hi
  linarith [hi, hx j, hc.1]

lemma selectedAtom_on_level {T : Functional X 1}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (E : Set ℝ) (c : AtomCode)
    (t : atomDomain (superlevelSlice hT hB u) E c) (i : Fin c.size) :
    u (selectedAtom (superlevelSlice hT hB u) E c t i) = t := by
  have hs := selectedAtom_spec (superlevelSlice hT hB u) E c t
  exact unitRepresentation_atoms_on_level hT hB hu t t.property.2.1.2.2.1
    (atomCode_atoms_injective c t.property.2.1 _ hs.1) hs.2 i

theorem exists_compact_bilipschitz_scalar_atom_graphs {T : Functional X 1}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    (hI : ∀ᵐ t : ℝ, IsIntegral 0 (superlevelSlice hT hB u t)) :
    ∃ (D : PieceIndex × AtomCode → Set ℝ)
      (γ : ∀ i : PieceIndex × AtomCode, D i → Fin i.2.size → X),
      (∀ i, IsCompact (D i)) ∧ (∀ᵐ t : ℝ, t ∈ ⋃ i, D i) ∧
      (∀ i j, LipschitzWith (i.1.1 : ℝ≥0) (fun t => γ i t j)) ∧
      (∀ i j, AntilipschitzWith K (fun t => γ i t j)) ∧
      (∀ i (t : D i) j, u (γ i t j) = t) ∧
      (∀ i (t : D i), UnitRepresentation (superlevelSlice hT hB u t) i.2.weights (γ i t)) ∧
      (∀ i (t : D i), Function.Injective (γ i t)) := by
  classical
  obtain ⟨E, hEc, hEae, hLip⟩ := exists_compact_slice_lipschitz_pieces hT hB hu.continuous
  let S := superlevelSlice hT hB u
  let D (i : PieceIndex × AtomCode) : Set ℝ := atomDomain S (E i.1) i.2
  let γ (i : PieceIndex × AtomCode) (t : D i) := selectedAtom S (E i.1) i.2 t
  have hL (i : PieceIndex) (b : X → ℝ) (hb : LipschitzWith 1 b) (hb1 : ∀ x, |b x| ≤ 1) :
      LipschitzOnWith (i.1 : ℝ≥0) (fun t => S t b (fun j => Fin.elim0 j)) (E i) :=
    hLip i b (fun j => Fin.elim0 j) hb hb1 (fun j => Fin.elim0 j)
  refine ⟨D, γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isCompact_atomDomain S (hEc i.1) i.2
      (fun b hb hb1 => (hL i.1 b hb hb1).continuousOn)
  · filter_upwards [hEae, hI] with t ht hIt
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    obtain ⟨c, hc⟩ := integral_mem_atomDomain S hi hIt
    exact mem_iUnion.mpr ⟨(i,c), hc⟩
  · intro i j
    exact selectedAtom_lipschitz S (E i.1) i.2 (hL i.1) j
  · intro i j
    apply AntilipschitzWith.of_le_mul_dist
    intro s t
    have hs := selectedAtom_on_level hT hB hu.continuous (E i.1) i.2 s j
    have ht := selectedAtom_on_level hT hB hu.continuous (E i.1) i.2 t j
    have h := hu.dist_le_mul (γ i s j) (γ i t j)
    rw [hs, ht] at h
    exact h
  · intro i t j
    exact selectedAtom_on_level hT hB hu.continuous (E i.1) i.2 t j
  · intro i t
    exact (selectedAtom_spec S (E i.1) i.2 t).2
  · intro i t
    exact atomCode_atoms_injective i.2 t.property.2.1 _
      (selectedAtom_spec S (E i.1) i.2 t).1

end CAT0Fillings.SliceReconstruction
end

end OAI
