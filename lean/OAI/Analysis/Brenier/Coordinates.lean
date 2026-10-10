import Mathlib

namespace OAI

/-! # Volume-preserving coordinates adapted to an arbitrary affine hyperplane -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem358.HouseholderCoordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Householder reflection sends the chosen normal to a coordinate normal. -/
def alignNormal (i : ι) (n : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  Submodule.reflection (Submodule.span ℝ {n - EuclideanSpace.single i ‖n‖})ᗮ

lemma alignNormal_normal (i : ι) (n : EuclideanSpace ℝ ι) :
    alignNormal i n n = EuclideanSpace.single i ‖n‖ := by
  apply Submodule.reflection_sub
  simp [PiLp.norm_single]

lemma inner_eq_norm_mul_coord (i : ι) (n x : EuclideanSpace ℝ ι) :
    inner ℝ x n = ‖n‖ * (alignNormal i n x) i := by
  rw [← (alignNormal i n).inner_map_map x n, alignNormal_normal]
  simp [EuclideanSpace.inner_single_right, mul_comm]

lemma alignNormal_coord (i : ι) {n : EuclideanSpace ℝ ι} (hn : n ≠ 0)
    (x : EuclideanSpace ℝ ι) :
    (alignNormal i n x) i = inner ℝ x n / ‖n‖ := by
  apply (eq_div_iff (norm_ne_zero_iff.mpr hn)).2
  rw [inner_eq_norm_mul_coord]
  ring

lemma alignNormal_measurePreserving (i : ι) (n : EuclideanSpace ℝ ι) :
    MeasurePreserving (alignNormal i n) volume volume :=
  (alignNormal i n).measurePreserving

/-- Translation after the reflection straightens an affine hyperplane. -/
def affineCoordinates (i : ι) (n : EuclideanSpace ℝ ι) (c : ℝ) :
    EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι :=
  (alignNormal i n).toHomeomorph.toMeasurableEquiv.trans
    (MeasurableEquiv.addRight (EuclideanSpace.single i (c / ‖n‖)))

lemma affineCoordinates_apply (i : ι) (n x : EuclideanSpace ℝ ι) (c : ℝ) :
    affineCoordinates i n c x = alignNormal i n x + EuclideanSpace.single i (c / ‖n‖) := rfl

lemma affineCoordinates_symm_apply (i : ι) (n y : EuclideanSpace ℝ ι) (c : ℝ) :
    (affineCoordinates i n c).symm y =
      (alignNormal i n).symm (y - EuclideanSpace.single i (c / ‖n‖)) := rfl

lemma affineCoordinates_coord (i : ι) {n : EuclideanSpace ℝ ι} (hn : n ≠ 0)
    (c : ℝ) (x : EuclideanSpace ℝ ι) :
    (affineCoordinates i n c x) i = (inner ℝ x n + c) / ‖n‖ := by
  simp [affineCoordinates_apply, alignNormal_coord i hn, add_div]

lemma affineCoordinates_measurePreserving (i : ι) (n : EuclideanSpace ℝ ι) (c : ℝ) :
    MeasurePreserving (affineCoordinates i n c) volume volume :=
  (measurePreserving_add_right volume (EuclideanSpace.single i (c / ‖n‖))).comp
    (alignNormal_measurePreserving i n)

lemma affineCoordinates_dist (i : ι) (n x y : EuclideanSpace ℝ ι) (c : ℝ) :
    dist (affineCoordinates i n c x) (affineCoordinates i n c y) = dist x y := by
  rw [affineCoordinates_apply, affineCoordinates_apply, dist_add_right]
  exact (alignNormal i n).isometry.dist_eq x y

lemma affineCoordinates_le_iff (i : ι) {n : EuclideanSpace ℝ ι} (hn : n ≠ 0)
    (c t : ℝ) (x : EuclideanSpace ℝ ι) :
    (affineCoordinates i n c x) i ≤ t ↔ inner ℝ x n + c ≤ ‖n‖ * t := by
  rw [affineCoordinates_coord i hn, div_le_iff₀ (norm_pos_iff.mpr hn), mul_comm]

lemma affineCoordinates_nonneg_iff (i : ι) {n : EuclideanSpace ℝ ι} (hn : n ≠ 0)
    (c : ℝ) (x : EuclideanSpace ℝ ι) :
    0 ≤ (affineCoordinates i n c x) i ↔ 0 ≤ inner ℝ x n + c := by
  rw [affineCoordinates_coord i hn, le_div_iff₀ (norm_pos_iff.mpr hn), zero_mul]

lemma affineCoordinates_eq_iff (i : ι) {n : EuclideanSpace ℝ ι} (hn : n ≠ 0)
    (c t : ℝ) (x : EuclideanSpace ℝ ι) :
    (affineCoordinates i n c x) i = t ↔ inner ℝ x n + c = ‖n‖ * t := by
  rw [affineCoordinates_coord i hn, div_eq_iff (norm_ne_zero_iff.mpr hn), mul_comm]

/-- No measurability hypothesis on the integrand is needed for an invertible
measure-preserving coordinate change. -/
lemma integral_affineCoordinates (i : ι) (n : EuclideanSpace ℝ ι) (c : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ ι → F) :
    (∫ x, f (affineCoordinates i n c x)) = ∫ y, f y :=
  (affineCoordinates_measurePreserving i n c).integral_comp
    (affineCoordinates i n c).measurableEmbedding f

lemma alignNormal_symm_single (i : ι) {n : EuclideanSpace ℝ ι} (hn : n ≠ 0)
    (t : ℝ) :
    (alignNormal i n).symm (EuclideanSpace.single i t) = (t / ‖n‖) • n := by
  apply (alignNormal i n).injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_smul, alignNormal_normal]
  ext k
  by_cases hki : k = i
  · subst k
    simp [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hn)]
  · simp [hki]

/-- A unit coordinate displacement in straightened coordinates is displacement
along the unit normal in the original space. -/
lemma affineCoordinates_symm_add_single (i : ι) {n : EuclideanSpace ℝ ι}
    (hn : n ≠ 0) (c t : ℝ) (y : EuclideanSpace ℝ ι) :
    (affineCoordinates i n c).symm (y + EuclideanSpace.single i t) =
      (affineCoordinates i n c).symm y + (t / ‖n‖) • n := by
  rw [affineCoordinates_symm_apply, affineCoordinates_symm_apply]
  have heq : y + EuclideanSpace.single i t - EuclideanSpace.single i (c / ‖n‖) =
      (y - EuclideanSpace.single i (c / ‖n‖)) + EuclideanSpace.single i t := by abel
  rw [heq, map_add, alignNormal_symm_single i hn]

lemma affineFunctional_symm (i : ι) {n : EuclideanSpace ℝ ι} (hn : n ≠ 0)
    (c : ℝ) (y : EuclideanSpace ℝ ι) :
    inner ℝ ((affineCoordinates i n c).symm y) n + c = ‖n‖ * y i := by
  have h := affineCoordinates_coord i hn c ((affineCoordinates i n c).symm y)
  rw [MeasurableEquiv.apply_symm_apply] at h
  have hm := (eq_div_iff (norm_ne_zero_iff.mpr hn)).mp h
  simpa only [mul_comm] using hm.symm

lemma setIntegral_affineCoordinates (i : ι) (n : EuclideanSpace ℝ ι) (c : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ ι → F) {s : Set (EuclideanSpace ℝ ι)}
    (hs : MeasurableSet s) :
    (∫ x in (affineCoordinates i n c) ⁻¹' s, f (affineCoordinates i n c x)) =
      ∫ y in s, f y :=
  ((affineCoordinates_measurePreserving i n c).restrict_preimage hs).integral_comp
    (affineCoordinates i n c).measurableEmbedding f

end Problem358.HouseholderCoordinates

end

/-! # Fubini coordinates along an arbitrary affine normal -/
noncomputable section
open MeasureTheory

namespace Problem358.HouseholderCoordinates

variable {d : ℕ}

/-- First coordinate is signed distance to the chosen affine plane; the others
parameterize its orthogonal coordinates. -/
def productCoordinates (i : Fin (d + 1)) (n : EuclideanSpace ℝ (Fin (d + 1)))
    (c : ℝ) : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵐ ℝ × (Fin d → ℝ) :=
  ((affineCoordinates i n c).trans
    (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℝ)).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i)

lemma productCoordinates_measurePreserving (i : Fin (d + 1))
    (n : EuclideanSpace ℝ (Fin (d + 1))) (c : ℝ) :
    MeasurePreserving (productCoordinates i n c) volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) i).comp
    ((PiLp.volume_preserving_ofLp (Fin (d + 1))).comp
      (affineCoordinates_measurePreserving i n c))

lemma productCoordinates_symm_apply (i : Fin (d + 1))
    (n : EuclideanSpace ℝ (Fin (d + 1))) (c t : ℝ) (z : Fin d → ℝ) :
    (productCoordinates i n c).symm (t, z) =
      (affineCoordinates i n c).symm (WithLp.toLp 2 (i.insertNth t z)) := rfl

lemma productCoordinates_symm_affineFunctional (i : Fin (d + 1))
    {n : EuclideanSpace ℝ (Fin (d + 1))} (hn : n ≠ 0)
    (c t : ℝ) (z : Fin d → ℝ) :
    inner ℝ ((productCoordinates i n c).symm (t, z)) n + c = ‖n‖ * t := by
  rw [productCoordinates_symm_apply, affineFunctional_symm i hn]
  simp

lemma productCoordinates_symm_line (i : Fin (d + 1))
    {n : EuclideanSpace ℝ (Fin (d + 1))} (hn : n ≠ 0)
    (c t : ℝ) (z : Fin d → ℝ) :
    (productCoordinates i n c).symm (t, z) =
      (productCoordinates i n c).symm (0, z) + (t / ‖n‖) • n := by
  rw [productCoordinates_symm_apply, productCoordinates_symm_apply]
  have heq : WithLp.toLp 2 (i.insertNth t z) =
      WithLp.toLp 2 (i.insertNth 0 z) + EuclideanSpace.single i t := by
    ext k
    refine Fin.succAboveCases i ?_ ?_ k
    · simp
    · intro j
      simp [Fin.succAbove_ne]
  rw [heq, affineCoordinates_symm_add_single i hn]

/-- The normal product chart, with the tangential variable first as in a
moving-halfspace disintegration. -/
def normalChart (i : Fin (d + 1)) (n : EuclideanSpace ℝ (Fin (d + 1)))
    (c : ℝ) : (Fin d → ℝ) × ℝ ≃ᵐ EuclideanSpace ℝ (Fin (d + 1)) :=
  MeasurableEquiv.prodComm.trans (productCoordinates i n c).symm

lemma normalChart_measurePreserving (i : Fin (d + 1))
    (n : EuclideanSpace ℝ (Fin (d + 1))) (c : ℝ) :
    MeasurePreserving (normalChart i n c) (volume.prod volume) volume :=
  (productCoordinates_measurePreserving i n c).symm.comp
    Measure.measurePreserving_swap

lemma normalChart_affineFunctional (i : Fin (d + 1))
    {n : EuclideanSpace ℝ (Fin (d + 1))} (hn : n ≠ 0)
    (c t : ℝ) (z : Fin d → ℝ) :
    inner ℝ (normalChart i n c (z, t)) n + c = ‖n‖ * t :=
  productCoordinates_symm_affineFunctional i hn c t z

lemma normalChart_line (i : Fin (d + 1))
    {n : EuclideanSpace ℝ (Fin (d + 1))} (hn : n ≠ 0)
    (c t : ℝ) (z : Fin d → ℝ) :
    normalChart i n c (z, t) = normalChart i n c (z, 0) + (t / ‖n‖) • n :=
  productCoordinates_symm_line i hn c t z

lemma normalChart_nonneg_iff (i : Fin (d + 1))
    {n : EuclideanSpace ℝ (Fin (d + 1))} (hn : n ≠ 0)
    (c t : ℝ) (z : Fin d → ℝ) :
    0 ≤ inner ℝ (normalChart i n c (z, t)) n + c ↔ 0 ≤ t := by
  rw [normalChart_affineFunctional i hn, mul_nonneg_iff_of_pos_left (norm_pos_iff.mpr hn)]

lemma continuous_normalChart_symm (i : Fin (d + 1))
    (n : EuclideanSpace ℝ (Fin (d + 1))) (c : ℝ) :
    Continuous (normalChart i n c).symm := by
  change Continuous (fun x : EuclideanSpace ℝ (Fin (d + 1)) =>
    ((fun j : Fin d => (alignNormal i n x + EuclideanSpace.single i (c / ‖n‖))
      (i.succAbove j)), (alignNormal i n x + EuclideanSpace.single i (c / ‖n‖)) i))
  fun_prop

/-- Compact ambient support gives a compact common tangential support for all
normal fibers, hence a finite-volume dominator for moving-face integrals. -/
lemma exists_compact_tangential_support (i : Fin (d + 1))
    (n : EuclideanSpace ℝ (Fin (d + 1))) (c : ℝ)
    {K : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hK : IsCompact K) :
    ∃ S : Set (Fin d → ℝ), IsCompact S ∧
      ∀ z t, normalChart i n c (z, t) ∈ K → z ∈ S := by
  refine ⟨(fun x => ((normalChart i n c).symm x).1) '' K,
    hK.image ((continuous_normalChart_symm i n c).fst), ?_⟩
  intro z t hzt
  exact ⟨normalChart i n c (z, t), hzt, by simp⟩

/-- Exact ambient Fubini decomposition in fixed affine-normal coordinates. -/
theorem integral_normal_fubini (i : Fin (d + 1))
    (n : EuclideanSpace ℝ (Fin (d + 1))) (c : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin (d + 1)) → F) (hf : Integrable f) :
    (∫ x, f x) = ∫ z : Fin d → ℝ, ∫ t : ℝ,
      f ((productCoordinates i n c).symm (t, z)) := by
  have hp := (productCoordinates_measurePreserving i n c).symm
  have hi : Integrable (fun p => f ((productCoordinates i n c).symm p)) :=
    (hp.integrable_comp hf.aestronglyMeasurable).2 hf
  rw [← hp.integral_comp (productCoordinates i n c).symm.measurableEmbedding f]
  exact integral_prod_symm _ hi

/-- The same formula with the straight normal lines displayed explicitly. -/
theorem integral_normal_lines (i : Fin (d + 1))
    {n : EuclideanSpace ℝ (Fin (d + 1))} (hn : n ≠ 0) (c : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin (d + 1)) → F) (hf : Integrable f) :
    (∫ x, f x) = ∫ z : Fin d → ℝ, ∫ t : ℝ,
      f ((productCoordinates i n c).symm (0, z) + (t / ‖n‖) • n) := by
  rw [integral_normal_fubini i n c f hf]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => integral_congr_ae
    (Filter.Eventually.of_forall fun t => congrArg f
      (productCoordinates_symm_line i hn c t z))

end Problem358.HouseholderCoordinates

end

end OAI
