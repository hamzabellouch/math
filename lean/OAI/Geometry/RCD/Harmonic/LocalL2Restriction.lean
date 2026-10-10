import OAI.Geometry.RCD.Harmonic.LocalAffineMoments

namespace OAI

/-! # Restricting actual local L² functions between the fitting balls -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)

/-- Restriction to a smaller measurable region as a continuous linear map. -/
def localL2Restriction (s t : Set X) (hts : t ⊆ s) :
    Lp ℝ 2 (μ.restrict s) →L[ℝ] Lp ℝ 2 (μ.restrict t) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by norm_num)
    (by simpa only [one_smul] using Measure.restrict_mono_set μ hts)

omit [MetricSpace X] in
theorem localL2Restriction_coe (s t : Set X) (hts : t ⊆ s)
    (f : Lp ℝ 2 (μ.restrict s)) :
    localL2Restriction μ s t hts f =ᵐ[μ.restrict t] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by norm_num) _ f

omit [MetricSpace X] in
theorem localL2Restriction_norm_le (s t : Set X) (hts : t ⊆ s)
    (f : Lp ℝ 2 (μ.restrict s)) :
    ‖localL2Restriction μ s t hts f‖ ≤ ‖f‖ := by
  have hR : ‖localL2Restriction μ s t hts‖ ≤ 1 := by
    simpa only [localL2Restriction, ENNReal.toReal_one, Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := (2 : ℝ≥0∞)) (c := 1)
        (by norm_num) (by simpa only [one_smul] using Measure.restrict_mono_set μ hts)
  exact ((localL2Restriction μ s t hts).le_opNorm f).trans
    (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hR (norm_nonneg f)))

theorem localL2Restriction_sobolev (hQ : QuadraticCheegerEnergy μ)
    (s t : Set X) (hts : t ⊆ s) (w : SobolevSpace μ hQ) :
    localL2Restriction μ s t hts (SobolevSpace.restrictLp μ hQ s w) =
      SobolevSpace.restrictLp μ hQ t w := by
  apply Lp.ext
  exact ((localL2Restriction_coe μ s t hts _).trans
    (ae_restrict_of_ae_restrict_of_subset hts (SobolevSpace.restrictLp_coe μ hQ s w))).trans
      (SobolevSpace.restrictLp_coe μ hQ t w).symm

omit [MetricSpace X] in
theorem restrictedOne_coe (s : Set X) (hs : μ s ≠ ∞) :
    restrictedOne μ s hs =ᵐ[μ.restrict s] fun _ => (1 : ℝ) := by
  simpa only [restrictedOne, indicator_univ] using
    (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ.restrict s)
      (hs := MeasurableSet.univ) (hμs := by simpa only [Measure.restrict_apply_univ] using hs)
      (c := (1 : ℝ)))

omit [MetricSpace X] in
theorem localL2Restriction_one (s t : Set X) (hts : t ⊆ s)
    (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) :
    localL2Restriction μ s t hts (restrictedOne μ s hs) = restrictedOne μ t ht := by
  apply Lp.ext
  exact ((localL2Restriction_coe μ s t hts _).trans
    (ae_restrict_of_ae_restrict_of_subset hts (restrictedOne_coe μ s hs))).trans
      (restrictedOne_coe μ t ht).symm

theorem localL2Restriction_affine (hQ : QuadraticCheegerEnergy μ) {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (s t : Set X) (hts : t ⊆ s)
    (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) (c : ℝ) (v : Euclidean n) :
    localL2Restriction μ s t hts (affineCoordinateMap μ hQ u s hs (c, v)) =
      affineCoordinateMap μ hQ u t ht (c, v) := by
  rw [affineCoordinateMap_apply, map_add, map_smul, localL2Restriction_one,
    localL2Restriction_sobolev, affineCoordinateMap_apply]

omit [MetricSpace X] in
/-- The only norm loss under normalized restriction is the square root of
the volume ratio, written as a ratio of the actual constant-function norms. -/
theorem normalized_localL2Restriction_le (s t : Set X) (hts : t ⊆ s)
    (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) (hs0 : μ s ≠ 0) (ht0 : μ t ≠ 0)
    (f : Lp ℝ 2 (μ.restrict s)) :
    ‖normalizeLocalL2 μ t ht (localL2Restriction μ s t hts f)‖ ≤
      (Real.sqrt (μ.real s) / Real.sqrt (μ.real t)) * ‖normalizeLocalL2 μ s hs f‖ := by
  have hspos : 0 < μ.real s := ENNReal.toReal_pos hs0 hs
  have htpos : 0 < μ.real t := ENNReal.toReal_pos ht0 ht
  simp only [normalizeLocalL2, norm_smul, Real.norm_eq_abs, abs_inv,
    restrictedOne_norm, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    (Real.sqrt (μ.real t))⁻¹ * ‖localL2Restriction μ s t hts f‖ ≤
        (Real.sqrt (μ.real t))⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_left (localL2Restriction_norm_le μ s t hts f) (by positivity)
    _ = (Real.sqrt (μ.real s) / Real.sqrt (μ.real t)) *
        ((Real.sqrt (μ.real s))⁻¹ * ‖f‖) := by
      field_simp [ne_of_gt (Real.sqrt_pos.2 hspos), ne_of_gt (Real.sqrt_pos.2 htpos)]

end RegularPointCoordinates

end

end OAI
