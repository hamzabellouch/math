import OAI.Geometry.RCD.Harmonic.QuadraticRadialError

namespace OAI

/-! # Interior radial error from the explicit cutoff comparison -/

open Set MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- A nonnegative cutoff equal to one on the inner region dominates its
actual gradient energy. -/
theorem cutoff_inner_energy_le {I Ω : Set X} (hI : MeasurableSet I) (hIΩ : I ⊆ Ω)
    (c w : SobolevSpace μ hQ) (χ : X → ℝ) (C : ℝ≥0)
    (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hbound : ∀ x, |χ x| ≤ C) (hnonneg : ∀ x, 0 ≤ χ x)
    (hone : ∀ x ∈ I, χ x = 1) :
    (∫ x in I, localGamma μ hQ w w x ∂μ) ≤
      ∫ x in Ω, SobolevSpace.toLp μ hQ c x * localGamma μ hQ w w x ∂μ := by
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ C := by
    filter_upwards [hcrep] with x hx
    rw [hx]
    exact hbound x
  have hi := (localGamma_memL1 μ hQ w w).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ c))
    (by simpa only [Real.norm_eq_abs] using hc)
  have hn : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ c x * localGamma μ hQ w w x := by
    filter_upwards [hcrep, localGamma_self μ hQ w] with x hx hself
    rw [hx, hself]
    exact mul_nonneg (hnonneg x) (sq_nonneg _)
  calc
    _ = ∫ x in I, SobolevSpace.toLp μ hQ c x * localGamma μ hQ w w x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hcrep, ae_restrict_mem hI] with x hx hxi
      rw [hx, hone x hxi, one_mul]
    _ ≤ _ := setIntegral_mono_set hi.integrableOn (ae_restrict_of_ae hn)
      (Filter.Eventually.of_forall hIΩ)

/-- Explicit interior radial error. The right side uses only the value
error, actual Gram errors and fixed coordinate/cutoff bounds. -/
theorem coordinateQuadratic_interior_radial_error {n : ℕ} {I Ω : Set X}
    (hI : MeasurableSet I) (hIΩ : I ⊆ Ω) (hfin : μ Ω ≠ ∞)
    (u : Fin n → SobolevSpace μ hQ) (C D Lχ : ℝ≥0)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (c q : SobolevSpace μ hQ) (χ : X → ℝ)
    (hχ : LipschitzWith Lχ χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ 1) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hone : ∀ x ∈ I, χ x = 1)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ D)
    {δ M L : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hsmall : ∀ᵐ x ∂μ.restrict Ω,
      |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ δ)
    (heik : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ q q x = 2 * SobolevSpace.toLp μ hQ q x)
    (hgrad : ∀ j, ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ (u j) (u j) x ≤ M ^ 2)
    (hcut : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ c c x ≤ L ^ 2)
    (j : Fin n) :
    (∫ x in I, (localGamma μ hQ q (u j) x - SobolevSpace.toLp μ hQ (u j) x) ^ 2 ∂μ) ≤
      2 * M ^ 2 * (2 * δ * (1 + (n : ℝ) * M ^ 2 + (n : ℝ) * C * M * L) * μ.real Ω +
        (C : ℝ) ^ 2 * ∫ x in Ω, ∑ i, ∑ k,
          |localGamma μ hQ (u k) (u i) x - if k = i then 1 else 0| ∂μ) +
      2 * ((n : ℝ) * (C : ℝ) ^ 2 * (M ^ 2 + 1)) *
        ∫ x in I, ∑ i, |localGamma μ hQ (u i) (u j) x - if i = j then 1 else 0| ∂μ := by
  have hIfin : μ I ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hIΩ)
  have hraw := coordinateQuadratic_raw_error μ hQ hIfin u C q hub hM
    (fun k => ae_restrict_of_ae_restrict_of_subset hIΩ (hgrad k)) j
  have henergy := cutoff_inner_energy_le μ hQ hI hIΩ c
    (q - coordinateQuadratic μ hQ u C) χ 1 hcrep hbound hnonneg hone
  have hboundE := coordinateQuadratic_uniform_value_gradient μ hQ hfin u C D Lχ hu hub
    c q χ hχ hcpt hbound hnonneg hsupp hcrep hw hδ hM hL hsmall heik hgrad hcut
  have hE := henergy.trans hboundE
  exact hraw.trans (add_le_add (mul_le_mul_of_nonneg_left hE (by positivity)) le_rfl)

end RegularPointCoordinates

end

end OAI
