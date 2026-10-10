import OAI.Geometry.RCD.Sobolev.QuadraticGradientComparison

namespace OAI

/-! # Local form of the distance-model energy identity -/

open Set MeasureTheory
open scoped NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
private theorem cutoff_integral_local {Ω : Set X} (c : SobolevSpace μ hQ)
    (χ f : X → ℝ) (hsupp : tsupport χ ⊆ Ω)
    (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ) :
    (∫ x in Ω, SobolevSpace.toLp μ hQ c x * f x ∂μ) =
      ∫ x, SobolevSpace.toLp μ hQ c x * f x ∂μ := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hcrep] with x hx hn
  have hz : χ x = 0 := by
    by_contra h
    exact hn (hsupp (subset_tsupport χ h))
  rw [hx, hz, zero_mul]

private theorem cutoff_gradient_integral_local {Ω : Set X} (c H : SobolevSpace μ hQ)
    (χ f : X → ℝ) (hsupp : tsupport χ ⊆ Ω)
    (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ) :
    (∫ x in Ω, f x * localGamma μ hQ c H x ∂μ) =
      ∫ x, f x * localGamma μ hQ c H x ∂μ := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hcrep, localGamma_zero_on_level μ hQ c H 0] with x hx hlevel hn
  have hz : χ x = 0 := by
    by_contra h
    exact hn (hsupp (subset_tsupport χ h))
  rw [hlevel (hx.trans hz), mul_zero]

/-- All terms in the cutoff identity are supported in the same working
region. In particular the value error only needs to be small there. -/
theorem coordinateQuadratic_local_difference_energy {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (C D E L : ℝ≥0)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (c q : SobolevSpace μ hQ) (χ : X → ℝ)
    (hχ : LipschitzWith L χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ E) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ D) :
    let H := coordinateQuadratic μ hQ u C
    let w := q - H
    (∫ x in Ω, SobolevSpace.toLp μ hQ c x * localGamma μ hQ w w x ∂μ) =
      ∫ x in Ω, SobolevSpace.toLp μ hQ c x *
        (localGamma μ hQ q q x - localGamma μ hQ H H x) +
        2 * (SobolevSpace.toLp μ hQ c x * SobolevSpace.toLp μ hQ w x *
          (∑ j, localGamma μ hQ (u j) (u j) x)) +
        2 * (SobolevSpace.toLp μ hQ w x * localGamma μ hQ c H x) ∂μ := by
  dsimp only
  let H := coordinateQuadratic μ hQ u C
  let w := q - H
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ E := by
    filter_upwards [hcrep] with x hx
    rw [hx]
    exact hbound x
  have hcw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x * SobolevSpace.toLp μ hQ w x| ≤
      (E : ℝ) * D := by
    filter_upwards [hc, hw] with x hx hy
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) E.coe_nonneg
  have hiq := (localGamma_memL1 μ hQ q q).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ c))
    (by simpa only [Real.norm_eq_abs] using hc)
  have hiH := (localGamma_memL1 μ hQ H H).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ c))
    (by simpa only [Real.norm_eq_abs] using hc)
  have hit := (integrable_finsetSum Finset.univ (fun j _ => localGamma_memL1 μ hQ (u j) (u j))).bdd_mul
    ((Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ c)).mul
      (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w)))
    (by simpa only [Real.norm_eq_abs, Pi.mul_apply] using hcw)
  have hic := (localGamma_memL1 μ hQ c H).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w))
    (by simpa only [Real.norm_eq_abs] using hw)
  have hid := coordinateQuadratic_difference_energy μ hQ u C D E L hu hub
    c q χ hχ hcpt hbound hnonneg hsupp hcrep hw
  dsimp only at hid
  have hp := SobolevSpace.product_coe μ hQ c w E D hc hw
  have hprod : (∫ x, SobolevSpace.toLp μ hQ
      (SobolevSpace.product μ hQ c w E D) x * (∑ j, localGamma μ hQ (u j) (u j) x) ∂μ) =
      ∫ x, SobolevSpace.toLp μ hQ c x *
        (SobolevSpace.toLp μ hQ w x * (∑ j, localGamma μ hQ (u j) (u j) x)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    rw [hx, mul_assoc]
  rw [hprod] at hid
  rw [cutoff_integral_local μ hQ c χ _ hsupp hcrep]
  simp_rw [mul_sub]
  have hsum := integral_add (μ := μ.restrict Ω) ((hiq.integrableOn.sub hiH.integrableOn).add
      (hit.integrableOn.const_mul 2)) (hic.integrableOn.const_mul 2)
  have hsum' := integral_add (μ := μ.restrict Ω) (hiq.integrableOn.sub hiH.integrableOn) (hit.integrableOn.const_mul 2)
  have hdiff := integral_sub (μ := μ.restrict Ω) hiq.integrableOn hiH.integrableOn
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at hsum hsum' hdiff
  rw [hsum, hsum', hdiff, integral_const_mul, integral_const_mul]
  rw [cutoff_integral_local μ hQ c χ _ hsupp hcrep,
    cutoff_integral_local μ hQ c χ _ hsupp hcrep,
    integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_assoc _ _ _)),
    cutoff_integral_local μ hQ c χ _ hsupp hcrep,
    cutoff_gradient_integral_local μ hQ c H χ _ hsupp hcrep]
  exact hid

end RegularPointCoordinates

end

end OAI
