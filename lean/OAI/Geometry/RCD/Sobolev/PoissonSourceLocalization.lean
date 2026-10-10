import OAI.Geometry.RCD.Sobolev.PositiveDefectCutoff

namespace OAI

/-! # Localizing the actual distance datum and its compact-test defect -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- For the actual positive squared-distance datum, half its energy
density is the datum itself on the entire inner ball. -/
theorem positiveSquaredDistance_energy_value {p : X} {R C : ℝ} (hR : 0 ≤ R)
    (χ : GoodLaplacianCutoff μ hQ p R C)
    (heik : ∀ᵐ x ∂μ.restrict (ball p R),
      localGamma μ hQ (inwardSobolev μ hQ p R) (inwardSobolev μ hQ p R) x = 1) :
    let q := positiveSquaredDistance μ hQ hR χ
    ∀ᵐ x ∂μ.restrict (ball p R),
      (1 / 2 : ℝ) * localGamma μ hQ q q x = SobolevSpace.toLp μ hQ q x := by
  dsimp only
  filter_upwards [positiveSquaredDistance_gradient μ hQ hR χ heik,
    ae_restrict_of_ae (positiveSquaredDistance_representative μ hQ hR χ),
    ae_restrict_mem measurableSet_ball] with x hg hq hx
  rw [hg, hq, positiveSquaredDistanceValue_on_ball μ hQ χ hx]
  ring

omit [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
/-- Compact support transfers a positive defect identity to any smaller
open testing region, even when its center changes. -/
theorem positive_defect_mono {S T : Set X} (hST : S ⊆ T)
    (Q : SobolevSpace μ hQ) (σ : Measure X) (a : ℝ)
    (hsource : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (L : ℝ≥0),
      LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ T →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ Q ψ + a * (∫ x in T, v x ∂μ) = ∫ x, v x ∂σ) :
    ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (L : ℝ≥0),
      LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ S →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ Q ψ + a * (∫ x in S, v x ∂μ) = ∫ x, v x ∂σ := by
  intro ψ v L hv hc hs hψ
  have hzero (U : Set X) (hU : tsupport v ⊆ U) :
      ∀ x, x ∉ U → v x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hU (subset_tsupport v hn))
  have hiS : (∫ x in S, v x ∂μ) = ∫ x, v x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hzero S hs)
  have hiT : (∫ x in T, v x ∂μ) = ∫ x, v x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hzero T (hs.trans hST))
  rw [hiS, ← hiT]
  exact hsource ψ v L hv hc (hs.trans hST) hψ

end RegularPointCoordinates

end

end OAI
