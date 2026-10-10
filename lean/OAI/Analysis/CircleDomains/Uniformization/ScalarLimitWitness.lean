import OAI.Analysis.CircleDomains.Uniformization.ScalarDistributionalLimit
import OAI.Analysis.CircleDomains.Sobolev.ScalarWeakEnergy

namespace OAI

/-! The actual sequence and its conformal-subsequence factor are retained
alongside the scalar, its weak derivatives and the sharp energy bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

structure ScalarWeakLimit (i : Fin m) where
  fillings : ∀ n, R.HoleFilling i n
  subsequence : ℕ → ℕ
  strict : StrictMono subsequence
  factor : ∃ τ : ℕ → ℕ, StrictMono τ ∧ subsequence = R.limit.subsequence ∘ τ
  scalar : Lp ℝ 2 planarSphericalArea
  horizontal : Lp ℝ 2 (volume : Measure ℂ)
  vertical : Lp ℝ 2 (volume : Measure ℂ)
  scalar_weak : ∀ w : Lp ℝ 2 planarSphericalArea,
    Tendsto (fun n => ∫ z, (fillings (subsequence n)).filled z * w z ∂planarSphericalArea)
      atTop (𝓝 (∫ z, scalar z * w z ∂planarSphericalArea))
  horizontal_weak : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
    Tendsto (fun n => ∫ z, fderiv ℝ (fillings (subsequence n)).filled z 1 * w z)
      atTop (𝓝 (∫ z, horizontal z * w z))
  vertical_weak : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
    Tendsto (fun n => ∫ z, fderiv ℝ (fillings (subsequence n)).filled z Complex.I * w z)
      atTop (𝓝 (∫ z, vertical z * w z))
  derivative : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    (∫ z, scalar z * fderiv ℝ φ z 1) = -(∫ z, horizontal z * φ z) ∧
    (∫ z, scalar z * fderiv ℝ φ z Complex.I) = -(∫ z, vertical z * φ z)
  energy : (∫ z, horizontal z ^ 2 + vertical z ^ 2) ≤
    ∫ x in realChartDomain d.physicalDomain,
      gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x

 theorem exists_scalar_weak_limit (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) : Nonempty (R.ScalarWeakLimit i) := by
  let F : ∀ n, R.HoleFilling i n := fun n => Classical.choice (R.exists_hole_filling i n)
  obtain ⟨V, G₁, G₂, σ, hσ, hfactor, hv, hg₁, hg₂⟩ := R.exists_filled_weak_limits i F
  exact ⟨⟨F, σ, hσ, hfactor, V, G₁, G₂, hv, hg₁, hg₂,
    R.distributional_identities_of_filled_weak_limits harea i hQ F hσ V G₁ G₂ hv hg₁ hg₂,
    R.filled_weak_energy_le i F hσ G₁ G₂ hg₁ hg₂⟩⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
