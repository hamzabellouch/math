import OAI.Analysis.CircleDomains.Modulus.WeightedScalarTests
import OAI.Analysis.CircleDomains.Uniformization.ActualScalarJumpLimit
import OAI.Analysis.CircleDomains.Uniformization.ActualVerticalJumpLimit

namespace OAI

/-! A genuine distributional limit of the constructed scalar fillings.
The scalar and both L² derivative fields are obtained by weak compactness;
the derivative identities follow from the vanishing actual disk errors. -/
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

 theorem distributional_identities_of_filled_weak_limits
    (harea : ExteriorCoefficientAreaTheorem) (i : Fin m) (hQ : Continuous (Q i).quotient)
    (F : ∀ n, R.HoleFilling i n) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (V : Lp ℝ 2 planarSphericalArea) (G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ))
    (hv : ∀ w : Lp ℝ 2 planarSphericalArea,
      Tendsto (fun n => ∫ z, (F (σ n)).filled z * w z ∂planarSphericalArea)
        atTop (𝓝 (∫ z, V z * w z ∂planarSphericalArea)))
    (hg₁ : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
      Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z 1 * w z)
        atTop (𝓝 (∫ z, G₁ z * w z)))
    (hg₂ : ∀ w : Lp ℝ 2 (volume : Measure ℂ),
      Tendsto (fun n => ∫ z, fderiv ℝ (F (σ n)).filled z Complex.I * w z)
        atTop (𝓝 (∫ z, G₂ z * w z))) :
    ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, V z * fderiv ℝ φ z 1) = -(∫ z, G₁ z * φ z) ∧
      (∫ z, V z * fderiv ℝ φ z Complex.I) = -(∫ z, G₂ z * φ z) := by
  intro φ hφ hs
  have hφ₂ : MemLp φ 2 (volume : Measure ℂ) := hφ.continuous.memLp_of_hasCompactSupport hs
  have hc (v : ℂ) : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hV₁ := tendsto_planar_pairings_of_spherical hv
    (hc 1)
    (hs.fderiv_apply (𝕜 := ℝ) 1)
  have hV₂ := tendsto_planar_pairings_of_spherical hv
    (hc Complex.I)
    (hs.fderiv_apply (𝕜 := ℝ) Complex.I)
  exact ⟨R.horizontal_weak_limit_identity harea i hQ F hσ hφ hs hV₁
      (tendsto_pairings_with_memLp_test hg₁ hφ₂),
    R.vertical_weak_limit_identity harea i hQ F hσ hφ hs hV₂
      (tendsto_pairings_with_memLp_test hg₂ hφ₂)⟩


include R in
 theorem exists_scalar_distributional_limit (harea : ExteriorCoefficientAreaTheorem)
    (i : Fin m) (hQ : Continuous (Q i).quotient) :
    ∃ (V : Lp ℝ 2 planarSphericalArea) (G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ)),
      ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, V z * fderiv ℝ φ z 1) = -(∫ z, G₁ z * φ z) ∧
      (∫ z, V z * fderiv ℝ φ z Complex.I) = -(∫ z, G₂ z * φ z) := by
  let F : ∀ n, R.HoleFilling i n := fun n => Classical.choice (R.exists_hole_filling i n)
  obtain ⟨V, G₁, G₂, σ, hσ, _, hv, hg₁, hg₂⟩ := R.exists_filled_weak_limits i F
  exact ⟨V, G₁, G₂, R.distributional_identities_of_filled_weak_limits
    harea i hQ F hσ V G₁ G₂ hv hg₁ hg₂⟩

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
