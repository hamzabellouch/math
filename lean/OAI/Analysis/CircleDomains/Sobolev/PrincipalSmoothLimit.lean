import OAI.Analysis.CircleDomains.Sobolev.PrincipalSmoothExterior
import OAI.Analysis.CircleDomains.Topology.PrincipalHomeomorphCompactness
import OAI.Analysis.CircleDomains.Sobolev.PrincipalWeakDirections
import OAI.Analysis.CircleDomains.Reflection.SmoothBeltramiDistortion

namespace OAI

/-! Construct the principal plane homeomorphism with the specified strong
L2 density. Retain the actual smooth approximants and both convergences
for the subsequent scalar transport application. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane

structure PrincipalMapLimit {g : PlaneL2} {k R : ℝ}
    (S : PrincipalSmoothApproximation g k R) where
  map : ℂ ≃ₜ ℂ
  index : ℕ → ℕ
  index_strict : StrictMono index
  forward : Tendsto (fun n => homeomorphMap (S.map (index n))) atTop
    (𝓝 (homeomorphMap map))
  inverse : Tendsto (fun n => homeomorphMap (S.map (index n)).symm) atTop
    (𝓝 (homeomorphMap map.symm))
  principal : Tendsto (fun z => map z-z) (Bornology.cobounded ℂ) (𝓝 0)
  weak : ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
    (∫ z, map z*fderiv ℝ (φ : ℂ → ℂ) z v) =
      -(∫ z, (v+principalDirectionalCorrection g v z)*φ z)

namespace PrincipalSmoothApproximation
variable {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)

lemma exists_principal_limit_data (harea : ExteriorCoefficientAreaTheorem)
    (hk : 0 ≤ k) (hk1 : k < 1) {T : ℝ} (hT : 0 < T) (hRT : R+2 ≤ T) :
    Nonempty (PrincipalMapLimit S) := by
  have hK : 0 ≤ (1+k)/(1-k) := div_nonneg (by linarith) (by linarith)
  have hdist (n : ℕ) := smooth_beltrami_two_sided_distortion (S.map n)
    (S.smooth n) (S.inverse_smooth n) (S.coefficient n) hk hk1
    (S.coefficient_bound n) (S.equation n)
  obtain ⟨hb, hdecay⟩ := S.exterior_bounds harea hT hRT
  obtain ⟨H, σ, hσ, hlim, hinverse⟩ := principal_smooth_homeomorph_subsequence S.map
    (fun n => (S.smooth n).of_le (by simp))
    (fun n => (S.inverse_smooth n).of_le (by simp)) hK hT
    (fun n => (hdist n).1) (fun n => (hdist n).2) hb
  have hp (z : ℂ) : Tendsto (fun n => S.map (σ n) z) atTop (𝓝 (H z)) :=
    (continuous_eval_const z).tendsto (homeomorphMap H) |>.comp hlim
  exact ⟨⟨H, σ, hσ, hlim, hinverse,
    principal_limit_decay hp (fun n => hdecay (σ n)),
    fun v => S.limit_weak_direction hσ hp hT hb v⟩⟩

include S in
lemma exists_principal_homeomorph_limit (harea : ExteriorCoefficientAreaTheorem)
    (hk : 0 ≤ k) (hk1 : k < 1) {T : ℝ} (hT : 0 < T) (hRT : R+2 ≤ T) :
    ∃ H : ℂ ≃ₜ ℂ,
      Tendsto (fun z => H z-z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀ (v : ℂ) (φ : SchwartzMap ℂ ℂ), HasCompactSupport (φ : ℂ → ℂ) →
        (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
          -(∫ z, (v+principalDirectionalCorrection g v z)*φ z) := by
  obtain ⟨L⟩ := S.exists_principal_limit_data harea hk hk1 hT hRT
  exact ⟨L.map, L.principal, L.weak⟩

end PrincipalSmoothApproximation
end CircleDomainRigidity

end

end OAI
