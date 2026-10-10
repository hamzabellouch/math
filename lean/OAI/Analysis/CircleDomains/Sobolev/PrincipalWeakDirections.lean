import OAI.Analysis.CircleDomains.Sobolev.PrincipalSmoothApproximation
import OAI.Analysis.CircleDomains.Topology.PrincipalHomeomorphBounds
import OAI.Geometry.Cannon.Beltrami.ContinuousMemLpRestrict

namespace OAI

/-! The strong principal density limit supplies the actual directional weak
derivatives of the locally uniform homeomorphism limit. -/
open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

 def principalDirectionalCorrection (g : PlaneL2) (v : ℂ) : PlaneL2 :=
  v • beurling g + star v • g

lemma principalDirectionalCorrection_ae (g : PlaneL2) (v : ℂ) :
    principalDirectionalCorrection g v =ᵐ[volume]
      fun z => v*beurling g z + star v*g z := by
  filter_upwards [Lp.coeFn_add (v • beurling g) (star v • g),
    Lp.coeFn_smul v (beurling g), Lp.coeFn_smul (star v) g] with z h1 h2 h3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  exact h1.trans (congrArg₂ (· + ·) h2 h3)

lemma principalDirectionalCorrection_tendsto {gₙ : ℕ → PlaneL2} {g : PlaneL2}
    (hg : Tendsto gₙ atTop (𝓝 g)) (v : ℂ) :
    Tendsto (fun n => principalDirectionalCorrection (gₙ n) v) atTop
      (𝓝 (principalDirectionalCorrection g v)) :=
  (((beurling.continuous.tendsto g).comp hg).const_smul v).add (hg.const_smul (star v))

namespace PrincipalSmoothApproximation
variable {g : PlaneL2} {k R : ℝ} (S : PrincipalSmoothApproximation g k R)

lemma directional_derivative_ae (n : ℕ) (v : ℂ) :
    (fun z => fderiv ℝ (S.map n : ℂ → ℂ) z v) =ᵐ[volume]
      fun z => v+principalDirectionalCorrection ((S.density n).toLp 2 (μ:=volume)) v z := by
  filter_upwards [principalDirectionalCorrection_ae ((S.density n).toLp 2 (μ:=volume)) v,
    (S.density n).coeFn_toLp 2 volume,
    (schwartz_smoothL2 (S.density n)).beurling.representative_ae] with z hc hd hB
  change (beurling ((S.density n).toLp 2 (μ:=volume))) z =
    smoothBeurling (S.density n) z at hB
  rw [hc, hd, hB, fderiv_wirtinger, (S.partials n z).1, (S.partials n z).2]
  ring

lemma limit_weak_direction {H : ℂ → ℂ} {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (ht : ∀ z, Tendsto (fun n => S.map (σ n) z) atTop (𝓝 (H z)))
    {T : ℝ} (hT : 0 < T)
    (hb : ∀ n z, 2*T ≤ ‖z‖ → ‖S.map n z-z‖ ≤ T) (v : ℂ) :
    ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      (∫ z, H z*fderiv ℝ (φ : ℂ → ℂ) z v) =
        -(∫ z, (v+principalDirectionalCorrection g v z)*φ z) := by
  apply smooth_limit_weak_derivative (fun n z => S.map (σ n) z) H
    (fun n => (S.smooth (σ n)).of_le (by simp)) (by positivity : 0 ≤ 5*T)
    (fun n => principal_homeomorph_displacement_bound (S.map (σ n)) hT (hb (σ n))) ht v
    (fun n => principalDirectionalCorrection ((S.density (σ n)).toLp 2 (μ:=volume)) v)
    (principalDirectionalCorrection g v) (fun n => S.directional_derivative_ae (σ n) v)
  exact (principalDirectionalCorrection_tendsto S.strong_density v).comp hσ.tendsto_atTop

end PrincipalSmoothApproximation
end CircleDomainRigidity

end

end OAI
