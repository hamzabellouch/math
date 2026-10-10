import OAI.Geometry.RCD.Harmonic.L1LocalLimitPairing
import OAI.Geometry.RCD.Sobolev.HessianActionRepresentatives
import OAI.Geometry.RCD.Sobolev.HessianActionIntegral

namespace OAI

/-! # The local Hessian pairing is independent of a larger cutoff -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem local_hessian_limits_pairing_eq (ν : Measure X) (hν : ν ≪ μ)
    {Ω Λ : Set X} (hΩ : MeasurableSet Ω) (hΛ : MeasurableSet Λ) (hsub : Ω ⊆ Λ)
    (w : SobolevSpace μ Q) (u v WU WV UU VV : ℕ → SobolevSpace μ Q)
    (huv : ∀ k, SobolevSpace.toLp μ Q (u k) =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q (v k))
    (hWU : ∀ k, SobolevSpace.toLp μ Q (WU k) =ᵐ[μ.restrict Ω] localGamma μ Q w (u k))
    (hWV : ∀ k, SobolevSpace.toLp μ Q (WV k) =ᵐ[μ.restrict Λ] localGamma μ Q w (v k))
    (hUU : ∀ k, SobolevSpace.toLp μ Q (UU k) =ᵐ[μ.restrict Ω] localGamma μ Q (u k) (u k))
    (hVV : ∀ k, SobolevSpace.toLp μ Q (VV k) =ᵐ[μ.restrict Λ] localGamma μ Q (v k) (v k))
    (φ ψ : X → ℝ) (hφ : AEStronglyMeasurable φ μ) (hψ : AEStronglyMeasurable ψ μ)
    (B C : ℝ≥0) (hB : ∀ᵐ x ∂μ, |φ x| ≤ B) (hC : ∀ᵐ x ∂μ, |ψ x| ≤ C)
    (hzφ : ∀ x ∉ Ω, φ x=0) (hzψ : ∀ x ∉ Λ, ψ x=0)
    (hψone : ∀ x ∈ Ω, ψ x=1) (hφone : φ =ᵐ[ν] fun _ => 1)
    (I : Lp ℝ 1 (μ.restrict Ω)) (J : Lp ℝ 1 (μ.restrict Λ))
    (hI : Tendsto (fun k => ∫ x in Ω,
      |φ x*localHessianAction μ Q w (u k) (u k) (WU k) (WU k) (UU k) x-I x| ∂μ)
      atTop (𝓝 0))
    (hJ : Tendsto (fun k => ∫ x in Λ,
      |ψ x*localHessianAction μ Q w (v k) (v k) (WV k) (WV k) (VV k) x-J x| ∂μ)
      atTop (𝓝 0)) :
    (∫ x in Ω, I x ∂ν) = ∫ x in Λ, J x ∂ν := by
  let F k x := φ x*localHessianAction μ Q w (u k) (u k) (WU k) (WU k) (UU k) x
  let G k x := ψ x*localHessianAction μ Q w (v k) (v k) (WV k) (WV k) (VV k) x
  have hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ B := by simpa only [Real.norm_eq_abs] using hB
  have hc : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C := by simpa only [Real.norm_eq_abs] using hC
  apply local_L1_limits_pairing_eq μ ν hν hΩ hΛ F G
    (fun k => (localHessianAction_integrable μ Q w (u k) (u k) (WU k) (WU k) (UU k)).bdd_mul hφ hb)
    (fun k => (localHessianAction_integrable μ Q w (v k) (v k) (WV k) (WV k) (VV k)).bdd_mul hψ hc)
    (fun k x hx => by dsimp only [F]; rw [hzφ x hx,zero_mul])
    (fun k x hx => by dsimp only [G]; rw [hzψ x hx,zero_mul])
    I J hI hJ φ hφ B hB _ hφone
  intro k
  have he := localHessianAction_congr_of_grams μ Q w (u k) (v k) (u k) (v k)
    (WU k) (WV k) (WU k) (WV k) (UU k) (VV k) (huv k) (huv k)
    (hWU k) (ae_restrict_of_ae_restrict_of_subset hsub (hWV k))
    (hWU k) (ae_restrict_of_ae_restrict_of_subset hsub (hWV k))
    (hUU k) (ae_restrict_of_ae_restrict_of_subset hsub (hVV k))
  filter_upwards [(ae_restrict_iff' hΩ).mp he] with x hx
  by_cases hm : x ∈ Ω
  · dsimp only [F,G]
    rw [hψone x hm,one_mul,hx hm]
  · dsimp only [F,G]
    rw [hzφ x hm,zero_mul,zero_mul]

end RegularPointCoordinates

end

end OAI
