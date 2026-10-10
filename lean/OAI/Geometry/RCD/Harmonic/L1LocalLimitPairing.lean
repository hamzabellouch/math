import OAI.Geometry.RCD.Sobolev.L1LimitLocalization
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Compatible local L1 limits have the same supported measure pairing -/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem local_L1_limit_zero_extension {Ω : Set X} (hΩ : MeasurableSet Ω)
    (F : ℕ → X → ℝ) (hz : ∀ k x, x ∉ Ω → F k x=0)
    (J : Lp ℝ 1 (μ.restrict Ω))
    (hJ : Tendsto (fun k => ∫ x in Ω, |F k x-J x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |F k x-Ω.indicator (fun y => J y) x| ∂μ) atTop (𝓝 0) := by
  apply hJ.congr'
  refine Eventually.of_forall fun k => ?_
  change (∫ x in Ω, |F k x-J x| ∂μ) =
    ∫ x, |F k x-Ω.indicator (fun y => J y) x| ∂μ
  symm
  calc
    _ = ∫ x in Ω, |F k x-Ω.indicator (fun y => J y) x| ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [hz k x hx,indicator_of_notMem hx,sub_self,abs_zero]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hΩ] with x hx
      rw [indicator_of_mem hx]

theorem local_L1_limits_pairing_eq (ν : Measure X) (hν : ν ≪ μ)
    {Ω Λ : Set X} (hΩ : MeasurableSet Ω) (hΛ : MeasurableSet Λ)
    (F G : ℕ → X → ℝ) (hF : ∀ k, Integrable (F k) μ) (hG : ∀ k, Integrable (G k) μ)
    (hzF : ∀ k x, x ∉ Ω → F k x=0) (hzG : ∀ k x, x ∉ Λ → G k x=0)
    (I : Lp ℝ 1 (μ.restrict Ω)) (J : Lp ℝ 1 (μ.restrict Λ))
    (hI : Tendsto (fun k => ∫ x in Ω, |F k x-I x| ∂μ) atTop (𝓝 0))
    (hJ : Tendsto (fun k => ∫ x in Λ, |G k x-J x| ∂μ) atTop (𝓝 0))
    (χ : X → ℝ) (hχ : AEStronglyMeasurable χ μ) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂μ, |χ x| ≤ D)
    (heq : ∀ k, F k =ᵐ[μ] fun x => χ x*G k x)
    (hone : χ =ᵐ[ν] fun _ => 1) :
    (∫ x in Ω, I x ∂ν) = ∫ x in Λ, J x ∂ν := by
  let f := Ω.indicator (fun x => I x)
  let g := Λ.indicator (fun x => J x)
  have hf : Integrable f μ := (integrable_indicator_iff hΩ).mpr
    (memLp_one_iff_integrable.mp (Lp.memLp I))
  have hg : Integrable g μ := (integrable_indicator_iff hΛ).mpr
    (memLp_one_iff_integrable.mp (Lp.memLp J))
  have he := L1_limit_mul_eq μ F G f g hF hG hf hg
    (local_L1_limit_zero_extension μ hΩ F hzF I hI)
    (local_L1_limit_zero_extension μ hΛ G hzG J hJ) χ hχ D hD heq
  have hfg : f =ᵐ[ν] g := by
    filter_upwards [hν.ae_eq he,hone] with x hx hχx
    simpa only [hχx,one_mul] using hx
  rw [← integral_indicator hΩ,← integral_indicator hΛ]
  exact integral_congr_ae hfg

end RegularPointCoordinates

end

end OAI
