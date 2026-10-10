import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings
import OAI.Analysis.RieszRectifiability.Kernel.TestStepApproximation
import OAI.Analysis.RieszRectifiability.Kernel.LipschitzL2Density

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal

theorem L2_ae_eq_of_compact_lipschitz_pairings {d : ℕ}
    (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (f g : Ambient d → ℝ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hpair : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) → MemLp ψ 2 ν →
      (∫ x, f x * ψ x ∂ν) = ∫ x, g x * ψ x ∂ν) : f =ᵐ[ν] g := by
  let h := fun x => f x - g x
  have hh : MemLp h 2 ν := hf.sub hg
  obtain ⟨ψ, K, B, hcomp, hLip, hbound, hψ, herror⟩ :=
    exists_bounded_lipschitz_L2_sequence ν h hh
  have hconv := L2_tendsto_of_squared_error ν ψ h hψ hh herror
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => hh.toLp h) atTop
    (𝓝 (hh.toLp h))).inner (𝕜 := ℝ) hconv
  simp only [toLp_inner_eq_integral] at hlim
  have hz : ∀ k, (∫ x, h x * ψ k x ∂ν) = 0 := by
    intro k
    rw [integral_mul_sub_eq ν f g (ψ k) hf hg (hψ k),
      hpair (ψ k) (K k) (B k) (hcomp k) (hLip k) (hbound k) (hψ k), sub_self]
  simp only [hz] at hlim
  have hsq : (∫ x, h x ^ 2 ∂ν) = 0 := by
    simpa only [pow_two] using! tendsto_nhds_unique hlim tendsto_const_nhds
  have hae : (fun x => h x ^ 2) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg (h x))
      hh.integrable_sq).mp hsq
  filter_upwards [hae] with x hx
  dsimp [h] at hx
  nlinarith [sq_nonneg (f x - g x)]

theorem L2_limit_unique_of_signed_moments {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (w : ℕ → Ambient d → ℝ) (f g : Ambient d → ℝ)
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hfirst : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) → MemLp ψ 2 ν →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, f x * ψ x ∂ν)))
    (hsecond : ∀ (ψ : Ambient d → ℝ) (K B : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith K ψ → (∀ x, |ψ x| ≤ (B : ℝ)) → MemLp ψ 2 ν →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, g x * ψ x ∂ν))) :
    f =ᵐ[ν] g := by
  apply L2_ae_eq_of_compact_lipschitz_pairings ν f g hf hg
  intro ψ K B hc hL hB hψ
  exact tendsto_nhds_unique (hfirst ψ K B hc hL hB hψ) (hsecond ψ K B hc hL hB hψ)

end

end RieszRectifiability

end OAI
