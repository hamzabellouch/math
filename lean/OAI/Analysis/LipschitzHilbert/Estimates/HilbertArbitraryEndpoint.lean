import OAI.Analysis.LipschitzHilbert.Estimates.HilbertSharpPairing
import OAI.Analysis.LipschitzHilbert.Estimates.TimeEndpointComparison

namespace OAI

/-! The finite Hilbert decomposition applies to every positive inner
truncation, with a nearby dyadic endpoint and a uniform error. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertTimeKernel_arbitrary_endpoint :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R →
      ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon ∧
        Integrable (fun t => sharpTimeKernel epsilon R t-
          finiteTimeKernel hilbertTimeKernel N (R/2) t) ∧
        (∫ t, ‖sharpTimeKernel epsilon R t-
          finiteTimeKernel hilbertTimeKernel N (R/2) t‖)≤B := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_sharp_integral
  refine ⟨3*Real.pi+B,by positivity,?_⟩
  intro epsilon R he heR
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi⟩ := exists_dyadic_time_endpoint epsilon R he heR
  refine ⟨N,hlo,hhi,?_⟩
  have hc := sharpTimeKernel_close_lower_integral epsilon (R/(2:ℝ)^N) R he hlo hhi.le
  have hk := hkernel N (R/2) (by positivity)
  rw [show 2*(R/2)=R by ring] at hk
  let A := fun t => sharpTimeKernel epsilon R t-sharpTimeKernel (R/(2:ℝ)^N) R t
  let C := fun t => sharpTimeKernel (R/(2:ℝ)^N) R t-
    finiteTimeKernel hilbertTimeKernel N (R/2) t
  have hi : Integrable (fun t => sharpTimeKernel epsilon R t-
      finiteTimeKernel hilbertTimeKernel N (R/2) t) := by
    apply (hc.1.add hk.1).congr
    filter_upwards [] with t
    dsimp
    ring
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t, ‖A t‖+‖C t‖ := by
      apply integral_mono hi.norm (hc.1.norm.add hk.1.norm)
      intro t
      have heq : sharpTimeKernel epsilon R t-finiteTimeKernel hilbertTimeKernel N (R/2) t=
          A t+C t := by dsimp [A,C]; ring
      change ‖sharpTimeKernel epsilon R t-finiteTimeKernel hilbertTimeKernel N (R/2) t‖≤
        ‖A t‖+‖C t‖
      rw [heq]
      exact norm_add_le _ _
    _ = (∫ t, ‖A t‖)+(∫ t, ‖C t‖) := integral_add hc.1.norm hk.1.norm
    _ ≤ 3*Real.pi+B := add_le_add hc.2 hk.2

theorem hilbertArbitraryEndpoint_pairing :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon R : ℝ, 0<epsilon → epsilon≤R →
      ∃ N : ℕ, epsilon≤R/(2:ℝ)^N ∧ R/(2:ℝ)^N<2*epsilon ∧
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 →
        (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖(∫ z, slopeKernelOperator (sharpTimeKernel epsilon R) u f z*star (g z) ∂planeMeasure)-
        (∫ z, slopeKernelOperator (finiteTimeKernel hilbertTimeKernel N (R/2))
          u f z*star (g z) ∂planeMeasure)‖≤
        B*min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hkernel⟩ := hilbertTimeKernel_arbitrary_endpoint
  refine ⟨B,hB,?_⟩
  intro epsilon R he heR
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,hlo,hhi,herror,hbound⟩ := hkernel epsilon R he heR
  refine ⟨N,hlo,hhi,?_⟩
  intro u hu f g hf1 hg1 l r hwidth hfstrip hgstrip
  have hJ := finiteTimeKernel_integrable hilbertTimeKernel N (R/2) (by positivity)
  have hK : Integrable (sharpTimeKernel epsilon R) := by
    apply (herror.add hJ).congr
    filter_upwards [] with t
    simp only [Pi.add_apply,sub_add_cancel]
  have h := kernelDifference_pairing (sharpTimeKernel epsilon R)
    (finiteTimeKernel hilbertTimeKernel N (R/2)) (sharpTimeKernel_measurable _ _)
    (finiteTimeKernel_measurable _ _ _) hK hJ u hu f g hf1 hg1 l r hwidth hfstrip hgstrip
  exact h.trans ((mul_le_mul_of_nonneg_left hbound
    (le_min (by positivity) (integral_nonneg fun _ => norm_nonneg _))).trans_eq (mul_comm _ _))

end LipschitzHilbert.PacketRepresentation

end

end OAI
