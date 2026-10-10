import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedTransform

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function

theorem scalarCappedRieszKernel_swap {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) :
    scalarCappedRieszKernel m e ε q.swap = -scalarCappedRieszKernel m e ε q := by
  have hcap : cappedInverseDistancePow (m + 1) ε q.swap = cappedInverseDistancePow (m + 1) ε q := by
    simp only [cappedInverseDistancePow, Prod.fst_swap, Prod.snd_swap, dist_comm q.2 q.1]
  unfold scalarCappedRieszKernel cappedRieszKernel
  rw [hcap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← neg_sub q.1 q.2, smul_neg, inner_neg_right]

theorem cappedRieszInterior_eq_scalar_cap {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedRieszInterior m ε e φ q = scalarCappedRieszKernel m e ε q * (φ q.1 - φ q.2) := by
  unfold cappedRieszInterior scalarCappedRieszKernel cappedRieszKernel
  rw [real_inner_smul_right]
  ring

theorem finite_capped_pairing_symmetrization {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (hφm : Measurable φ) (hφ : Integrable φ ν) :
    (∫ x, scalarCappedTransform m ν e ε (fun _ => 1) x * φ x ∂ν) =
      (1 / 2 : ℝ) * (∫ q, cappedRieszInterior m ε e φ q ∂ν.prod ν) := by
  let F := fun q : Ambient d × Ambient d => φ q.1 * scalarCappedRieszKernel m e ε q
  have hF : Integrable F (ν.prod ν) := by
    simpa only [mul_one] using! bounded_kernel_bilinear_integrable ν (scalarCappedRieszKernel m e ε)
      (scalarCappedRieszKernel_continuous m e ε hε).measurable (‖e‖ * (ε ^ m)⁻¹)
      (scalarCappedRieszKernel_bound m e ε hε) φ (fun _ => 1) hφm measurable_const hφ (integrable_const 1)
  have heq : cappedRieszInterior m ε e φ = fun q => F q + F q.swap := by
    funext q
    rw [cappedRieszInterior_eq_scalar_cap]
    dsimp only [F]
    rw [scalarCappedRieszKernel_swap]
    dsimp only [Prod.swap]
    ring
  have hsum : (∫ q, cappedRieszInterior m ε e φ q ∂ν.prod ν) = 2 * (∫ q, F q ∂ν.prod ν) := by
    rw [heq]
    change (∫ q, F q + (F ∘ Prod.swap) q ∂ν.prod ν) = 2 * (∫ q, F q ∂ν.prod ν)
    rw [integral_add hF hF.swap]
    simp only [Function.comp_def, integral_prod_swap]
    ring
  have hpair : (∫ q, F q ∂ν.prod ν) =
      ∫ x, scalarCappedTransform m ν e ε (fun _ => 1) x * φ x ∂ν := by
    have h := capped_bilinear_eq_scalarCappedTransform m ν e ε hε (fun _ => 1) φ
      measurable_const hφm (integrable_const 1) hφ
    simpa only [mul_one, mul_comm (φ _) (scalarCappedTransform m ν e ε (fun _ => 1) _)] using! h
  rw [hsum, hpair]
  ring

end

end RieszRectifiability

end OAI
