import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel
import OAI.Analysis.RieszRectifiability.Kernel.FarTestKernelBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Set

theorem far_kernel_add_translation {d : ℕ} (m : ℕ) (g : Ambient d → ℂ)
    (x : Ambient d) (R : ℝ) :
    (IntegrableOn (fun h => inverseDistancePow (m + 1) 0 h • g (x + h)) (closedExterior 0 R) ↔
      IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)) ∧
    (∫ h in closedExterior 0 R, inverseDistancePow (m + 1) 0 h • g (x + h)) =
      ∫ y in closedExterior x R, inverseDistancePow (m + 1) x y • g y := by
  have hp := measurePreserving_add_left (volume : Measure (Ambient d)) x
  have he := (MeasurableEquiv.addLeft x).measurableEmbedding
  have hs : (fun h => x + h) ⁻¹' closedExterior x R = closedExterior 0 R := by
    ext h
    simp [closedExterior, dist_eq_norm]
  have hk : ∀ h : Ambient d, inverseDistancePow (m + 1) x (x + h) = inverseDistancePow (m + 1) 0 h := by
    intro h
    simp [inverseDistancePow, dist_eq_norm]
  constructor
  · simpa only [hs, Function.comp_def, hk] using! hp.integrableOn_comp_preimage he
      (f := fun y => inverseDistancePow (m + 1) x y • g y) (s := closedExterior x R)
  · simpa only [hs, hk] using! hp.setIntegral_preimage_emb he
      (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)

theorem far_kernel_sub_translation {d : ℕ} (m : ℕ) (g : Ambient d → ℂ)
    (x : Ambient d) (R : ℝ) :
    (IntegrableOn (fun h => inverseDistancePow (m + 1) 0 h • g (x - h)) (closedExterior 0 R) ↔
      IntegrableOn (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)) ∧
    (∫ h in closedExterior 0 R, inverseDistancePow (m + 1) 0 h • g (x - h)) =
      ∫ y in closedExterior x R, inverseDistancePow (m + 1) x y • g y := by
  have hp := (volume : Measure (Ambient d)).measurePreserving_sub_left x
  have he := (MeasurableEquiv.subLeft x).measurableEmbedding
  have hs : (fun h => x - h) ⁻¹' closedExterior x R = closedExterior 0 R := by
    ext h
    simp [closedExterior, dist_eq_norm]
  have hk : ∀ h : Ambient d, inverseDistancePow (m + 1) x (x - h) = inverseDistancePow (m + 1) 0 h := by
    intro h
    simp [inverseDistancePow, dist_eq_norm]
  constructor
  · simpa only [hs, Function.comp_def, hk] using! hp.integrableOn_comp_preimage he
      (f := fun y => inverseDistancePow (m + 1) x y • g y) (s := closedExterior x R)
  · simpa only [hs, hk] using! hp.setIntegral_preimage_emb he
      (fun y => inverseDistancePow (m + 1) x y • g y) (closedExterior x R)

theorem fractionalSchwartz_far_integral_identity (p : ℕ) (g : 𝓢(Ambient (p + 1), ℂ))
    (x : Ambient (p + 1)) (R : ℝ) (hR : 0 < R) :
    (-1 / 2 : ℝ) • (∫ h in closedExterior 0 R, fractionalSchwartzKernel (p + 1) g x h) =
      (∫ h in closedExterior (0 : Ambient (p + 1)) R, inverseDistancePow (p + 1 + 1) 0 h) • g x -
        ∫ y in closedExterior x R, inverseDistancePow (p + 1 + 1) x y • g y := by
  obtain ⟨hplus, heqplus⟩ := far_kernel_add_translation (p + 1) g x R
  obtain ⟨hminus, heqminus⟩ := far_kernel_sub_translation (p + 1) g x R
  have hr := raw_far_test_kernel_integrable volume g g.integrable (p + 1) x R hR
  have hp := hplus.mpr hr
  have hm := hminus.mpr hr
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound (d := p + 1) (p + 1) _ volume
    (volume_global_upper_growth (p + 1)) 0 R hR).1
  have hc := hk.smul_const (g x)
  have heq : fractionalSchwartzKernel (p + 1) g x = fun h =>
      (inverseDistancePow (p + 1 + 1) 0 h • g (x + h) +
        inverseDistancePow (p + 1 + 1) 0 h • g (x - h)) -
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x) := by
    funext h
    change inverseDistancePow (p + 1 + 1) 0 h •
      (g (x + h) + g (x - h) - (2 : ℝ) • g x) = _
    exact (smul_sub (inverseDistancePow (p + 1 + 1) 0 h)
      (g (x + h) + g (x - h)) ((2 : ℝ) • g x)).trans
      (congrArg₂ (fun a b : ℂ => a - b)
        (smul_add (inverseDistancePow (p + 1 + 1) 0 h) (g (x + h)) (g (x - h)))
        (smul_comm (inverseDistancePow (p + 1 + 1) 0 h) (2 : ℝ) (g x)))
  have hpm : IntegrableOn (fun h => inverseDistancePow (p + 1 + 1) 0 h • g (x + h) +
      inverseDistancePow (p + 1 + 1) 0 h • g (x - h)) (closedExterior 0 R) := hp.add hm
  have hcc : IntegrableOn (fun h : Ambient (p + 1) =>
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x))
      (closedExterior 0 R) := hc.smul (2 : ℝ)
  have hci : (∫ h in closedExterior (0 : Ambient (p + 1)) R,
      (2 : ℝ) • (inverseDistancePow (p + 1 + 1) 0 h • g x)) =
      (2 : ℝ) • ((∫ h in closedExterior (0 : Ambient (p + 1)) R,
        inverseDistancePow (p + 1 + 1) 0 h) • g x) := by
    calc
      _ = (2 : ℝ) • (∫ h in closedExterior (0 : Ambient (p + 1)) R,
          inverseDistancePow (p + 1 + 1) 0 h • g x) := integral_smul (2 : ℝ) _
      _ = _ := congrArg (fun z : ℂ => (2 : ℝ) • z)
        (integral_smul_const (inverseDistancePow (p + 1 + 1) (0 : Ambient (p + 1))) (g x))
  rw [heq, integral_sub hpm hcc, integral_add hp hm, hci, heqplus, heqminus]
  norm_num [RCLike.real_smul_eq_coe_mul]
  ring

end

end RieszRectifiability

end OAI
