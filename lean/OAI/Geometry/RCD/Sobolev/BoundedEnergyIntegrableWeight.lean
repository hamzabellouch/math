import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Vanishing bounded energies remain small under an integrable weight -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem bounded_energy_integrable_weight
    (F : ℕ → X → ℝ) (hFi : ∀ k, Integrable (F k) μ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hFb : ∀ k, ∀ᵐ x ∂μ, 0 ≤ F k x ∧ F k x ≤ C)
    (hlim : Tendsto (fun k => ∫ x, F k x ∂μ) atTop (𝓝 0))
    (w : X → ℝ) (hwi : Integrable w μ) :
    Tendsto (fun k => ∫ x, w x*F k x ∂μ) atTop (𝓝 0) := by
  have hnorm (k : ℕ) : eLpNorm (F k) 1 μ = ENNReal.ofReal (∫ x, F k x ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hFi k).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hFi k)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hFb k] with x hx
    exact Real.norm_of_nonneg hx.1
  have hnormlim : Tendsto (fun k => eLpNorm (F k) 1 μ) atTop (𝓝 0) := by
    simpa only [hnorm,ENNReal.ofReal_zero,Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  have hmeasure : TendstoInMeasure μ F atTop (fun _ => (0:ℝ)) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (μ := μ) (f := F)
      (g := (0 : X → ℝ)) (l := atTop) (p := 1) (by norm_num)
    change Tendsto (fun k => eLpNorm (F k-0) 1 μ) atTop (𝓝 0)
    simpa only [sub_zero] using hnormlim
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,_hms,hmsae⟩ := (hmeasure.comp hns).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  have hb (k : ℕ) : ∀ᵐ x ∂μ, ‖w x*F (ns (ms k)) x‖ ≤ |w x| *C := by
    filter_upwards [hFb (ns (ms k))] with x hx
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hx.1]
    exact mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
  have hl : ∀ᵐ x ∂μ, Tendsto (fun k => w x*F (ns (ms k)) x) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hmsae] with x hx
    simpa only [mul_zero,Function.comp_def] using hx.const_mul (w x)
  simpa only [integral_zero,Pi.mul_apply] using
    tendsto_integral_of_dominated_convergence (fun x => |w x| *C)
      (fun k => hwi.aestronglyMeasurable.mul (hFi (ns (ms k))).aestronglyMeasurable)
      (hwi.abs.mul_const C) hb hl

end RegularPointCoordinates

end

end OAI
