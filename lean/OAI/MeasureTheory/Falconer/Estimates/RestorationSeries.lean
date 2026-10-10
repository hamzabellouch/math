import OAI.MeasureTheory.Falconer.Shells.AssemblyLosses

namespace OAI

/-! # Summability of the actual cap, class and descriptor deletion costs -/

namespace Falconer
open Filter
open scoped ENNReal Topology

noncomputable def restorationError (Cw Ccap c lam σ : ℝ) (k₁ k₂ N : ℕ) : ℝ :=
  Cw * (Ccap*((2:ℝ)^N)^(-c) + 2*((2:ℝ)^N)^(-2:ℝ) +
    ((N:ℝ)+1)^k₁*((2:ℝ)^N)^(-lam) + ((N:ℝ)+1)^k₂*((2:ℝ)^N)^(-lam) +
    4*((N:ℝ)+1)^2*((2:ℝ)^N)^(-σ))

theorem restorationError_nonneg {Cw Ccap : ℝ} (hw : 0 ≤ Cw) (hcap : 0 ≤ Ccap)
    (c lam σ : ℝ) (k₁ k₂ N : ℕ) : 0 ≤ restorationError Cw Ccap c lam σ k₁ k₂ N := by
  unfold restorationError
  positivity

theorem restorationError_summable (Cw Ccap : ℝ) {c lam σ : ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hσ : 0 < σ) (k₁ k₂ : ℕ) :
    Summable (restorationError Cw Ccap c lam σ k₁ k₂) := by
  have hcap := (summable_scale_decay hc).mul_left Ccap
  have hleaf := (summable_scale_decay (by norm_num : (0:ℝ) < 2)).mul_left 2
  have h₁ := summable_polynomial_scale_decay hlam 1 k₁
  have h₂ := summable_polynomial_scale_decay hlam 1 k₂
  have htest := summable_polynomial_scale_decay hσ 4 2
  change Summable (fun N : ℕ => Cw * (Ccap*((2:ℝ)^N)^(-c) + 2*((2:ℝ)^N)^(-2:ℝ) +
    ((N:ℝ)+1)^k₁*((2:ℝ)^N)^(-lam) + ((N:ℝ)+1)^k₂*((2:ℝ)^N)^(-lam) +
    4*((N:ℝ)+1)^2*((2:ℝ)^N)^(-σ)))
  simpa only [one_mul] using ((((hcap.add hleaf).add h₁).add h₂).add htest).mul_left Cw

theorem summable_of_restoration_error {f : ℕ → ℝ≥0∞} {Cw Ccap c lam σ : ℝ}
    (hw : 0 ≤ Cw) (hcap : 0 ≤ Ccap) (hc : 0 < c) (hlam : 0 < lam) (hσ : 0 < σ)
    (k₁ k₂ N₀ : ℕ)
    (hbound : ∀ N ≥ N₀, f N ≤ ENNReal.ofReal (restorationError Cw Ccap c lam σ k₁ k₂ N)) :
    Summable (fun N => (f N).toReal) := by
  apply (restorationError_summable Cw Ccap hc hlam hσ k₁ k₂).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound N hN)
  simpa only [ENNReal.toReal_ofReal (restorationError_nonneg hw hcap c lam σ k₁ k₂ N)] using hh

end Falconer

end OAI
