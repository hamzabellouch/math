import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

namespace OAI

/-! # Negative logarithmic density limits carry no limiting mass -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem density_le_of_log_gap {ε δ x : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hx : 0 < x)
    (hgap : ε*Real.log x ≤ -δ) : x ≤ ε/δ := by
  have hl : Real.log x ≤ -δ/ε := (le_div_iff₀ hε).mpr (by nlinarith only [hgap])
  have he : (δ/ε)*Real.exp (-(δ/ε)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one _).trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hb : Real.exp (-(δ/ε)) ≤ ε/δ := by
    apply (mul_le_mul_iff_right₀ (div_pos hδ hε)).mp
    calc
      (δ/ε)*Real.exp (-(δ/ε)) ≤ 1 := he
      _ = (δ/ε)*(ε/δ) := by field_simp
  exact ((Real.log_le_iff_le_exp hx).mp hl).trans (by simpa only [neg_div] using hb)

theorem negative_log_density_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (ε : ℕ → ℝ)
    (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    {U : Set X} (hU : MeasurableSet U) (hfinite : μ U ≠ ∞)
    (hf : ∀ k x, x ∈ U → 0 < f k x)
    (s : X → ℝ) {δ : ℝ} (hδ : 0 < δ) (hs : ∀ x ∈ U, s x ≤ -δ)
    (hlog : TendstoUniformlyOn (fun k x => ε k*Real.log (f k x)) s atTop U) :
    Tendsto (fun k => (μ.withDensity (fun x => ENNReal.ofReal (f k x))) U) atTop (𝓝 0) := by
  have hbound : ∀ᶠ k in atTop, (μ.withDensity (fun x => ENNReal.ofReal (f k x))) U ≤
      ENNReal.ofReal (ε k/(δ/2))*μ U := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlog) (δ/2) (half_pos hδ)] with k hk
    rw [withDensity_apply _ hU]
    calc
      _ ≤ ∫⁻ _ in U, ENNReal.ofReal (ε k/(δ/2)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hU] with x hx
        apply ENNReal.ofReal_le_ofReal
        apply density_le_of_log_gap (hε k) (half_pos hδ) (hf k x hx)
        have hh := hk x hx
        rw [Real.dist_eq] at hh
        have hu := (abs_lt.mp hh).1
        linarith [hs x hx]
      _ = _ := by simp
  have hreal : Tendsto (fun k => ε k/(δ/2)) atTop (𝓝 0) := by
    simpa only [zero_div] using hε0.div_const (δ/2)
  have hn : Tendsto (fun k => ENNReal.ofReal (ε k/(δ/2))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hm := ENNReal.Tendsto.mul_const hn (Or.inr hfinite)
  simp only [zero_mul] at hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hm
    (Eventually.of_forall fun _ => bot_le) hbound

end RegularPointCoordinates

end

end OAI
