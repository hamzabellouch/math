import OAI.Analysis.CircleDomains.Sobolev.L2WeakSubsequence
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace OAI

/-! Restricting global weak L2 pairings to a finite-measure set, with a
fixed scalar added to each field. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem restricted_shifted_weak_pairing
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : Set X}
    (hF : MeasurableSet F) [IsFiniteMeasure (μ.restrict F)]
    {u : ℕ → X → ℝ} (hu : ∀ n, MemLp (u n) 2 μ)
    (G : Lp ℝ 2 μ)
    (h : ∀ w : Lp ℝ 2 μ, Tendsto (fun n => ∫ p, u n p*w p ∂μ) atTop
      (𝓝 (∫ p, G p*w p ∂μ))) (a : ℝ) (w : Lp ℝ 2 (μ.restrict F)) :
    Tendsto (fun n => ∫ p in F, (u n p+a)*w p ∂μ) atTop
      (𝓝 (∫ p in F, (G p+a)*w p ∂μ)) := by
  let ψ : X → ℝ := F.indicator w
  have hψ : MemLp ψ 2 μ := (memLp_indicator_iff_restrict hF).mpr (Lp.memLp w)
  have he (f : X → ℝ) : (∫ p, f p*hψ.toLp ψ p ∂μ) = ∫ p in F, f p*w p ∂μ := by
    calc
      _ = ∫ p, f p*ψ p ∂μ := by
        apply integral_congr_ae
        filter_upwards [hψ.coeFn_toLp] with p hp
        rw [hp]
      _ = ∫ p, F.indicator (fun p => f p*w p) p ∂μ := by
        congr 1
        funext p
        by_cases hp : p ∈ F <;> simp [ψ, hp]
      _ = _ := integral_indicator hF
  have hl := h (hψ.toLp ψ)
  simp only [he] at hl
  have hwa : Integrable (fun p => a*w p) (μ.restrict F) :=
    ((Lp.memLp w).integrable (by norm_num)).const_mul a
  have he₀ (n : ℕ) : (∫ p in F, (u n p+a)*w p ∂μ) =
      (∫ p in F, u n p*w p ∂μ)+(∫ p in F, a*w p ∂μ) := by
    simp only [add_mul]
    exact integral_add (((hu n).restrict F).integrable_mul (Lp.memLp w)) hwa
  have he₁ : (∫ p in F, (G p+a)*w p ∂μ) =
      (∫ p in F, G p*w p ∂μ)+(∫ p in F, a*w p ∂μ) := by
    simp only [add_mul]
    exact integral_add (((Lp.memLp G).restrict F).integrable_mul (Lp.memLp w)) hwa
  simpa only [← he₀, ← he₁] using hl.add_const (∫ p in F, a*w p ∂μ)

end CircleDomainRigidity

end

end OAI
