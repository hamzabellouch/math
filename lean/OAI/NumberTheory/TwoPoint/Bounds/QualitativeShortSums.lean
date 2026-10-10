import OAI.NumberTheory.TwoPoint.Bounds.ModifiedShortSums
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! The published MRT theorem at fixed window length, uniformly over
all finite-prime modifications of the original nonpretentious factor. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

lemma loglog_div_log_nonneg (D : ℕ) (hD : 10 ≤ D) :
    0 ≤ Real.log (Real.log (D : ℝ)) / Real.log D := by
  have hDr : (10 : ℝ) ≤ D := by exact_mod_cast hD
  have hdlog : 1 ≤ Real.log (D : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  exact div_nonneg (Real.log_nonneg hdlog) (by linarith)

/-- Fixed-length MRT, with an arbitrarily small residual error. The
supremum over frequencies remains outside the sum over window origins. -/
theorem MRTShortExponentialInput.modified_fixed_windows
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (D : ℕ), 10 ≤ D → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ Y : ℕ in atTop, ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ (l : ℕ) [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ range Y,
          ‖forwardWindowPolynomial (progressionSequence b l a) D (v + 1) θ‖) ≤
          C * D * Y * (Real.log (Real.log (D : ℝ)) / Real.log D + ε) := by
  obtain ⟨C, hC, hraw⟩ := hMRT.modified_windows hfnp hf
  refine ⟨2 * C, by positivity, ?_⟩
  intro P D hD ε hε
  have hehalf : 0 < ε / 2 := by positivity
  have ht : Tendsto (fun Y : ℕ => (Real.log (Y + 1 : ℕ)) ^ (-1 / (700 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (show 0 < (1 / (700 : ℝ)) by norm_num)).comp
      (Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)))
  have hsmall := ht.eventually (gt_mem_nhds hehalf)
  filter_upwards [hraw P D hD (-20 * Real.log (ε / 2)), hsmall,
    eventually_ge_atTop 1] with Y hy hs hY
  intro b hb hbounded heq l _ a θ
  have hval := hy b hb hbounded heq l a θ
  have he : Real.exp (-(-20 * Real.log (ε / 2)) / 20) = ε / 2 := by
    convert Real.exp_log hehalf using 1
    congr 1
    ring
  rw [he] at hval
  have hfirst := loglog_div_log_nonneg D hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hYpos : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
  have hbound := (div_le_iff₀ (mul_pos hDpos hYpos)).mp hval
  have herror : ε / 2 + mrtShortError (Y + 1) D ≤
      Real.log (Real.log (D : ℝ)) / Real.log D + ε := by
    unfold mrtShortError
    linarith only [hs]
  have hYn : ((Y + 1 : ℕ) : ℝ) ≤ 2 * Y := by exact_mod_cast (show Y + 1 ≤ 2 * Y by omega)
  calc
    _ ≤ (C * (ε / 2 + mrtShortError (Y + 1) D)) * ((D : ℝ) * (Y + 1 : ℕ)) := hbound
    _ ≤ (C * (Real.log (Real.log (D : ℝ)) / Real.log D + ε)) *
        ((D : ℝ) * (Y + 1 : ℕ)) := by gcongr
    _ ≤ (C * (Real.log (Real.log (D : ℝ)) / Real.log D + ε)) *
        ((D : ℝ) * (2 * Y)) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
