import OAI.Analysis.LipschitzHilbert.Estimates.FiniteVariation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! A measurable common exceptional set for all selected scale intervals. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem measurable_finiteCubicVariation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (F : ℕ → Ω → E) (hF : ∀ n, Measurable (F n)) (N : ℕ) :
    Measurable (fun x => finiteCubicVariation (fun n => F n x) N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : Ω) =>
    if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Measurable (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact Finset.measurable_sum _ fun i _ => ((hF _).sub (hF _)).norm.pow_const _
    · simpa only [g, ite_eq_right hp] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  have hs := Finset.measurable_sup' Finset.univ_nonempty (fun p _ => hg p)
  convert hs using 1
  funext x
  simp only [finiteCubicVariation, g, Finset.sup'_apply]

def variationBadSet {Ω E : Type*} [NormedAddCommGroup E]
    (F : ℕ → Ω → E) (N : ℕ) (V : ℝ) : Set Ω :=
  {x | V ^ 3 ≤ finiteCubicVariation (fun n => F n x) N}

theorem measurableSet_variationBadSet {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (F : ℕ → Ω → E) (hF : ∀ n, Measurable (F n))
    (N : ℕ) (V : ℝ) : MeasurableSet (variationBadSet F N V) :=
  measurableSet_le measurable_const (measurable_finiteCubicVariation F hF N)

theorem variationBadSet_measure {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) (F : ℕ → Ω → E)
    (hF : ∀ n, Measurable (F n)) (N : ℕ) {V : ℝ} (hV : 0 ≤ V) :
    ENNReal.ofReal (V ^ 2) * μ (variationBadSet F N V) ≤
      ∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ) ∂μ := by
  have hVpow : (V ^ 3) ^ (2 / 3 : ℝ) = V ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV]
    norm_num
  have hsubset : variationBadSet F N V ⊆
      {x | ENNReal.ofReal (V ^ 2) ≤
        ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ)} := by
    intro x hx
    have h := Real.rpow_le_rpow (pow_nonneg hV 3) hx (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [hVpow] at h
    change ENNReal.ofReal (V ^ 2) ≤
      ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ)
    rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
    exact ENNReal.ofReal_le_ofReal h
  exact (mul_le_mul_right (measure_mono hsubset) _).trans
    (mul_meas_ge_le_lintegral
      ((measurable_finiteCubicVariation F hF N).ennreal_ofReal.pow_const _) _)

end LipschitzHilbert

end

end OAI
