import OAI.Analysis.IrrationalRotation.Sampling.MixedRadix
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233

theorem infinitePi_eventually_mem_null
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : (n : ℕ) → Set (X n)) (hs : ∀ n, MeasurableSet (s n))
    {q : ℝ≥0∞} (hq : q < 1) (hprob : ∀ n, μ n (s n) ≤ q) :
    (Measure.infinitePi μ) {x | ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ s n} = 0 := by
  have htail (N k : ℕ) :
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} ≤ q ^ k := by
    calc
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} ≤
          (Measure.infinitePi μ) (Set.pi (Finset.Ico N (N + k)) s) := by
        apply measure_mono
        intro x hx n hn
        exact hx n (Finset.mem_Ico.mp hn).1
      _ = ∏ n ∈ Finset.Ico N (N + k), μ n (s n) :=
        Measure.infinitePi_pi μ (fun n _ => hs n)
      _ ≤ ∏ _n ∈ Finset.Ico N (N + k), q :=
        Finset.prod_le_prod (fun n _ => hprob n)
      _ = q ^ k := by simp
  have hnull (N : ℕ) :
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} = 0 := by
    apply le_antisymm _ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
      (Eventually.of_forall (htail N))
  have heq : {x : (n : ℕ) → X n | ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ s n} =
      ⋃ N : ℕ, {x | ∀ n, N ≤ n → x n ∈ s n} := by
    ext x
    simp
  rw [heq]
  exact measure_iUnion_null hnull

namespace MixedRadix

variable {r : ℕ → ℕ} [∀ n, NeZero (r n)]

theorem uniformDigit_singleton (n : ℕ) (a : Fin (r n)) :
    (PMF.uniformOfFintype (Fin (r n))).toMeasure {a} = (r n : ℝ≥0∞)⁻¹ := by
  simp

theorem ae_nonterminal_uniformDigits (hr : ∀ n, 2 ≤ r n) :
    ∀ᵐ d ∂Measure.infinitePi (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure),
      Nonterminal d := by
  let s : (n : ℕ) → Set (Fin (r n)) := fun n => {a | ¬(a : ℕ) + 1 < r n}
  have hs (n : ℕ) : MeasurableSet (s n) := Set.toFinite (s n) |>.measurableSet
  have heq (n : ℕ) : s n = {⟨r n - 1, by have := hr n; omega⟩} := by
    ext a
    simp only [s, Set.mem_ofPred_eq, Set.mem_singleton_iff, Fin.ext_iff]
    have ha := a.isLt
    have h := hr n
    omega
  have hprob (n : ℕ) : (PMF.uniformOfFintype (Fin (r n))).toMeasure (s n) ≤
      (2 : ℝ≥0∞)⁻¹ := by
    rw [heq, uniformDigit_singleton]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hr n)
  have hnull := infinitePi_eventually_mem_null
    (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure) s hs
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1) hprob
  rw [ae_iff]
  simpa only [Nonterminal, Set.mem_ofPred_eq, not_forall, not_exists, not_and, s] using hnull

theorem ae_nonterminal_of_absolutelyContinuous (hr : ∀ n, 2 ≤ r n)
    {ν : Measure (Digits r)}
    (hν : ν ≪ Measure.infinitePi (fun n =>
      (PMF.uniformOfFintype (Fin (r n))).toMeasure)) :
    ∀ᵐ d ∂ν, Nonterminal d :=
  hν.ae_le (ae_nonterminal_uniformDigits hr)

theorem ae_floor_coordinate_recovers_digit (hr : ∀ n, 2 ≤ r n) :
    ∀ᵐ d ∂Measure.infinitePi (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure),
      ∀ j : ℕ, ⌊(r j : ℝ) * Int.fract ((denominator r j : ℝ) * ofDigits d)⌋₊ =
        (d j : ℕ) := by
  filter_upwards [ae_nonterminal_uniformDigits hr] with d hd
  exact floor_coordinate_recovers_digit (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)) d hd

theorem ae_ofDigits_mem_Ico (hr : ∀ n, 2 ≤ r n) :
    ∀ᵐ d ∂Measure.infinitePi (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure),
      ofDigits d ∈ Set.Ico (0 : ℝ) 1 := by
  filter_upwards [ae_nonterminal_uniformDigits hr] with d hd
  refine ⟨ofDigits_nonneg d, ?_⟩
  simpa [tailValue, ofDigits] using
    tailValue_lt_one (fun n => lt_of_lt_of_le (by decide : 0 < 2) (hr n)) d hd 0

end MixedRadix
end Invariant233

end OAI
