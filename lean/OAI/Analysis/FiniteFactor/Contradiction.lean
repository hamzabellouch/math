import OAI.Analysis.FiniteFactor.Polynomial
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology

/-- Choose the uniform ε before any endpoint coefficient arrays are supplied. -/
noncomputable def polynomialEpsilon (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) : ℝ :=
  (laurent_product_uniform_lower_bound K D δ hδ).choose

theorem polynomialEpsilon_pos (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    0 < polynomialEpsilon K D δ hδ :=
  (laurent_product_uniform_lower_bound K D δ hδ).choose_spec.1

noncomputable def coefficientMass (K : ℕ) (A B : ℤ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range (2*K+1), ‖laurentProductCoefficient K A B (-(n : ℤ))‖

theorem polynomialEpsilon_le_mass (K : ℕ) (D δ : ℝ) (hδ : 0 < δ)
    (A B : ℤ → ℂ)
    (hA : ∀ v : ℤ, -(K : ℤ) ≤ v → v ≤ K → ‖A v‖ ≤ D)
    (hB : ∀ v : ℤ, -(K : ℤ) ≤ v → v ≤ K → ‖B v‖ ≤ D)
    (hA0 : δ ≤ ‖A 0‖) (hB0 : δ ≤ ‖B 0‖) :
    polynomialEpsilon K D δ hδ ≤ coefficientMass K A B := by
  obtain ⟨n, hn, hbound⟩ :=
    (laurent_product_uniform_lower_bound K D δ hδ).choose_spec.2 A B hA hB hA0 hB0
  have hnmem : n ∈ Finset.range (2*K+1) := Finset.mem_range.mpr (by omega)
  apply hbound.trans
  unfold coefficientMass
  exact Finset.single_le_sum (fun (i : ℕ) _ => norm_nonneg (laurentProductCoefficient K A B (-(i : ℤ)))) hnmem

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The finite-polynomial lower bound survives expectation on a measurable
event, using only almost-everywhere coefficient bounds. -/
theorem polynomial_event_integral_lower (K : ℕ) (D δ : ℝ) (hδ : 0 < δ)
    (A B : Ω → ℤ → ℂ) {E : Set Ω} (hE : MeasurableSet E)
    (hint : IntegrableOn (fun ω => coefficientMass K (A ω) (B ω)) E μ)
    (hA : ∀ᵐ ω ∂μ, ω ∈ E →
      ∀ v : ℤ, -(K : ℤ) ≤ v → v ≤ K → ‖A ω v‖ ≤ D)
    (hB : ∀ᵐ ω ∂μ, ω ∈ E →
      ∀ v : ℤ, -(K : ℤ) ≤ v → v ≤ K → ‖B ω v‖ ≤ D)
    (hA0 : ∀ᵐ ω ∂μ, ω ∈ E → δ ≤ ‖A ω 0‖)
    (hB0 : ∀ᵐ ω ∂μ, ω ∈ E → δ ≤ ‖B ω 0‖) :
    polynomialEpsilon K D δ hδ * μ.real E ≤
      ∫ ω in E, coefficientMass K (A ω) (B ω) ∂μ := by
  have hlower : ∀ᵐ ω ∂μ, ω ∈ E →
      polynomialEpsilon K D δ hδ ≤ coefficientMass K (A ω) (B ω) := by
    filter_upwards [hA, hB, hA0, hB0] with ω ha hb ha0 hb0 hω
    exact polynomialEpsilon_le_mass K D δ hδ _ _ (ha hω) (hb hω) (ha0 hω) (hb0 hω)
  have hi := setIntegral_mono_on_ae
    (integrable_const (polynomialEpsilon K D δ hδ)) hint hE hlower
  rw [setIntegral_const, smul_eq_mul, mul_comm] at hi
  exact hi

omit [IsFiniteMeasure μ] in
/-- Sum the per-coefficient expectation bounds over the exact finite range. -/
theorem coefficientMass_integral_upper (K : ℕ) (A B : Ω → ℤ → ℂ)
    {E : Set Ω} {a : ℝ}
    (hint : ∀ n ≤ 2*K, IntegrableOn
      (fun ω => ‖laurentProductCoefficient K (A ω) (B ω) (-(n : ℤ))‖) E μ)
    (hupper : ∀ n ≤ 2*K,
      (∫ ω in E, ‖laurentProductCoefficient K (A ω) (B ω) (-(n : ℤ))‖ ∂μ) ≤ a) :
    (∫ ω in E, coefficientMass K (A ω) (B ω) ∂μ) ≤ (2*(K : ℝ)+1)*a := by
  unfold coefficientMass
  rw [integral_finsetSum (Finset.range (2*K+1)) (fun n hn => hint n (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hn)))]
  calc
    _ ≤ ∑ n ∈ Finset.range (2*K+1), a :=
      Finset.sum_le_sum (fun n hn => hupper n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
    _ = _ := by simp [Nat.cast_add, Nat.cast_mul]

/-- The numerical relaxation in final-upper-bound. -/
theorem exponential_tail_relaxation {L : ℝ} (hL : 0 ≤ L) :
    Real.exp (-L) + 2 * Real.exp (-L/800) ≤ 3 * Real.exp (-L/10000) := by
  have h₁ : Real.exp (-L) ≤ Real.exp (-L/10000) := Real.exp_le_exp.mpr (by linarith)
  have h₂ : Real.exp (-L/800) ≤ Real.exp (-L/10000) := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem no_eventual_small_convolutions
    {Ωs : ℕ → Type*} [∀ j, MeasurableSpace (Ωs j)]
    (μs : ∀ j, Measure (Ωs j)) [∀ j, IsFiniteMeasure (μs j)]
    (K : ℕ → ℕ) (D δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (A B : ∀ j, Ωs j → ℤ → ℂ) (E : ∀ j, Set (Ωs j))
    (hE : ∀ j, MeasurableSet (E j))
    (hint : ∀ j, IntegrableOn (fun ω => coefficientMass (K j) (A j ω) (B j ω)) (E j) (μs j))
    (hA : ∀ j, ∀ᵐ ω ∂(μs j), ω ∈ E j →
      ∀ v : ℤ, -(K j : ℤ) ≤ v → v ≤ K j → ‖A j ω v‖ ≤ D j)
    (hB : ∀ j, ∀ᵐ ω ∂(μs j), ω ∈ E j →
      ∀ v : ℤ, -(K j : ℤ) ≤ v → v ≤ K j → ‖B j ω v‖ ≤ D j)
    (hA0 : ∀ j, ∀ᵐ ω ∂(μs j), ω ∈ E j → δ j ≤ ‖A j ω 0‖)
    (hB0 : ∀ j, ∀ᵐ ω ∂(μs j), ω ∈ E j → δ j ≤ ‖B j ω 0‖)
    {c : ℝ} (hc : 0 < c)
    (hmass : ∀ᶠ j in atTop, c ≤ (μs j).real (E j))
    (hupper : ∀ᶠ j in atTop,
      (∫ ω in E j, coefficientMass (K j) (A j ω) (B j ω) ∂(μs j)) ≤
        polynomialEpsilon (K j) (D j) (δ j) (hδ j) / ((j : ℝ)+1)) : False := by
  have hsmall : ∀ᶠ (j : ℕ) in atTop, c ≤ 1 / ((j : ℝ)+1) := by
    filter_upwards [hmass, hupper] with j hm hu
    have hp := polynomialEpsilon_pos (K j) (D j) (δ j) (hδ j)
    have hl := polynomial_event_integral_lower (K j) (D j) (δ j) (hδ j)
      (A j) (B j) (hE j) (hint j) (hA j) (hB j) (hA0 j) (hB0 j)
    have hmul : polynomialEpsilon (K j) (D j) (δ j) (hδ j) * c ≤
        polynomialEpsilon (K j) (D j) (δ j) (hδ j) * (1 / ((j : ℝ)+1)) := by
      calc
        _ ≤ polynomialEpsilon (K j) (D j) (δ j) (hδ j) * (μs j).real (E j) :=
          mul_le_mul_of_nonneg_left hm hp.le
        _ ≤ _ := hl
        _ ≤ polynomialEpsilon (K j) (D j) (δ j) (hδ j) / ((j : ℝ)+1) := hu
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [mul_comm] using hmul)
  exact (not_le_of_gt hc) (ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat hsmall)

end FiniteFactor

end OAI
