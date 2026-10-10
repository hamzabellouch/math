import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic

namespace OAI

section

open scoped NNReal

namespace Balanced
open scoped _root_.Balanced

theorem profile_recurrence_factorial {p : ℕ → ℝ} {k : ℝ}
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * p (n + 1) = k * p n) (n : ℕ) :
    p n = p 0 * k ^ n / (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    calc
      p (n + 1) = k * p n / (n + 1 : ℝ) := by
        apply (eq_div_iff hn).2
        nlinarith [hrec n]
      _ = p 0 * k ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        rw [ih, Nat.factorial_succ, pow_succ]
        push_cast
        field_simp

theorem profile_recurrence_poisson {p : ℕ → ℝ} {k : ℝ}
    (hsum : HasSum p 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * p (n + 1) = k * p n) (n : ℕ) :
    p n = Real.exp (-k) * k ^ n / (n.factorial : ℝ) := by
  have hseries : HasSum p (p 0 * Real.exp k) := by
    have hexp : HasSum (fun i : ℕ => k ^ i / (i.factorial : ℝ)) (Real.exp k) := by
      simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp k
    have hp : p = fun i => p 0 * (k ^ i / (i.factorial : ℝ)) := by
      funext i
      rw [profile_recurrence_factorial hrec i]
      ring
    convert! hexp.mul_left (p 0) using 1
  have hzero : p 0 = Real.exp (-k) := by
    have hnorm : p 0 * Real.exp k = 1 := hseries.unique hsum
    calc
      p 0 = 1 / Real.exp k := (eq_div_iff (Real.exp_ne_zero k)).2 hnorm
      _ = Real.exp (-k) := by simp [Real.exp_neg]
  rw [profile_recurrence_factorial hrec n, hzero]

theorem profile_recurrence_eq_poissonMeasure {p : ℕ → ℝ} (k : ℝ≥0)
    (hsum : HasSum p 1)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * p (n + 1) = (k : ℝ) * p n) :
    ∀ n : ℕ, p n = (ProbabilityTheory.poissonMeasure k).real {n} := by
  intro n
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  exact profile_recurrence_poisson hsum hrec n

theorem profile_recurrence_factorization {p : ℕ → ℕ → ℝ} {k : ℝ}
    (hrec : ∀ i j : ℕ, (i + 1 : ℝ) * p (i + 1) j = k * p i j)
    (i j : ℕ) : p i j = k ^ i / (i.factorial : ℝ) * p 0 j := by
  rw [profile_recurrence_factorial (p := fun n => p n j) (fun n => hrec n j) i]
  ring

end Balanced

end

section

namespace Balanced
open scoped _root_.Balanced
namespace ProfileVisibility

open MeasureTheory

theorem ae_eq_const_of_integral_eq {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ} {a : ℝ}
    (hf : Integrable f ν) (hupper : ∀ᵐ x ∂ν, f x ≤ a)
    (hint : (∫ x, f x ∂ν) = ν.real Set.univ * a) :
    f =ᵐ[ν] fun _ => a := by
  apply (integral_eq_iff_of_ae_le hf (integrable_const a) hupper).mp
  simpa [integral_const] using hint

theorem ae_eq_const_of_probability_integral {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ} {a : ℝ}
    (hf : Integrable f ν) (hupper : ∀ᵐ x ∂ν, f x ≤ a)
    (hint : (∫ x, f x ∂ν) = a) :
    f =ᵐ[ν] fun _ => a := by
  apply ae_eq_const_of_integral_eq hf hupper
  simpa using hint

theorem recurrence_of_invisible {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν]
    (P : ℕ → ℕ → ℝ) (X : Ω → ℕ → ℕ → ℝ) {k : ℝ}
    (hmass : ν.real Set.univ = k)
    (hinc : ∀ i j : ℕ, (∫ x, X x (i + 1) j ∂ν) =
      (i + 1 : ℝ) * P (i + 1) j)
    (hinvisible : ∀ i j : ℕ,
      (fun x => X x (i + 1) j) =ᵐ[ν] fun _ => P i j) :
    ∀ i j : ℕ, (i + 1 : ℝ) * P (i + 1) j = k * P i j := by
  intro i j
  calc
    (i + 1 : ℝ) * P (i + 1) j = ∫ x, X x (i + 1) j ∂ν := (hinc i j).symm
    _ = ∫ _x, P i j ∂ν := integral_congr_ae (hinvisible i j)
    _ = k * P i j := by simp [integral_const, hmass]

theorem null_of_vanishes {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f : Ω → ℝ} {a : ℝ} {I : Set Ω}
    (ha : a ≠ 0) (hf : f =ᵐ[ν] fun _ => a)
    (hI : ∀ x ∈ I, f x = 0) : ν I = 0 := by
  have hnot : ∀ᵐ x ∂ν, x ∉ I := by
    filter_upwards [hf] with x hx hxI
    apply ha
    exact hx.symm.trans (hI x hxI)
  simpa using (ae_iff.mp hnot)

theorem full_mass_of_vanishes {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {f : Ω → ℝ} {a : ℝ} {I : Set Ω}
    (ha : a ≠ 0) (hf : f =ᵐ[ν] fun _ => a)
    (hI : ∀ x ∈ I, f x = 0) : ν Iᶜ = ν Set.univ := by
  apply measure_congr
  filter_upwards [hf] with x hx
  apply propext
  apply iff_true_intro
  intro hxI
  apply ha
  exact hx.symm.trans (hI x hxI)

theorem saturated_coordinate_visible {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ} {μ : ℝ}
    {invisible : Set Ω} (hμ : 0 < μ)
    (hf : Integrable f ν) (hupper : ∀ᵐ x ∂ν, f x ≤ μ)
    (hint : (∫ x, f x ∂ν) = μ)
    (hvanish : ∀ x ∈ invisible, f x = 0) :
    ν invisible = 0 ∧ ν invisibleᶜ = 1 := by
  have heq := ae_eq_const_of_probability_integral hf hupper hint
  refine ⟨null_of_vanishes (ne_of_gt hμ) heq hvanish, ?_⟩
  rw [full_mass_of_vanishes (ne_of_gt hμ) heq hvanish, measure_univ]

end ProfileVisibility
end Balanced

end

end OAI
