import OAI.NumberTheory.Ostmann.Construction.PhaseGiantCollision
import OAI.NumberTheory.Ostmann.Construction.BoundedWordStatistic

namespace OAI

/-! # The initial positive statistic for the actual Fourier-phase giant -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def phasePrimeAverage {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (ν : I → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (a : ℤ) : ℂ :=
  ∑ i, (ν i : ℂ) * phaseGiantPhysical (g i) (a : ZMod (p i))

theorem phasePrimeAverage_bound {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (ν : I → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (hν : ∀ i, 0 ≤ ν i) (hmass : ∑ i, ν i = 1)
    (N : ℕ) (hN : ∀ i, p i ≤ N) (a : ℤ) :
    ‖phasePrimeAverage p ν g a‖ ≤ Real.sqrt N := by
  apply (norm_sum_le _ _).trans
  calc
    (∑ i, ‖(ν i : ℂ) * phaseGiantPhysical (g i) (a : ZMod (p i))‖) ≤
        ∑ i, ν i * Real.sqrt N := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hν i)]
      exact mul_le_mul_of_nonneg_left ((phaseGiantPhysical_bound (g i) _).trans
        (Real.sqrt_le_sqrt (by exact_mod_cast hN i))) (hν i)
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem phasePrimeAverage_endpoint_sum {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (ν : I → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (E : Finset ℤ) :
    (∑ a ∈ E, (phasePrimeAverage p ν g a).re) =
      ∑ i, ν i * ∑ a ∈ E, (phaseGiantPhysical (g i) (a : ZMod (p i))).re := by
  simp only [phasePrimeAverage, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- The independent nongiant factors have the same positive value at every
selected endpoint. Their lower bound is represented by `κ`; the giant factor
uses its genuine inverse transform and its genuine finite prime law. -/
theorem phasePrimeAverage_initial_statistic {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (ν : I → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (hν : ∀ i, 0 ≤ ν i) (hmass : ∑ i, ν i = 1)
    (N : ℕ) (hN : ∀ i, p i ≤ N)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) (E : Finset ℤ)
    (c κ δ : ℝ) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hδ : 0 ≤ δ)
    (hψ : ∀ x, 0 ≤ (ψ x).re)
    (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (hmean : (E.card : ℝ) * δ ≤
      ∑ i, ν i * ∑ a ∈ E, (phaseGiantPhysical (g i) (a : ZMod (p i))).re) :
    (E.card : ℝ) * (c * (κ * δ) ^ 2) ≤
      ∑' a : ℤ, (ψ ((a : ℝ) / X)).re * ‖(κ : ℂ) * phasePrimeAverage p ν g a‖ ^ 2 := by
  have hb (a : ℤ) : ‖(κ : ℂ) * phasePrimeAverage p ν g a‖ ≤ κ * Real.sqrt N := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hκ]
    exact mul_le_mul_of_nonneg_left (phasePrimeAverage_bound p ν g hν hmass N hN a) hκ
  have hm : (E.card : ℝ) * (κ * δ) ≤
      ∑ a ∈ E, ((κ : ℂ) * phasePrimeAverage p ν g a).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ← Finset.mul_sum, phasePrimeAverage_endpoint_sum]
    calc
      _ = κ * ((E.card : ℝ) * δ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean hκ
  have h := wordStatistic_lower_of_endpoint_mean (m := 0) ψ X hX
    (fun a => (κ : ℂ) * phasePrimeAverage p ν g a) (fun _ _ => 0) E
    (κ * Real.sqrt N) (fun _ => 0) hψ hb (fun i _ => Fin.elim0 i)
    c (κ * δ) 1 hc (mul_nonneg hκ hδ) (by norm_num) hcE hm (fun _ _ i => Fin.elim0 i)
  simpa only [wordStatisticTerm, Nat.mul_zero, pow_zero, mul_one, Fin.prod_univ_zero] using h

end Ostmann

end OAI
