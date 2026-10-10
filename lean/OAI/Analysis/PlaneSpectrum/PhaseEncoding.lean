import Mathlib

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators

open scoped BigOperators
open Polynomial
namespace EuclideanFiveColor.PhaseEncoding

section

def phases {m : ℕ} (z : Fin m → Circle) : Multiset ℂ :=
  Finset.univ.val.map (fun i => (z i : ℂ))

def elem {m : ℕ} (z : Fin m → Circle) (n : ℕ) : ℂ := (phases z).esymm n

/-- Exactly the elementary symmetric functions of degrees 1,…,m. -/
def encoding {m : ℕ} (z : Fin m → Circle) : Fin m → ℂ :=
  fun i => elem z (i.val + 1)

def phasePolynomial {m : ℕ} (z : Fin m → Circle) : ℂ[X] :=
  ∏ i : Fin m, (X - C (z i : ℂ))

@[simp] theorem card_phases {m : ℕ} (z : Fin m → Circle) : (phases z).card = m := by
  simp [phases]

@[simp] theorem elem_zero {m : ℕ} (z : Fin m → Circle) : elem z 0 = 1 := by
  simp [elem, Multiset.esymm]

theorem elem_eq_sum {m : ℕ} (z : Fin m → Circle) (n : ℕ) :
    elem z n = ∑ t ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      ∏ i ∈ t, (z i : ℂ) :=
  Finset.esymm_map_val _ _ n

theorem continuous_encoding {m : ℕ} : Continuous (encoding (m := m)) := by
  apply continuous_pi
  intro i
  simp only [encoding, elem_eq_sum]
  fun_prop

theorem polynomial_expansion {m : ℕ} (z : Fin m → Circle) :
    phasePolynomial z = ∑ n ∈ Finset.range (m + 1),
      (-1) ^ n * (C (elem z n) * X ^ (m - n)) := by
  have he : phasePolynomial z = ((phases z).map (fun t => X - C t)).prod := by
    rw [phasePolynomial, Finset.prod_eq_multiset_prod]
    simp only [phases, Multiset.map_map, Function.comp_def]
  rw [he, Multiset.prod_X_sub_X_eq_sum_esymm, card_phases]
  rfl

@[simp] theorem eval_at_phase {m : ℕ} (z : Fin m → Circle) (i : Fin m) :
    (phasePolynomial z).eval (z i : ℂ) = 0 := by
  rw [phasePolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

theorem eval_expansion {m : ℕ} (z : Fin m → Circle) (a : ℂ) :
    (phasePolynomial z).eval a = ∑ n ∈ Finset.range (m + 1),
      (-1 : ℂ) ^ n * (elem z n * a ^ (m - n)) := by
  rw [polynomial_expansion, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  simp

theorem eval_difference {m : ℕ} (z w : Fin m → Circle) (a : ℂ) :
    (phasePolynomial w).eval a - (phasePolynomial z).eval a =
      ∑ n ∈ Finset.range m,
        (-1 : ℂ) ^ (n+1) * ((elem w (n+1) - elem z (n+1)) * a ^ (m-(n+1))) := by
  rw [eval_expansion, eval_expansion, ← Finset.sum_sub_distrib,
    Finset.sum_range_succ']
  simp only [pow_zero, elem_zero, one_mul, sub_self, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- A coefficient bound on the unit circle, with the common leading term removed. -/
theorem eval_difference_bound {m : ℕ} (z w : Fin m → Circle) (a : Circle) :
    ‖(phasePolynomial w).eval (a : ℂ) - (phasePolynomial z).eval (a : ℂ)‖ ≤
      m * dist (encoding z) (encoding w) := by
  rw [eval_difference]
  calc
    _ ≤ ∑ n ∈ Finset.range m,
      ‖(-1 : ℂ) ^ (n+1) * ((elem w (n+1) - elem z (n+1)) * (a : ℂ) ^ (m-(n+1)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range m, dist (encoding z) (encoding w) := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, Circle.norm_coe,
        one_mul, mul_one]
      have h := dist_le_pi_dist (encoding z) (encoding w) ⟨n, Finset.mem_range.mp hn⟩
      simpa only [dist_eq_norm, encoding, norm_sub_rev] using h
    _ = _ := by simp

/-- An explicit uniform inverse estimate sufficient for the phase collision step. -/
theorem close_encoding_each_phase {m : ℕ} (hm : 0 < m)
    (z w : Fin m → Circle) {ρ : ℝ} (hρ : 0 < ρ)
    (hzw : dist (encoding z) (encoding w) < ρ ^ m / m) :
    ∀ i, ∃ j, dist (z i : ℂ) (w j : ℂ) < ρ := by
  intro i
  by_contra h
  push Not at h
  have hl : ρ ^ m ≤ ‖(phasePolynomial w).eval (z i : ℂ)‖ := by
    rw [phasePolynomial, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [norm_prod]
    calc
      ρ ^ m = ∏ _j : Fin m, ρ := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hρ.le) (fun j _ => by
        simpa only [dist_eq_norm] using h j)
  have hu := eval_difference_bound z w (z i)
  rw [eval_at_phase, sub_zero] at hu
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hb : (m : ℝ) * dist (encoding z) (encoding w) < ρ ^ m := by
    simpa only [mul_comm] using (lt_div_iff₀ hm').mp hzw
  exact (not_lt_of_ge (hl.trans hu)) hb

open scoped BigOperators

/-- Newton reconstruction from the entire sequence of power sums. -/
def fromPowers (p : ℕ → ℂ) (n : ℕ) : ℂ :=
  match n with
  | 0 => 1
  | k + 1 => (k + 1 : ℂ)⁻¹ * (-1) ^ (k + 2) *
      ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) * fromPowers p i * p (k + 1 - i)
termination_by n
decreasing_by
  exact i.isLt

lemma measurable_fromPowers {Y : Type*} [MeasurableSpace Y] (p : Y → ℕ → ℂ)
    (hp : ∀ n, Measurable (fun y => p y n)) (n : ℕ) :
    Measurable (fun y => fromPowers (p y) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [fromPowers]; exact measurable_const
    | succ k =>
      simp only [fromPowers]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i _
      exact (Measurable.const_mul (ih i i.isLt) _).mul (hp _)

lemma newton_elem {m : ℕ} (z : Fin m → Circle) (k : ℕ) :
    (k : ℂ) * elem z k = (-1) ^ (k + 1) *
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * elem z a.1 * (∑ i, (z i : ℂ) ^ a.2) := by
  have h := congrArg (MvPolynomial.aeval (fun i => (z i : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum (Fin m) ℂ k)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X,
    elem, phases] using h

lemma filtered_antidiagonal_sum (f : ℕ → ℕ → ℂ) (k : ℕ) :
    (∑ a ∈ (Finset.HasAntidiagonal.antidiagonal (k+1)).filter (fun a => a.1 < k+1), f a.1 a.2) =
      ∑ i : Fin (k+1), f i (k+1-i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f i (k+1-i)) (k+1), Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

theorem fromPowers_eq_elem {m : ℕ} (z : Fin m → Circle) (n : ℕ) :
    fromPowers (fun k => ∑ i, (z i : ℂ) ^ k) n = elem z n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [fromPowers]
    | succ k =>
      rw [fromPowers]
      have hs : (∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) *
          fromPowers (fun n => ∑ j, (z j : ℂ)^n) i * (∑ j, (z j : ℂ)^(k+1-i))) =
          ∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) * elem z i *
            (∑ j, (z j : ℂ)^(k+1-i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ih i i.isLt]
      rw [hs, mul_assoc, ← filtered_antidiagonal_sum
        (fun i j => (-1 : ℂ)^i * elem z i * (∑ l, (z l : ℂ)^j)) k]
      have hn := newton_elem z (k+1)
      rw [Nat.cast_add, Nat.cast_one] at hn
      rw [← hn, inv_mul_cancel_left₀]
      exact_mod_cast (Nat.succ_ne_zero k)

end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Y G : Type*} [MeasurableSpace Y] [MeasurableSpace G]

/-- The measurable phase encoding, defined without a measurable enumeration. -/
def kernelEncoding (β : Kernel Y G) (χ : G → ℂ) (m : ℕ) (y : Y) : Fin m → ℂ :=
  fun i => fromPowers (fun n => (m : ℂ) * ∫ d, χ d ^ n ∂β y) (i.val + 1)

theorem measurable_kernelEncoding (β : Kernel Y G) [IsMarkovKernel β]
    (χ : G → ℂ) (hχ : Measurable χ) (m : ℕ) :
    Measurable (kernelEncoding β χ m) := by
  apply Measurable.of_eval
  intro i
  apply measurable_fromPowers
  intro n
  exact (((hχ.pow_const n).stronglyMeasurable.integral_kernel).measurable).const_mul _

theorem moments_uniform_list [MeasurableSingletonClass G] (χ : G → ℂ) (m : ℕ) (hm : 0 < m) (g : Fin m → G)
    (μ : Measure G) (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i))
    (n : ℕ) :
    (m : ℂ) * (∫ d, χ d ^ n ∂μ) = ∑ i, χ (g i) ^ n := by
  classical
  rw [hμ, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [← mul_assoc, mul_inv_cancel₀, one_mul]
    exact_mod_cast hm.ne'
  · intro i _
    exact integrable_dirac (by simp)

/-- On every uniform finite fiber, the formula is exactly the source's
 elementary-symmetric vector, including repetitions of equal phases. -/
theorem kernelEncoding_eq_encoding [MeasurableSingletonClass G] (β : Kernel Y G) (χ : G → Circle)
    (m : ℕ) (hm : 0 < m) (y : Y) (g : Fin m → G)
    (hβ : β y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i)) :
    kernelEncoding β (fun d => (χ d : ℂ)) m y = encoding (fun i => χ (g i)) := by
  have hp : (fun n => (m : ℂ) * ∫ d, (χ d : ℂ)^n ∂β y) =
      fun n => ∑ i, (χ (g i) : ℂ)^n := by
    funext n
    exact moments_uniform_list (fun d => (χ d : ℂ)) m hm g (β y) hβ n
  funext i
  change fromPowers _ (i.val+1) = elem _ (i.val+1)
  rw [hp]
  exact fromPowers_eq_elem (fun i => χ (g i)) (i.val+1)

end

/-- Boundedness of the exact phase encoding, from compactness of the phase torus. -/
theorem exists_encoding_bound (m : ℕ) :
    ∃ B : ℝ, ∀ z : Fin m → Circle, ‖encoding z‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_encoding (m := m))).isBounded.exists_norm_le
  exact ⟨B, fun z => hB _ ⟨z, rfl⟩⟩
end EuclideanFiveColor.PhaseEncoding

end

end OAI
