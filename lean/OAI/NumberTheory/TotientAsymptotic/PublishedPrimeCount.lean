import OAI.NumberTheory.TotientAsymptotic.Basic

namespace OAI

/-!
The classical prime number theorem, in precisely the epsilon form used here.
Hadamard and de la Vallée Poussin (1896); for a numbered, accessible statement
see Terence Tao, *254A, Notes 2: Complex-analytic multiplicative number theory*
(9 December 2014), Exercise 40, following Corollary 39:
https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/
Only pi(y) ~ y/log(y) is retained from the stronger published estimate.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def PrimeNumberTheoremInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ y : ℝ in atTop,
    |(Nat.primeCounting ⌊y⌋₊ : ℝ)-y/Real.log y| ≤ ε*(y/Real.log y)

/-- A deterministic change of the logarithm and the endpoint in a prime
count. Its hypotheses are later verified uniformly over all prefix data. -/
lemma prime_count_change_scale {x y z δ : ℝ}
    (hL : 0 < Real.log x) (hz : 0 ≤ z) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/4)
    (hlog : (1-δ)*Real.log x ≤ Real.log y ∧ Real.log y ≤ (1+δ)*Real.log x)
    (hy : z ≤ y ∧ y ≤ (1+δ)*z)
    (hp : |(Nat.primeCounting ⌊y⌋₊ : ℝ)-y/Real.log y| ≤ δ*(y/Real.log y)) :
    |(Nat.primeCounting ⌊y⌋₊ : ℝ)-z/Real.log x| ≤ 6*δ*(z/Real.log x) := by
  have hly : 0 < Real.log y := lt_of_lt_of_le (mul_pos (by linarith) hL) hlog.1
  have hden : 0 < Real.log y*Real.log x := mul_pos hly hL
  have hratio : |y/Real.log y-z/Real.log x| ≤ 3*δ*(z/Real.log x) := by
    apply (abs_le).mpr
    constructor
    · have hh : -(3*δ*z*Real.log y) ≤ y*Real.log x-z*Real.log y := by
        have h1 := mul_le_mul_of_nonneg_right hy.1 hL.le
        have h2 := mul_le_mul_of_nonneg_left hlog.2 hz
        have h3 := mul_le_mul_of_nonneg_left hlog.1 (mul_nonneg hδ hz)
        nlinarith
      convert (div_le_div_of_nonneg_right hh hden.le) using 1 <;> field_simp
    · have hh : y*Real.log x-z*Real.log y ≤ 3*δ*z*Real.log y := by
        have h1 := mul_le_mul_of_nonneg_right hy.2 hL.le
        have h2 := mul_le_mul_of_nonneg_left hlog.1 hz
        have h3 := mul_le_mul_of_nonneg_left hlog.1 (mul_nonneg hδ hz)
        nlinarith [mul_nonneg (show 0 ≤ δ*(1-4*δ) by nlinarith) (mul_nonneg hz hL.le)]
      convert (div_le_div_of_nonneg_right hh hden.le) using 1 <;> field_simp
  have hsize : y/Real.log y ≤ 2*(z/Real.log x) := by
    apply (div_le_iff₀ hly).mpr
    have h1 := mul_le_mul_of_nonneg_right hy.2 hL.le
    have h2 := mul_le_mul_of_nonneg_left hlog.1 hz
    have hh : y*Real.log x ≤ 2*z*Real.log y := by
      nlinarith [mul_nonneg hz hL.le]
    have ht := (le_div_iff₀ hL).mpr hh
    convert ht using 1; field_simp
  calc
    _ ≤ |(Nat.primeCounting ⌊y⌋₊ : ℝ)-y/Real.log y|+|y/Real.log y-z/Real.log x| := abs_sub_le _ _ _
    _ ≤ δ*(y/Real.log y)+3*δ*(z/Real.log x) := add_le_add hp hratio
    _ ≤ 6*δ*(z/Real.log x) := by
      have hh := mul_le_mul_of_nonneg_left hsize hδ
      nlinarith [mul_nonneg hδ (div_nonneg hz hL.le)]

end TotientAsymptotic

end

end OAI
