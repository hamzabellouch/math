import OAI.NumberTheory.TwoPoint.Halasz.HalaszPoissonBound
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparsePolynomial

namespace OAI

/-! The actual finite weighted integer kernel used by sparse cofactor energy. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def halaszTriangleSupport (N : ℝ) : Finset ℕ :=
  range (⌈5*N/2⌉₊+1)

lemma halasz_triangle_nat_zero (N u : ℝ) (hN : 0 < N) (n : ℕ)
    (hn : n ∉ halaszTriangleSupport N) :
    halaszTriangleFunction N u 0 n = 0 := by
    have hnat : ⌈5*N/2⌉₊ < n := by simpa [halaszTriangleSupport] using hn
    have hreal : (⌈5*N/2⌉₊:ℝ) < n := by exact_mod_cast hnat
    unfold halaszTriangleFunction
    rw [halasz_triangle_weight_right_zero N n hN ((Nat.le_ceil _).trans hreal.le),
      Complex.ofReal_zero,zero_mul]
lemma halasz_triangle_neg_zero (N u : ℝ) (hN : 0 < N) (n : ℕ) :
    halaszTriangleFunction N u 0 (-(n+1:ℝ)) = 0 := by
    unfold halaszTriangleFunction
    rw [halasz_triangle_weight_left_zero N _ hN (by
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith),Complex.ofReal_zero,zero_mul]

lemma halasz_triangle_finite_sum (N u : ℝ) (hN : 0 < N) :
    (∑' n : ℤ, halaszTriangleFunction N u 0 n) =
      ∑ n ∈ halaszTriangleSupport N, halaszTriangleFunction N u 0 n := by
  have hn := halasz_triangle_nat_zero N u hN
  have hs : Summable (fun n : ℕ => halaszTriangleFunction N u 0 n) :=
    summable_of_ne_finset_zero hn
  have hneg : (fun n : ℕ => halaszTriangleFunction N u 0 (-(n+1:ℝ))) = 0 := by
    funext n
    exact halasz_triangle_neg_zero N u hN n
  have hsn : Summable (fun n : ℕ => halaszTriangleFunction N u 0 (-(n+1:ℝ))) := by
    rw [hneg]
    exact summable_zero
  have he := tsum_of_nat_of_neg_add_one (f := fun n : ℤ =>
    halaszTriangleFunction N u 0 n) (by simpa only [Int.cast_natCast] using hs)
    (by simpa only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one] using hsn)
  simp only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one] at he
  rw [hneg] at he
  simp only [Pi.zero_def,tsum_zero,add_zero] at he
  exact he.trans (tsum_eq_sum hn)

lemma halasz_triangle_polynomial (N t : ℝ) (hN : 0 < N) :
    mrtExponentialPolynomial (halaszTriangleSupport N)
      (fun n => (halaszTriangleWeight N n:ℂ)) (fun n => -Real.log n) t =
      ∑' n : ℤ, halaszTriangleFunction N (-t) 0 n := by
  rw [halasz_triangle_finite_sum N (-t) hN]
  unfold mrtExponentialPolynomial
  apply sum_congr rfl
  intro n _
  unfold halaszTriangleFunction halaszLogPhase
  congr 2
  push_cast
  ring

theorem halasz_integer_kernel (N t : ℝ) (hN : 0 < N) :
    ‖mrtExponentialPolynomial (halaszTriangleSupport N)
      (fun n => (halaszTriangleWeight N n:ℂ)) (fun n => -Real.log n) t‖ ≤
      18600*N/(1+t^2) + (440/Real.pi)*Real.sqrt |t| +
        (512/(N*(2*Real.pi)^2))*halaszIntegerSquareMass := by
  rw [halasz_triangle_polynomial N t hN]
  simpa only [neg_sq,abs_neg] using halasz_triangle_poisson_bound N (-t) hN

end TwoPointCorrelations

end OAI
