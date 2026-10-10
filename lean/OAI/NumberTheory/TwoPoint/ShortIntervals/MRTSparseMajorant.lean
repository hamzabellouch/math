import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSparseRows

namespace OAI

/-! Removing the artificial smooth coefficient weight on the original
finite polynomial support. The majorant need only be at least one there. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

theorem mrt_sparse_majorized_energy {ι : Type*} (K P : Finset ι) (hPK : P ⊆ K)
    (w freq : ι → ℝ) (a : ι → ℂ) (hw : ∀ n ∈ K, 0 ≤ w n)
    (hwP : ∀ n ∈ P, 1 ≤ w n) (S : Finset ℝ)
    (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hkernel : ∀ t ∈ S, ∀ s ∈ S,
      ‖mrtExponentialPolynomial K (fun n => (w n:ℂ)) freq (t-s)‖ ≤
        A/(1+(t-s)^2)+D) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a freq t‖^2) ≤
      (8*A+(S.card:ℝ)*D) * ∑ n ∈ P, ‖a n‖^2 := by
  let b := fun n => if n ∈ P then a n/(w n:ℂ) else 0
  have hb (n : ι) (hn : n ∈ P) : (w n:ℂ)*b n = a n := by
    have hpos : 0 < w n := lt_of_lt_of_le zero_lt_one (hwP n hn)
    have hnz : (w n:ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    dsimp only [b]
    rw [ite_eq_left hn]
    field_simp
  have he (t : ℝ) : mrtExponentialPolynomial K (fun n => (w n:ℂ)*b n) freq t =
      mrtExponentialPolynomial P a freq t := by
    unfold mrtExponentialPolynomial
    calc
      _ = ∑ n ∈ P, (w n:ℂ)*b n*Complex.exp (((freq n*t:ℝ):ℂ)*I) := by
        symm
        apply sum_subset hPK
        intro n _ hn
        simp [b,hn]
      _ = _ := sum_congr rfl (fun n hn => by rw [hb n hn])
  have hmass : (∑ n ∈ K, w n*‖b n‖^2) ≤ ∑ n ∈ P, ‖a n‖^2 := by
    calc
      _ = ∑ n ∈ P, w n*‖b n‖^2 := by
        symm
        apply sum_subset hPK
        intro n _ hn
        simp [b,hn]
      _ ≤ _ := by
        apply sum_le_sum
        intro n hn
        have hpos : 0 < w n := lt_of_lt_of_le zero_lt_one (hwP n hn)
        dsimp only [b]
        rw [ite_eq_left hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hpos]
        calc
          _ = ‖a n‖^2/w n := by field_simp
          _ ≤ _ := div_le_self (sq_nonneg _) (hwP n hn)
  have h := mrt_sparse_weighted_row_energy K w freq b hw S hsep hA hD hkernel
  simp_rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left hmass (by positivity))

end TwoPointCorrelations

end OAI
