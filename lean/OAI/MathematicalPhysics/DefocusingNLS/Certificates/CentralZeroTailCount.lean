import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ZeroTailAnalyticCount

namespace OAI

/-! # The numerical central zero-tail count in a counting rectangle -/

open Polynomial

namespace DefocusingNLS.SeparatorArithmetic

attribute [local irreducible] spectralHomotopyDeterminant windingPolynomial

theorem central_zeroTail_zero_of_polynomial_root (ell : ℕ) (w : ℂ)
    (hw : ((windingPolynomial ell).map (Int.castRingHom ℂ)).IsRoot w) :
    spectralHomotopyDeterminant ell (33477607 / 100000000) (270506819 / 100000000)
      0 (w - 1 / 32) = 0 := by
  have h := windingPolynomial_eval_zeroTailDeterminant ell w
  rw [hw.eq_zero, mul_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- Every sufficiently tall counting rectangle contains exactly the certified
number of zero-tail zeros, counted by their analytic orders. -/
theorem exists_central_zeroTail_rectangle_count (ell : Fin 4) :
    ∃ V : ℝ, 0 < V ∧ ∀ W : ℝ, V < W →
      rectangleZeroCount W
        (spectralHomotopyDeterminant ell (33477607 / 100000000) (270506819 / 100000000) 0) =
          (positiveRootCount ell : ℕ∞) := by
  classical
  obtain ⟨V, hV, hboundary⟩ := exists_spectral_counting_boundary ell
  refine ⟨V, hV, ?_⟩
  intro W hW
  rw [central_zeroTail_rectangle_count]
  have hfilter :
      (((windingPolynomial ell).map (Int.castRingHom ℂ)).roots.toFinset.filter
        (fun w => w - 1 / 32 ∈ countingRectangle W)) =
      (((windingPolynomial ell).map (Int.castRingHom ℂ)).roots.toFinset.filter
        (fun w => 0 ≤ w.re)) := by
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hw, hrect⟩
      refine ⟨hw, ?_⟩
      have hlo := hrect.1
      simp only [Complex.sub_re] at hlo
      norm_num at hlo
      linarith
    · rintro ⟨hw, hre⟩
      have hroot : ((windingPolynomial ell).map (Int.castRingHom ℂ)).IsRoot w :=
        (Polynomial.mem_roots (windingPolynomial_complex_ne_zero ell)).mp
          (Multiset.mem_toFinset.mp hw)
      have haxis := windingPolynomial_no_axis_root ell hroot
      have hwpos : 0 < w.re := lt_of_le_of_ne hre (Ne.symm haxis)
      have hz0 := central_zeroTail_zero_of_polynomial_root ell w hroot
      have hlo : -(1 / 32 : ℝ) < (w - (1 / 32 : ℂ)).re := by
        simp only [Complex.sub_re]
        norm_num
        linarith
      have hn := fun (he : (w - (1 / 32 : ℂ)).re = -(1 / 32 : ℝ) ∨
          8 ≤ (w - (1 / 32 : ℂ)).re ∨
          (-(1 / 32 : ℝ) ≤ (w - (1 / 32 : ℂ)).re ∧ V < |(w - (1 / 32 : ℂ)).im|)) =>
        (hboundary (33477607 / 100000000) (270506819 / 100000000) 0
          (w - 1 / 32) (by norm_num) (by norm_num) le_rfl (by norm_num) he) hz0
      have hright : (w - (1 / 32 : ℂ)).re < 8 :=
        lt_of_not_ge (fun h => hn (Or.inr (Or.inl h)))
      have hheight : |(w - (1 / 32 : ℂ)).im| < W :=
        (le_of_not_gt (fun h => hn (Or.inr (Or.inr ⟨hlo.le, h⟩)))).trans_lt hW
      exact ⟨hw, hlo, hright, (abs_lt.mp hheight).1, (abs_lt.mp hheight).2⟩
  rw [hfilter, windingPolynomial_closed_half_plane_count]

end DefocusingNLS.SeparatorArithmetic

end OAI
