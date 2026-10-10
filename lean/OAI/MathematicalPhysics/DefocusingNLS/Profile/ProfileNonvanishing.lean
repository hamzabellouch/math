import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileDenominatorGap
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.AnalyticMatchingColumn
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileQuotientAlgebra

namespace OAI

/-! The computed denominator gap proves that the actual free slow profile is nonzero. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

attribute [local irreducible] backwardProduct normalizedMatchingB normalizedMatchingC
  profileProduct

private theorem actualZ_pos (z : ℝ) (hz : |z| ≤ (radius : ℝ)) :
    0 < (centerZ : ℝ)+z := by
  have h := (abs_le.mp hz).1
  norm_num [centerZ, radius] at h ⊢
  linarith

/-- The tail used in the finite product is the actual normalized analytic tail. -/
theorem profile_tail_disk (b z : ℝ) (hz : |z| ≤ (radius : ℝ)) :
    let q : ℂ := -Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)
    let s : ℂ := Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)
    normalizedMatchingC q 6 s 34 ≠ 0 ∧
      ‖normalizedMatchingB q 6 s 34/normalizedMatchingC q 6 s 34+s/5‖ ≤
        ((centerZ : ℝ)+z)/5 := by
  dsimp only
  have hZ := actualZ_pos z hz
  have h := normalizedMatching_tail_disk 0 0 34
    (-Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)) (Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ))
    (by norm_num) (by decide) (by simp) (by simp) (by simpa using hZ.ne')
  refine ⟨h.1, ?_⟩
  have hd := h.2
  simp only [Nat.cast_zero, Complex.ofReal_zero, zero_add] at hd
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hd
  have hs : ‖Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)/(5 : ℂ)‖ = ((centerZ : ℝ)+z)/5 := by
    simp only [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_ofNat, abs_of_pos hZ]
  rw [hs] at hd
  nlinarith [norm_nonneg (normalizedMatchingB (-Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)) 6
    (Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)) 34/normalizedMatchingC (-Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)) 6
    (Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)) 34+Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)/5)]

/-- No zero of H occurs anywhere in the certificate's full parameter square. -/
theorem free_profile_nonzero (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) :
    regularizedSlowSolution (-Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)) 6
      (-(Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ))) ≠ 0 := by
  let q : ℂ := -Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)
  let s : ℂ := Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)
  let R := normalizedMatchingB q 6 s 34/normalizedMatchingC q 6 s 34
  let A : Matrix (Fin 2) (Fin 2) ℂ := normalizedProfile b z
  obtain ⟨hC, hR⟩ := profile_tail_disk b z hz
  have hg := normalized_denominator_gap b z hb hz
  simp only [← Complex.ofReal_add] at hg
  have hn : A 0 0*R+A 0 1 ≠ 0 := by
    apply matched_denominator_ne_zero A R (s/5) (((centerZ : ℝ)+z)/5) hR
    dsimp only [A, s]
    linarith
  have hq : -1 < q.re := by dsimp [q]; norm_num
  have hsre : s.re = 0 := by simp [s]
  have hsim : s.im ≠ 0 := by simpa [s] using (actualZ_pos z hz).ne'
  have hc := congrFun (normalizedMatching_ratio_column q 5 34 s (by decide)
    hq hsre hsim hC) 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, Pi.smul_apply, smul_eq_mul, slowBoundaryColumn] at hc
  intro hH
  have he : A 0 0*R+A 0 1 = 0 := by
    dsimp only [A, normalizedProfile]
    unfold profileProduct
    simp only [Matrix.smul_apply, smul_eq_mul]
    have he0 : regularizedSlowSolution q 6 (-s) = 0 := hH
    rw [he0, mul_zero] at hc
    change backwardProduct 5 s q 34 0 0*R+backwardProduct 5 s q 34 0 1 = 0 at hc
    calc
      _ = ((Nat.factorial 34 : ℂ)⁻¹/centralM)*
        (backwardProduct 5 s q 34 0 0*R+backwardProduct 5 s q 34 0 1) := by
          change (((Nat.factorial 34 : ℂ)⁻¹*backwardProduct 5 s q 34 0 0)/centralM)*R+
            ((Nat.factorial 34 : ℂ)⁻¹*backwardProduct 5 s q 34 0 1)/centralM = _
          ring
      _ = 0 := by rw [hc]; ring
  exact hn he

end DefocusingNLS.ProfileCertificate

end OAI
