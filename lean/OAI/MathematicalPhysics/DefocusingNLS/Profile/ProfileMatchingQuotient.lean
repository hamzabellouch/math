import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileNonvanishing

namespace OAI

/-! The actual logarithmic derivative equals the quotient of the matched column. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

attribute [local irreducible] backwardProduct profileProduct
  normalizedMatchingB normalizedMatchingC

noncomputable def freeProfileJ (b Z : ℝ) : ℂ :=
  let q : ℂ := -Complex.I*(b : ℂ)
  q*regularizedSlowSolution (q+1) 7 (-Complex.I*(Z : ℂ))/
    regularizedSlowSolution q 6 (-Complex.I*(Z : ℂ))

/-- The normalization of the finite matrix cancels in the component ratio. -/
theorem freeProfileJ_eq_matched (b z : ℝ)
    (hz : |z| ≤ (radius : ℝ)) :
    let q : ℂ := -Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)
    let s : ℂ := Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)
    let r := normalizedMatchingB q 6 s 34/normalizedMatchingC q 6 s 34
    freeProfileJ ((centerB : ℝ)+b) ((centerZ : ℝ)+z) =
      (normalizedProfile b z 1 0*r+normalizedProfile b z 1 1)/
        (normalizedProfile b z 0 0*r+normalizedProfile b z 0 1) := by
  dsimp only
  let q : ℂ := -Complex.I*(((centerB : ℝ)+b : ℝ) : ℂ)
  let s : ℂ := Complex.I*(((centerZ : ℝ)+z : ℝ) : ℂ)
  let r := normalizedMatchingB q 6 s 34/normalizedMatchingC q 6 s 34
  have hq : -1 < q.re := by simp [q]
  have hsre : s.re = 0 := by simp [s]
  have hsim : s.im ≠ 0 := by
    have he := (abs_le.mp hz).1
    have hZ : 0 < (centerZ : ℝ)+z := by norm_num [centerZ, radius] at he ⊢; linarith
    simpa [s] using hZ.ne'
  have hC := (profile_tail_disk b z hz).1
  have hv := normalizedMatching_ratio_column q 5 34 s (by decide) hq hsre hsim hC
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, Pi.smul_apply, smul_eq_mul, slowBoundaryColumn] at h0 h1
  change backwardProduct 5 s q 34 0 0*r+backwardProduct 5 s q 34 0 1 =
    (normalizedMatchingC q 6 s 34)⁻¹*regularizedSlowSolution q 6 (-s) at h0
  change backwardProduct 5 s q 34 1 0*r+backwardProduct 5 s q 34 1 1 =
    (normalizedMatchingC q 6 s 34)⁻¹*(q*regularizedSlowSolution (q+1) 7 (-s)) at h1
  have hfac : (Nat.factorial 34 : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero 34
  have hn : ∀ i j, normalizedProfile b z i j =
      ((Nat.factorial 34 : ℂ)⁻¹/centralM)*backwardProduct 5 s q 34 i j := by
    intro i j
    unfold normalizedProfile profileProduct
    simp only [Matrix.smul_apply, smul_eq_mul]
    change ((Nat.factorial 34 : ℂ)⁻¹*backwardProduct 5 s q 34 i j)/centralM = _
    ring
  rw [hn 1 0, hn 1 1, hn 0 0, hn 0 1]
  simp only [mul_assoc]
  rw [← mul_add, ← mul_add]
  change freeProfileJ ((centerB : ℝ)+b) ((centerZ : ℝ)+z) =
    _*(backwardProduct 5 s q 34 1 0*r+backwardProduct 5 s q 34 1 1)/
      (_*(backwardProduct 5 s q 34 0 0*r+backwardProduct 5 s q 34 0 1))
  rw [h0, h1]
  have hscale : ((Nat.factorial 34 : ℂ)⁻¹/centralM) ≠ 0 :=
    div_ne_zero (inv_ne_zero hfac) centralM_ne_zero
  rw [mul_div_mul_left _ _ hscale, mul_div_mul_left _ _ (inv_ne_zero hC)]
  simp only [freeProfileJ, q, s, neg_mul]

end DefocusingNLS.ProfileCertificate

end OAI
