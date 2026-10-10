import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardConeMonotonicity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.MatchingBoundary

namespace OAI

/-! # Uniform exclusion to the right of the counting rectangle -/

open Matrix Polynomial

namespace DefocusingNLS

noncomputable def normalizedForwardMatrix (M s q : ℂ) (N : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((ascPochhammer ℂ N).eval (q - M))⁻¹ • forwardProduct M s q N

theorem normalizedForwardJet_eq_mulVec (M s q : ℂ) (w : Fin 2 → ℂ) (N : ℕ) :
    normalizedForwardJet M s q w N = normalizedForwardMatrix M s q N *ᵥ w := by
  rw [normalizedForwardJet_eq, normalizedForwardMatrix, Matrix.smul_mulVec]

theorem matrixCone_normalizedForwardMatrix (M : ℝ) (s q : ℂ) (N : ℕ)
    (w : Fin 2 → ℂ) :
    matrixCone M s (normalizedForwardMatrix M s q N) w =
      Complex.normSq (((ascPochhammer ℂ N).eval (q - M))⁻¹) *
        matrixCone M s (forwardProduct M s q N) w := by
  simp only [matrixCone, normalizedForwardMatrix, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul]
  exact coneForm_scale M s _ _ _

theorem ascPochhammer_eval_ne_zero_of_re_pos (q : ℂ) (N : ℕ) (hq : 0 < q.re) :
    (ascPochhammer ℂ N).eval q ≠ 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ascPochhammer_succ_eval]
    apply mul_ne_zero ih
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) N]

/-- The right boundary may be taken uniformly beyond `Re q = ell + 5`.
This proves absence of homotopy zeros throughout that entire half-plane. -/
theorem matchingHomotopy_right_ne_zero (ell K : ℕ) (s q₁ q₂ : ℂ) (ρ : ℝ)
    (hK : 3 ≤ K) (hs : s.re = 0) (hs0 : s.im ≠ 0)
    (hq₁ : (ell : ℝ) + 5 < q₁.re) (hq₂ : (ell : ℝ) + 5 < q₂.re)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    matchingColumnDeterminant
      (matchingHomotopyColumn (ell + 5) K s ρ q₁)
      (matchingHomotopyColumn (ell + 5) K (-s) ρ q₂) ≠ 0 := by
  have hM : 0 < (ell : ℝ) + 5 := by positivity
  have hsne : s ≠ 0 := by intro h; apply hs0; simp [h]
  have hd (q : ℂ) (hq : (ell : ℝ) + 5 < q.re) (n : ℕ) :
      q + n - (((ell : ℝ) + 5) : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.ofReal_re,
      Complex.zero_re] at hr
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp (q : ℂ) (hq : (ell : ℝ) + 5 < q.re) :
      (ascPochhammer ℂ K).eval q ≠ 0 ∧
        (ascPochhammer ℂ K).eval (q - (ell + 5)) ≠ 0 := by
    constructor
    · exact ascPochhammer_eval_ne_zero_of_re_pos q K (lt_trans hM hq)
    · apply ascPochhammer_eval_ne_zero_of_re_pos
      simpa using (sub_pos.mpr hq)
  have hcone (q : ℂ) (hq : (ell : ℝ) + 5 < q.re) (s' : ℂ)
      (hs' : s'.re = 0) (hi' : s'.im ≠ 0) :
      matrixCone ((ell : ℝ) + 5) s' (normalizedForwardMatrix (ell + 5) s' q K)
        (matchingHomotopyColumn (ell + 5) K s' ρ q) ≤ 0 := by
    have he := matrixCone_normalizedForwardMatrix ((ell : ℝ) + 5) s' q K
      (matchingHomotopyColumn (ell + 5) K s' ρ q)
    push_cast at he
    rw [he]
    apply mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _)
    have hc := forward_matchingHomotopyColumn_cone (q.re - (ell : ℝ) / 2)
      ell K q s' ρ (by linarith [Nat.cast_nonneg (α := ℝ) ell]) hK (by ring)
      hs' hi' hρ hρ1
    simpa only [matrixCone, Nat.cast_add, Nat.cast_ofNat, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_ofNat] using hc
  apply matchingColumnDeterminant_ne_zero_of_forward_forms ((ell : ℝ) + 5) s (-s)
    (normalizedForwardMatrix (ell + 5) s q₁ K) (normalizedForwardMatrix (ell + 5) (-s) q₂ K)
  · exact matchingHomotopyColumn_ne_zero_of_factors _ _ _ _ _ (hp q₁ hq₁).1
      (by simpa only [Nat.cast_add, Nat.cast_ofNat] using (hp q₁ hq₁).2)
  · exact matchingHomotopyColumn_ne_zero_of_factors _ _ _ _ _ (hp q₂ hq₂).1
      (by simpa only [Nat.cast_add, Nat.cast_ofNat] using (hp q₂ hq₂).2)
  · exact hcone q₁ hq₁ s hs hs0
  · exact hcone q₂ hq₂ (-s) (by simpa using hs) (by simpa using hs0)
  · intro w hw
    have hc := normalizedForwardJet_sum_cone_pos ((ell : ℝ) + 5) s q₁ q₂ w K hM hs hsne
      (by linarith) (by linarith)
      (by simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hd q₁ hq₁)
      (by simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hd q₂ hq₂)
      (by omega) hw
    simpa only [normalizedForwardJet_eq_mulVec, matrixCone, Nat.cast_add, Nat.cast_ofNat,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hc

end DefocusingNLS

end OAI
