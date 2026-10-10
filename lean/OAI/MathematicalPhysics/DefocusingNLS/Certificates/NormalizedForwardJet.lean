import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardConeTransport

namespace OAI

/-! # Forward jets and their Pochhammer divisors -/

open Matrix Polynomial

namespace DefocusingNLS

noncomputable def normalizedForwardJet (M s q : ℂ) (w : Fin 2 → ℂ) :
    ℕ → Fin 2 → ℂ
  | 0 => w
  | n + 1 => (q + n - M)⁻¹ • (forwardMatrix M s (q + n) *ᵥ
      normalizedForwardJet M s q w n)

theorem normalizedForwardJet_eq (M s q : ℂ) (w : Fin 2 → ℂ) (n : ℕ) :
    normalizedForwardJet M s q w n =
      ((ascPochhammer ℂ n).eval (q - M))⁻¹ • (forwardProduct M s q n *ᵥ w) := by
  induction n with
  | zero => simp [normalizedForwardJet, forwardProduct]
  | succ n ih =>
    rw [normalizedForwardJet, ih, Matrix.mulVec_smul, smul_smul,
      forwardProduct, ← Matrix.mulVec_mulVec, ascPochhammer_succ_eval, _root_.mul_inv_rev]
    congr 1
    congr 1
    ring

theorem normalizedForwardJet_succ_first (M s q : ℂ) (w : Fin 2 → ℂ) (n : ℕ) :
    normalizedForwardJet M s q w (n + 1) 0 =
      ((q + n) * normalizedForwardJet M s q w n 0 +
        s * normalizedForwardJet M s q w n 1) / (q + n - M) := by
  simp [normalizedForwardJet, forwardMatrix, dotProduct, Fin.sum_univ_two,
    div_eq_mul_inv, mul_comm]

theorem normalizedForwardJet_succ_second (M s q : ℂ) (w : Fin 2 → ℂ) (n : ℕ)
    (hd : q + n - M ≠ 0) :
    normalizedForwardJet M s q w (n + 1) 1 = normalizedForwardJet M s q w n 1 -
      normalizedForwardJet M s q w (n + 1) 0 := by
  rw [normalizedForwardJet_succ_first]
  conv_lhs => rw [normalizedForwardJet]
  simp [forwardMatrix, dotProduct, Fin.sum_univ_two]

  field_simp [hd]
  ring

theorem normalizedForwardJet_increment (M : ℝ) (s q : ℂ) (w : Fin 2 → ℂ) (n : ℕ)
    (hs : s.re = 0) (hd : q + n - (M : ℂ) ≠ 0) :
    coneForm M s (normalizedForwardJet M s q w (n + 1) 0)
      (normalizedForwardJet M s q w (n + 1) 1) -
      coneForm M s (normalizedForwardJet M s q w n 0)
        (normalizedForwardJet M s q w n 1) =
      ((q + n).re - M / 2) * Complex.normSq
        (normalizedForwardJet M s q w n 0 - normalizedForwardJet M s q w (n + 1) 0) := by
  let B := normalizedForwardJet M s q w n 0
  let C := normalizedForwardJet M s q w n 1
  let B' := normalizedForwardJet M s q w (n + 1) 0
  have hB : B' = ((q + n) * B + s * C) / (q + n - M) :=
    normalizedForwardJet_succ_first M s q w n
  have hrec : (q + n) * (B - B') = -(M : ℂ) * (B - (B - B')) - s * C := by
    rw [hB]
    field_simp [hd]
    ring
  have h := coneForm_increment M s (q + n) B C (B - B') hs hrec
  simpa only [sub_sub_cancel, B, C, B', ← normalizedForwardJet_succ_second M s q w n hd] using h

end DefocusingNLS

end OAI
