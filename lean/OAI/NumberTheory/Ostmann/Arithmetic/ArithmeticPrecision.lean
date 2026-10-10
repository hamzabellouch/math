import Mathlib.Data.Int.ModEq
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSupport

namespace OAI

/-! # The exact loss of frequency precision at a reversing node -/

namespace Ostmann

theorem modEq_cancel_coprime_left (m u a b : ℤ) (hu : IsCoprime u m)
    (h : u * a ≡ u * b [ZMOD m]) : a ≡ b [ZMOD m] := by
  apply Int.modEq_iff_dvd.mpr
  apply hu.symm.dvd_of_dvd_mul_left
  have hd := h.dvd
  rwa [← mul_sub] at hd

/-- Division by `s` consumes one copy of `R`; division by its unit factor consumes none. -/
theorem reversal_residue_precision (R s u u' N N' p p' : ℤ) (k : ℕ)
    (hs : s ≠ 0) (hsR : s ∣ R) (hu : IsCoprime u R)
    (hN : N = s * u * p) (hN' : N' = s * u' * p')
    (hmod : N ≡ N' [ZMOD R ^ (k + 1)]) (humod : u ≡ u' [ZMOD R ^ k]) :
    p ≡ p' [ZMOD R ^ k] := by
  have hdiv : s * R ^ k ∣ N' - N := by
    apply dvd_trans _ hmod.dvd
    simpa only [pow_succ, mul_comm s] using mul_dvd_mul_left (R ^ k) hsR
  rw [hN', hN, show s * u' * p' - s * u * p = s * (u' * p' - u * p) by ring] at hdiv
  have hproducts : u * p ≡ u' * p' [ZMOD R ^ k] :=
    Int.modEq_iff_dvd.mpr (Int.dvd_of_mul_dvd_mul_left hs hdiv)
  apply modEq_cancel_coprime_left (R ^ k) u p p' hu.pow_right
  exact hproducts.trans (humod.symm.mul_right p')

/-- At every depth of a chain the remaining power still determines the reconstructed integer. -/
theorem reversal_chain_residue_precision (R : ℤ) (s u u' v v' : ℕ → ℤ) (k : ℕ)
    (hs : ∀ j, s j ≠ 0) (hsR : ∀ j, s j ∣ R) (hu : ∀ j, IsCoprime (u j) R)
    (hv : ∀ j, v j = s j * u j * v (j + 1))
    (hv' : ∀ j, v' j = s j * u' j * v' (j + 1))
    (hmod : v 0 ≡ v' 0 [ZMOD R ^ (k + 1)])
    (humod : ∀ j, u j ≡ u' j [ZMOD R ^ (k + 1)]) :
    ∀ j ≤ k + 1, v j ≡ v' j [ZMOD R ^ (k + 1 - j)] := by
  intro j
  induction j with
  | zero => intro _; simpa using hmod
  | succ j ih =>
    intro hj
    have hj' : j ≤ k := by omega
    have hexp : k + 1 - j = (k - j) + 1 := by omega
    have hprev := ih (by omega)
    rw [hexp] at hprev
    have hunit : u j ≡ u' j [ZMOD R ^ (k - j)] :=
      (humod j).of_dvd (pow_dvd_pow R (by omega : k - j ≤ k + 1))
    have h := reversal_residue_precision R (s j) (u j) (u' j) (v j) (v' j)
      (v (j + 1)) (v' (j + 1)) (k - j) (hs j) (hsR j) (hu j)
        (hv j) (hv' j) hprev hunit
    simpa only [show k + 1 - (j + 1) = k - j by omega] using h

end Ostmann

end OAI
