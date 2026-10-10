import Mathlib.Logic.Equiv.Fin.Basic
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedDeterminantGoodPrimes

namespace OAI

section

noncomputable section

namespace InternalCatalan

def palindromicResidueIndexEquiv (p : ℕ) : Fin p × Fin 48 ≃ Fin (n p) :=
  (Equiv.prodComm (Fin p) (Fin 48)).trans finProdFinEquiv

theorem palindromicResidueIndexEquiv_val (p : ℕ) (r : Fin p × Fin 48) :
    (palindromicResidueIndexEquiv p r).val = r.1.val + p * r.2.val := rfl

def palindromicScaledRatMatrix (z : ℚ) (p : ℕ) :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) ℚ :=
  fun r k => (p : ℚ) ^ 2 * filteredEntryRat z p
    (p * r.2.val + r.1.val) (k.1.val + p * k.2.val)

theorem palindromicScaledRatMatrix_eq_submatrix (z : ℚ) (p : ℕ) :
    palindromicScaledRatMatrix z p =
      (((p : ℚ) ^ 2) •
        Matrix.of (fun r k : Fin (n p) => filteredEntryRat z p r.val k.val)).submatrix
          (palindromicResidueIndexEquiv p) (palindromicResidueIndexEquiv p) := by
  ext r k
  change (p : ℚ) ^ 2 * filteredEntryRat z p
      (p * r.2.val + r.1.val) (k.1.val + p * k.2.val) =
    (p : ℚ) ^ 2 * filteredEntryRat z p
      (r.1.val + p * r.2.val) (k.1.val + p * k.2.val)
  rw [Nat.add_comm (p * r.2.val) r.1.val]

theorem det_palindromicScaledRatMatrix (z : ℚ) (p : ℕ) :
    (palindromicScaledRatMatrix z p).det =
      (p : ℚ) ^ (2 * n p) * determinantRat z p := by
  rw [palindromicScaledRatMatrix_eq_submatrix,
    Matrix.det_submatrix_equiv_self, Matrix.det_smul]
  simp only [Fintype.card_fin, ← pow_mul, determinantRat]
  rfl

theorem det_palindromicScaledRatMatrix_ne_zero_iff (z : ℚ) {p : ℕ}
    (hp : p ≠ 0) :
    (palindromicScaledRatMatrix z p).det ≠ 0 ↔ determinantRat z p ≠ 0 := by
  rw [det_palindromicScaledRatMatrix]
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  exact mul_ne_zero_iff.trans (and_iff_right (pow_ne_zero (2 * n p) hpq))

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

theorem palindromicScaledResidueMatrix_eq_map (z : ℚ) (p : ℕ) [Fact p.Prime] :
    palindromicScaledResidueMatrix z p =
      fun r k => palindromicRatResidue p (palindromicScaledRatMatrix z p r k) := rfl

theorem palindromicScaledRatMatrix_det_residue (z : ℚ) {p : ℕ} [Fact p.Prime]
    (hentry : ∀ r k : Fin p × Fin 48,
      ((palindromicScaledRatMatrix z p r k).den : ZMod p) ≠ 0) :
    ((palindromicScaledRatMatrix z p).det.den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p (palindromicScaledRatMatrix z p).det =
        (palindromicScaledResidueMatrix z p).det :=
  palindromicRatResidue_det (palindromicScaledRatMatrix z p) hentry

theorem determinantRat_ne_zero_of_scaledResidueMatrix (z : ℚ) {p : ℕ}
    [Fact p.Prime]
    (hentry : ∀ r k : Fin p × Fin 48,
      ((palindromicScaledRatMatrix z p r k).den : ZMod p) ≠ 0)
    (hcertificate : (palindromicScaledResidueMatrix z p).det ≠ 0) :
    determinantRat z p ≠ 0 := by
  apply (det_palindromicScaledRatMatrix_ne_zero_iff z
    (Nat.Prime.ne_zero (Fact.out : p.Prime))).mp
  exact rational_det_ne_zero_of_residue_det_ne_zero
    (palindromicScaledRatMatrix z p) hentry hcertificate

end InternalCatalan

end

end

end OAI
