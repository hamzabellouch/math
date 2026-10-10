import OAI.MeasureTheory.Falconer.Estimates.TripleGram
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace OAI

/-! # Dimension-dependent cofactor bounds for the weak-radial transverse frame -/

namespace Falconer
open scoped BigOperators
variable {d : ℕ}

theorem unit_entry_determinant_bound (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) : |M.det| ≤ (d.factorial:ℝ) := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d), |((Equiv.Perm.sign σ : ℤ):ℝ)*∏ i, M (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul,abs_unit_intCast,one_mul,Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hM (σ i) i)).trans_eq
        (by simp)
    _ = _ := by simp [Fintype.card_perm]

theorem unit_entry_adjugate_bound (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) (i j : Fin d) : |M.adjugate i j| ≤ (d.factorial:ℝ) := by
  rw [Matrix.adjugate_apply]
  apply unit_entry_determinant_bound
  intro a b
  by_cases ha : a = j
  · subst a
    by_cases hb : b = i <;> simp [Matrix.updateRow_apply,hb]
  · simpa only [Matrix.updateRow_apply,ha,ite_false] using hM a b

theorem unit_entry_inverse_bound (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) (i j : Fin d) : |M⁻¹ i j| ≤ (d.factorial:ℝ)/|M.det| := by
  rw [Matrix.inv_def,Matrix.smul_apply,Ring.inverse_eq_inv,smul_eq_mul,abs_mul,abs_inv]
  calc
    _ ≤ |M.det|⁻¹*(d.factorial:ℝ) :=
      mul_le_mul_of_nonneg_left (unit_entry_adjugate_bound M hM i j) (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by rw [div_eq_mul_inv,mul_comm]

end Falconer

end OAI
