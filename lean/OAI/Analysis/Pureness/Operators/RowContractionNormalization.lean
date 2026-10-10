import OAI.Analysis.Pureness.Operators.FiniteSelfCommutators
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem normalize_selfCommutator_family {n : ℕ} (a : Fin n → A)
    (hgap : algebraMap ℝ A (1 / 2) ≤ ∑ i, (star (a i) * a i - a i * star (a i))) :
    ∃ b : Fin (n + 1) → A,
      (∑ i, star (b i) * b i) = 1 ∧ ‖∑ i, b i * star (b i)‖ < 1 := by
  let S := ∑ i, star (a i) * a i
  let T := ∑ i, a i * star (a i)
  let r : ℝ := ‖S‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hrhalf : 0 ≤ r - 1 / 2 := by dsimp [r]; linarith [norm_nonneg S]
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => star_mul_self_nonneg (a i))
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_star_self_nonneg (a i))
  have hST : algebraMap ℝ A (1 / 2) ≤ S - T := by
    simpa only [Finset.sum_sub_distrib] using hgap
  have hSr : S ≤ r • (1 : A) := by
    apply hS.isSelfAdjoint.le_algebraMap_norm_self.trans
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right (show ‖S‖ ≤ r by dsimp [r]; linarith)
        (zero_le_one : (0 : A) ≤ 1)
  let c := CFC.sqrt (r • (1 : A) - S)
  have hc : star c = c := (CFC.sqrt_nonneg _).star_eq
  have hcc : c * c = r • (1 : A) - S :=
    CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hSr)
  let d : Fin (n + 1) → A := Fin.cons c a
  have hdcol : (∑ i, star (d i) * d i) = r • (1 : A) := by
    rw [Fin.sum_univ_succ]
    change star c * c + S = r • (1 : A)
    rw [hc, hcc, sub_add_cancel]
  have hdrow : (∑ i, d i * star (d i)) = r • (1 : A) - (S - T) := by
    rw [Fin.sum_univ_succ]
    change c * star c + T = r • (1 : A) - (S - T)
    rw [hc, hcc]
    abel
  have hdrow0 : 0 ≤ ∑ i, d i * star (d i) :=
    Finset.sum_nonneg (fun i _ => mul_star_self_nonneg (d i))
  have hdrown : ‖∑ i, d i * star (d i)‖ ≤ r - 1 / 2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hrhalf hdrow0).mpr
    rw [hdrow]
    have hh := sub_le_sub_left hST (r • (1 : A))
    simpa only [Algebra.algebraMap_eq_smul_one, ← sub_smul] using hh
  let t : ℝ := Real.sqrt r⁻¹
  have htt : t * t = r⁻¹ := Real.mul_self_sqrt (inv_nonneg.mpr hr.le)
  have hcol (i : Fin (n+1)) : star (t • d i) * (t • d i) = r⁻¹ • (star (d i) * d i) := by
    simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, htt]
  have hrow (i : Fin (n+1)) : (t • d i) * star (t • d i) = r⁻¹ • (d i * star (d i)) := by
    simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul, htt]
  refine ⟨fun i => t • d i, ?_, ?_⟩
  · simp only [hcol, ← Finset.smul_sum, hdcol, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · simp only [hrow, ← Finset.smul_sum, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hr.le)]
    calc
      r⁻¹ * ‖∑ i, d i * star (d i)‖ ≤ r⁻¹ * (r - 1 / 2) :=
        mul_le_mul_of_nonneg_left hdrown (inv_nonneg.mpr hr.le)
      _ < 1 := by
        rw [inv_mul_lt_iff₀ hr]
        linarith
end CuntzPureness

end

end OAI
