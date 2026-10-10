import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicHeight
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFixedPauli

namespace OAI

/-! Uniform rational-register bounds for the actual fixed-arity Pauli
trace.  These supply an explicit precision budget before scalar sampling. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar
open scoped BigOperators Classical

theorem height_finiteSum {α : Type} [Fintype α] (f : α → Scalar) :
    height (finiteSum f) ≤ ∑ a, height (f a) := by
  calc
    _ ≤ ∑ i : Fin (Fintype.card α), height (f ((Fintype.equivFin α).symm i)) := by
      simpa only [finiteSum,enumerate,List.map_map,List.map_ofFn,List.sum_ofFn,
        Function.comp_apply] using
        height_sum ((enumerate α).map f)
    _ = _ := (Fintype.equivFin α).symm.sum_comp (fun a => height (f a))

theorem height_finiteProduct {α : Type} [Fintype α] (f : α → Scalar) :
    height (finiteProduct f) ≤ ∏ a, height (f a) := by
  calc
    _ ≤ ∏ i : Fin (Fintype.card α), height (f ((Fintype.equivFin α).symm i)) := by
      simpa only [finiteProduct,enumerate,List.map_map,List.map_ofFn,List.prod_ofFn,
        Function.comp_apply] using
        height_product ((enumerate α).map f)
    _ = _ := (Fintype.equivFin α).symm.prod_comp (fun a => height (f a))

theorem height_pauli (μ : Fin 4) (a b : Fin 2) : height (pauli μ a b) ≤ 1 := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,height,realHeight,rat,realRat,neg,realNeg,imaginary]

theorem height_word {ι : Type} [Fintype ι]
    (w : ι → Fin 4) (s t : ι → Fin 2) : height (word w s t) ≤ 1 := by
  apply (height_finiteProduct _).trans
  exact Finset.prod_le_one₀ (fun _ _ => height_nonnegative _)
    (fun _ _ => height_pauli _ _ _)

theorem height_coefficient {ι : Type} [Fintype ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4)
    (C : ℚ) (hA : ∀ s t, height (A s t) ≤ C) :
    height (coefficient A w) ≤ (2:ℚ)^Fintype.card ι*C := by
  have hcell (s t : ι → Fin 2) : height (mul (A s t) (word w t s)) ≤ C := by
    calc
      _ ≤ height (A s t)*height (word w t s) := height_mul _ _
      _ ≤ height (A s t)*1 :=
        mul_le_mul_of_nonneg_left (height_word _ _ _) (height_nonnegative _)
      _ ≤ C := by simpa using hA s t
  have hsum : height (finiteSum (fun s : ι → Fin 2 =>
      finiteSum (fun t : ι → Fin 2 => mul (A s t) (word w t s)))) ≤
      ∑ _s : ι → Fin 2, ∑ _t : ι → Fin 2, C := by
    apply (height_finiteSum _).trans
    apply Finset.sum_le_sum
    intro s _
    exact (height_finiteSum _).trans (Finset.sum_le_sum (fun t _ => hcell s t))
  have hp : 0 < (2:ℚ)^Fintype.card ι := pow_pos (by norm_num) _
  calc
    _ ≤ height (rat ((2:ℚ)^Fintype.card ι)⁻¹)*
        height (finiteSum (fun s => finiteSum (fun t => mul (A s t) (word w t s)))) :=
      height_mul _ _
    _ ≤ ((2:ℚ)^Fintype.card ι)⁻¹*(∑ _s : ι → Fin 2, ∑ _t : ι → Fin 2, C) := by
      rw [height_rat,abs_of_pos (inv_pos.mpr hp)]
      exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hp.le)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,
        Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
      field_simp

theorem realHeight_coefficient {ι : Type} [Fintype ι]
    (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar) (w : ι → Fin 4)
    (C : ℚ) (hA : ∀ s t, height (A s t) ≤ C) :
    realHeight (realCoefficient A w) ≤ (2:ℚ)^Fintype.card ι*C := by
  apply le_trans (le_add_of_nonneg_right (realHeight_nonnegative (coefficient A w).2))
  exact height_coefficient A w C hA

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
