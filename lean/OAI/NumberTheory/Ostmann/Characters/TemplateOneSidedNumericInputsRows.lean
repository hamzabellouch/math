import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputsGrowth
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPrior

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedNumericInputs
open Preliminaries PrimeDyadicCover TemplateOneSidedPrior

theorem progression_row_height (C z β L : ℝ) (hC : 0 ≤ C)
    (Q b n r : ℕ) (hb : 1 ≤ b) (hbU : b ≤ sourceUpper β L)
    (hn : n ≤ 2*b+1) (hr : r < Q)
    (hQ : (Q:ℝ) ≤ Real.exp (historyPolynomialCost C z 3 L)) :
    |((Q*n+r:ℕ):ℝ)| ≤ Real.exp (rowLogHeight C z β L) := by
  have hrow : Q*n+r ≤ 4*Q*b := by
    have hqn := Nat.mul_le_mul_left Q hn
    have hqb := Nat.mul_le_mul_left Q hb
    nlinarith [Nat.le_of_lt hr]
  have hbexp : (b:ℝ) ≤ Real.exp (Real.exp (β*L)) :=
    (by exact_mod_cast hbU : (b:ℝ) ≤ sourceUpper β L).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hc : 0 ≤ historyPolynomialCost C z 3 L := by
    unfold historyPolynomialCost
    positivity
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ 4*(Q:ℝ)*(b:ℝ) := by exact_mod_cast hrow
    _ ≤ 4*(Real.exp (historyPolynomialCost C z 3 L)*Real.exp (Real.exp (β*L))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hQ hbexp (Nat.cast_nonneg _) (Real.exp_pos _).le) (by norm_num)
    _ = Real.exp (Real.exp (β*L)+Real.log 4+historyPolynomialCost C z 3 L) := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by unfold rowLogHeight; linarith)

theorem rowLogHeight_ge_log_two (C z β L : ℝ) (hC : 0 ≤ C) :
    Real.log 2 ≤ rowLogHeight C z β L := by
  have hc : 0 ≤ historyPolynomialCost C z 3 L := by unfold historyPolynomialCost; positivity
  have hh : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  unfold rowLogHeight
  linarith [Real.exp_pos (β*L)]

theorem source_prime_height {N : ℕ} (C z β L : ℝ) (hC : 0 ≤ C)
    (p : PrimeUpTo N) (hp : Real.log p.val ≤ Real.exp (β*L)) :
    |(p.val:ℝ)| ≤ Real.exp (rowLogHeight C z β L) := by
  have hp0 : (0:ℝ) < p.val := by exact_mod_cast (primeUpTo_prime p).pos
  have hc : 0 ≤ historyPolynomialCost C z 3 L := by unfold historyPolynomialCost; positivity
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hheight : Real.exp (β*L) ≤ rowLogHeight C z β L := by unfold rowLogHeight; linarith
  rw [abs_of_nonneg hp0.le]
  calc
    _ = Real.exp (Real.log p.val) := (Real.exp_log hp0).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hp.trans hheight)

theorem occupied_block_upper {N : ℕ} (Q : ℕ) (hQ : 0 < Q)
    (E : Finset (PrimeUpTo N)) {β L : ℝ}
    (hmin : ∀p∈E,Q ≤ p.val) (hmax : ∀p∈E,Real.log p.val ≤ Real.exp (β*L))
    (i : Index (sourceUpper β L)) (hi : (block Q (sourceUpper β L) (sourceNaturals E) i).Nonempty) :
    lower Q (sourceUpper β L) i ≤ sourceUpper β L := by
  obtain ⟨p,hp⟩ := hi
  have hlo := (block_bounds hQ _ (sourceNaturals_property E _ hmin) i hp).1
  have hps := block_subset Q (sourceUpper β L) (sourceNaturals E) i hp
  exact hlo.trans (sourceNaturals_property E (fun n=>n ≤ sourceUpper β L)
    (source_upper_of_log E hmax) p hps)

theorem occupied_source_row_height {N : ℕ} (C z β L : ℝ) (hC : 0 ≤ C)
    (Q : ℕ) (hQ : 0 < Q) (hQcost : (Q:ℝ) ≤ Real.exp (historyPolynomialCost C z 3 L))
    (E : Finset (PrimeUpTo N)) (hmin : ∀p∈E,Q ≤ p.val)
    (hmax : ∀p∈E,Real.log p.val ≤ Real.exp (β*L))
    (i : Index (sourceUpper β L)) (hi : (block Q (sourceUpper β L) (sourceNaturals E) i).Nonempty)
    (x : Fin Q × Fin (2*lower Q (sourceUpper β L) i+1)) :
    |(rowValue Q (2*lower Q (sourceUpper β L) i+1) x:ℝ)| ≤ Real.exp (rowLogHeight C z β L) := by
  exact progression_row_height C z β L hC Q _ x.2.val x.1.val
    (block_lower_pos hQ i) (occupied_block_upper Q hQ E hmin hmax i hi)
    x.2.isLt.le x.1.isLt hQcost

end Ostmann.Characters.TemplateOneSidedNumericInputs

end

end OAI
