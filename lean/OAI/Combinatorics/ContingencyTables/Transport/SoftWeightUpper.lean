import OAI.Combinatorics.ContingencyTables.Transport.EqualitySoftening
import OAI.Combinatorics.ContingencyTables.Transport.BalancedEnumeration

namespace OAI

/-! # Uniform upper mass of the positive physical softening family -/

namespace ContingencyTables.EqualitySoftening

open scoped BigOperators Classical
open ScalarPenalty ProductIntegerSignature BalancedFamily BalancedEnumeration

lemma factor_le_one (A : ℝ) (p : ℕ → ℝ) (hA : 0 ≤ A) (n : ℕ) (hp : 0 ≤ p n) :
    factor A p n ≤ 1 := by
  unfold factor
  calc
    (2:ℝ)^(-A*p n) ≤ (2:ℝ)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) hp)
    _ = 1 := by norm_num

variable {C G : Type*} [Fintype C] [Fintype G]

/-- Every actual line/unary soft factor lies in (0,1], even before
the exact nonroot equations are imposed. -/
theorem softenedWeight_le_one (line : C → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : C → ℝ) (L : ℝ)
    (hrate : ∀ g,0 ≤ rate g) (hu : ∀ i,0 ≤ urate i) (hL : 0 ≤ L) (z : C → ℕ) :
    softenedWeight line root rate offset slope urate ell uslope cap L z ≤ 1 := by
  have hl (g : G) : lineFactor root rate offset slope L g (lineTotal line z g) ≤ 1 := by
    apply factor_le_one
    · split_ifs
      · exact hrate g
      · exact hL
    · exact abs_nonneg _
  have hun (i : C) : unaryFactor urate ell uslope cap i (z i) ≤ 1 :=
    factor_le_one _ _ (hu i) _ (le_max_left _ _)
  have hprodL : (∏ g,lineFactor root rate offset slope L g (lineTotal line z g)) ≤ 1 := by
    calc
      _ ≤ ∏ _g : G,(1:ℝ) := Finset.prod_le_prod₀ (fun _ _ => (factor_positive _ _ _).le) (fun g _ => hl g)
      _ = _ := by simp
  have hprodU : (∏ i,unaryFactor urate ell uslope cap i (z i)) ≤ 1 := by
    calc
      _ ≤ ∏ _i : C,(1:ℝ) := Finset.prod_le_prod₀ (fun _ _ => (factor_positive _ _ _).le) (fun i _ => hun i)
      _ = _ := by simp
  have hnonneg : 0 ≤ ∏ i,unaryFactor urate ell uslope cap i (z i) :=
    Finset.prod_nonneg (fun _ _ => (factor_positive _ _ _).le)
  unfold softenedWeight productWeight
  exact (mul_le_mul_of_nonneg_right hprodL hnonneg).trans
    (by simpa only [one_mul] using hprodU)


end ContingencyTables.EqualitySoftening

namespace ContingencyTables.BalancedEnumeration

open scoped BigOperators Classical
open BalancedFamily

/-- The positive softened marginal is bounded by its finite number of
physical balanced assignments, uniformly in the softening parameter. -/
theorem eliminate_le_card {S : Type*} (Ms : List ℕ)
    (F : (Coordinates S Ms → ℕ) → ℝ) (hF : ∀ z,F z ≤ 1) (z : S → ℕ) :
    eliminate Ms F z ≤ (Fintype.card (Assignments Ms):ℝ) := by
  rw [eliminate_eq_sum]
  calc
    _ ≤ ∑ _a : Assignments Ms,(1:ℝ) := Finset.sum_le_sum (fun a _ => hF (embedding Ms z a))
    _ = _ := by simp

end ContingencyTables.BalancedEnumeration

end OAI
