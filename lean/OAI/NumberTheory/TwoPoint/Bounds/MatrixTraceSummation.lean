import OAI.NumberTheory.TwoPoint.Bounds.ActualColumnTrace

namespace OAI

/-! Sum the actual column bounds over signs and starting vertices. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma trace_dimension_allowance (L : ℝ) (k N : ℕ) (_hL : 0 ≤ L)
    (hk : (k : ℝ) ≤ L) (hN : (N : ℝ) ≤ Real.exp (106 * L)) :
    (N : ℝ) * (2 : ℝ) ^ (2 * k) ≤ Real.exp (108 * L) := by
  have hlog : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ ≤ Real.exp (106 * L) * (2 : ℝ) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = Real.exp (106 * L + (2 * k : ℕ) * Real.log 2) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hb := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 2 * k by positivity)
      push_cast at hb ⊢
      nlinarith

theorem matrix_residue_trace_of_column_bounds {h J M B k : ℕ} {P : Fin J → Finset ℕ}
    {V : Type*} [Fintype V] [DecidableEq V]
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (hP : ∀ j, P j ⊆ data.P) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (s budget : ℕ) (hk : 0 < 2 * k) (hbudget : 2 * k ≤ budget)
    (embed : V → ((j : Fin J) → P j) × ℤ) (hinj : Function.Injective embed)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K T : ℝ) (extra : ℕ → ℤ → Prop)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n, g n ≠ 0)
    (hgdep : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (hallowed : ∀ d q, eligible d q → (d, q) ∈ data.pairs)
    (hT : 0 ≤ T)
    (hdim : (Fintype.card V : ℝ) * (2 : ℝ) ^ (2 * k) ≤ Real.exp (108 * L))
    (hcolumn : ∀ (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool),
      Real.exp (108 * L) * (∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward,
        |prohibitedCenteredAverage data hB s budget
          (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (actualColumnLabel data hP a.1)
          (actualColumnWeight data u eligible g L K extra forward a)|) ≤ T) :
    let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
    let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
    (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
      (shiftMatrix embed (integerShiftNext Q tuple h) (physicalShiftWeight Q tuple h gate
        (fun t n => weight t (n + data.residueOrigin r))) ^ k)) ≤ T := by
  dsimp only
  have hb := columnMatrix_residue_trace_le data hB hP hprime hdisjoint s budget hk hbudget
    embed hinj Q u eligible g L K extra gate hsq hpool hg hgdep hextra hallowed
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (108 * L))).mp
  calc
    _ ≤ Real.exp (108 * L) * (∑ i : V, ∑ forward, ∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k (embed i)) forward,
        |prohibitedCenteredAverage data hB s budget
          (columnTupleWord a.1 forward (fun j => (a.2 j).val)) (actualColumnLabel data hP a.1)
          (actualColumnWeight data u eligible g L K extra forward a)|) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ ∑ _i : V, ∑ _forward : Fin (2 * k) → Bool, T := by
      simp only [mul_sum]
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro forward _
      simpa only [mul_sum] using hcolumn (embed i) forward
    _ = ((Fintype.card V : ℝ) * (2 : ℝ) ^ (2 * k)) * T := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    _ ≤ Real.exp (108 * L) * T := mul_le_mul_of_nonneg_right hdim hT

end TwoPointCorrelations

end OAI
