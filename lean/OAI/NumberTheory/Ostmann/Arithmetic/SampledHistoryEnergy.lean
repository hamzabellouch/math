import OAI.NumberTheory.Ostmann.Construction.AdaptivePivotSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HarmonicHistorySupport
import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveFrequencySupport

namespace OAI

/-! # The squared-history sum with its constructed arithmetic support -/

namespace Ostmann

open scoped BigOperators Classical

theorem treeIntegerResidues_prime_sample (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafTuple P n) :
    treeIntegerResidues Q n
      (treeLeafMap (fun p : P => ((p : ℕ) : ℤ)) n x)
      (treeLeafMap (fun p : P => ZMod.unitOfCoprime (p : ℕ) (hunit p)) n x) := by
  induction n with
  | zero =>
    simpa only [treeIntegerResidues, treeLeafMap, Int.cast_natCast] using
      ZMod.coe_unitOfCoprime (n := Q) (Subtype.val (show P from x)) (hunit x)
  | succ n ih => exact ⟨ih x.1, ih x.2⟩

noncomputable def sampledPrimeHistory (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (pivots : Fin (2 ^ n - 1) → ℤ) : SampledPivotHistory n Q where
  bulk := treeLeafMap (fun p : P => ((p : ℕ) : ℤ)) n ((treeLeafTupleEquiv P n).symm x)
  residue := treeLeafMap (fun p : P => ZMod.unitOfCoprime (p : ℕ) (hunit p)) n
    ((treeLeafTupleEquiv P n).symm x)
  pivots := pivots
  compatible := treeIntegerResidues_prime_sample P Q n hunit _

theorem sampledPrimeHistory_residue (P : Finset ℕ) (Q n : ℕ)
    (hunit : ∀ p : P, (p : ℕ).Coprime Q) (x : TreeLeafIndex n → P)
    (pivots : Fin (2 ^ n - 1) → ℤ) :
    (sampledPrimeHistory P Q n hunit x pivots).residue =
      (treeLeafTupleEquiv (ZMod Q)ˣ n).symm (fun i => ZMod.unitOfCoprime (x i : ℕ) (hunit (x i))) := by
  apply (treeLeafTupleEquiv (ZMod Q)ˣ n).injective
  funext i
  simp only [sampledPrimeHistory, treeLeafTupleEquiv_map, Equiv.apply_symm_apply]

/-- No new support probability is assumed: it is computed from the literal
integer reversal equations of each nonzero sampled history. -/
theorem sampled_history_square_sum_le (P : Finset ℕ) (S : Finset ℤ) (V n k : ℕ)
    (R : FrequencyTree S n → ℕ) [∀ t, NeZero (R t ^ (k + 2))]
    (D : FrequencyTree S n → PivotDependencyScheme (2 ^ n - 1))
    (hdepth : ∀ t i, (D t).depth i ≤ k)
    (hs : ∀ t i, ((D t).frequencies i).root ≠ 0)
    (hsR : ∀ t i, ((D t).frequencies i).root.natAbs ∣ R t)
    (T : TreeLeafIndex n → Finset ℕ)
    (hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (R t ^ (k + 2)))
    (pivots : FrequencyTree S n → (TreeLeafIndex n → P) → Fin (2 ^ n - 1) → ℤ)
    (W : FrequencyTree S n → (TreeLeafIndex n → P) → ℂ)
    (B : ℝ) (hB : 0 ≤ B)
    (hsize : ∀ t x, ‖W t x‖ ^ 2 ≤ B * frequencyLeafWeight (singleFrequencyLeaf S V) n t)
    (hvalid : ∀ t x, W t x ≠ 0 →
      (sampledPrimeHistory P (R t ^ (k + 2)) n (hunit t) x (pivots t x)).valid (D t)) :
    (∑ t, ∑ x, (∏ i, primeSubsetPrior P (T i) (x i)) * ‖W t x‖ ^ 2) ≤
      B * harmonicHistorySupportSum P S V n (fun t => R t ^ (k + 2)) T hunit
        (fun t => adaptivePivotData n (R t) k (D t) (hs t) (hsR t)) := by
  unfold harmonicHistorySupportSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have hμ : 0 ≤ ∏ i, primeSubsetPrior P (T i) (x i) :=
    Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg P (T i) (x i))
  by_cases hw : W t x = 0
  · simp only [hw, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact mul_nonneg (mul_nonneg hB (frequencyLeafWeight_nonneg _
      (fun _ => by unfold singleFrequencyLeaf; split_ifs <;> norm_num) n t))
      (mul_nonneg hμ (singleArithmeticLeafSupport_nonneg n _ _))
  · have hp := adaptivePivotData_actual_support n (R t) k (D t) (hdepth t) (hs t) (hsR t)
      (sampledPrimeHistory P (R t ^ (k + 2)) n (hunit t) x (pivots t x)) (hvalid t x hw)
    rw [sampledPrimeHistory_residue] at hp
    rw [hp, mul_one]
    calc
      _ ≤ (∏ i, primeSubsetPrior P (T i) (x i)) *
          (B * frequencyLeafWeight (singleFrequencyLeaf S V) n t) :=
        mul_le_mul_of_nonneg_left (hsize t x) hμ
      _ = _ := by ring

end Ostmann

end OAI
