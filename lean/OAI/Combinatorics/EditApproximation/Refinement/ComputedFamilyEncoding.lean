import OAI.Combinatorics.EditApproximation.Refinement.ComputedScalarCodeBits
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedEncoding
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRequestSpace
import OAI.Combinatorics.EditApproximation.Geometry.SeedFactorSchedule

namespace OAI

namespace EditApproximation

 theorem computed_physicalFamilyCode_bound (N nx ny R : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (target : List ℕ) (htarget : target.length = ny)
    (key : PhysicalFamilyScalarKey (M := (integerParameters N).M)
      (J := intervalTreeDepth (integerParameters N).M nx) (R := R)
      target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
      (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)) :
    physicalFamilyCode target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
      (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2) key <
      2 ^ (16384 * inputHeight N + 4) := by
  let H := inputHeight N
  have hH : 2 ≤ H := (by omega : 2 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hlift {e : ℕ} (he : e ≤ 64 * H) : 2 ^ e ≤ 2 ^ (64 * H) :=
    Nat.pow_le_pow_right (by decide) he
  have hp : computedSeedPassCount N + 1 ≤ 2 ^ (64 * H) :=
    ((Nat.add_le_add_right (computedSeedPassCount_le_height N hN hell) 1).trans
      (Nat.lt_two_pow_self : H < 2 ^ H)).trans (hlift (by omega))
  have hc : H ^ 2 + 1 ≤ 2 ^ (64 * H) := by
    have hh : H ^ 2 ≤ 2 ^ (2 * H) := by
      calc
        _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
        _ = _ := by rw [← pow_mul]; congr 1; omega
    calc
      _ ≤ 2 ^ (2 * H) + 2 ^ (2 * H) := Nat.add_le_add hh Nat.one_le_two_pow
      _ = 2 ^ (2 * H + 1) := by rw [pow_succ]; omega
      _ ≤ _ := hlift (by omega)
  have hscalar (scalar : PhysicalScalarKey (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) N target.length (40 * smallLogExponent N)
      (inputSmallLog N) (inputSmallLog N ^ 80) R
      (localOnlineMassBound (integerParameters N).M (integerParameters N).P H)) :
      physicalScalarCode scalar < 2 ^ (64 * (64 * H) + 1) :=
    computed_physicalScalarCode_bound N nx target.length R hN (by omega) hnx
      (by omega) hR hB scalar
  have h := physicalFamilyCode_bound (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M nx) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N) H
      (inputSmallLog N ^ 80) (computedSeedPassCount N) (H ^ 2) (64 * H) hp hc hscalar key
  convert h using 1
  congr 1
  omega

 theorem mixedCode_lt_two_pow {σ κ : Type*} (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (b : ℕ) (hs : ∀ source, sourceCode source < 2 ^ b)
    (ht : ∀ table, tableCode table < 2 ^ b) (key : Sum σ κ) :
    SourceRanked.keyCode sourceCode tableCode key < 2 ^ (b + 1) := by
  rw [pow_succ]
  cases key with
  | inl source => have h := hs source; change 2 * _ < _; omega
  | inr table => have h := ht table; change 2 * _ + 1 < _; omega

 theorem computed_mixed_cache_nodes {κ : Type*} (N : ℕ)
    (rank : κ → ℕ) (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (encode : κ → ℕ) (key : κ) :
    (rankedMemoEvaluate rank program (16384 * inputHeight N + 5) encode key .empty).memory.nodes + 1 ≤
      (N + 2) ^ 65542 := by
  have hcache := rankedMemoEvaluate_nodes_bound rank program (16384 * inputHeight N + 5) encode key
  apply hcache.trans
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith [Nat.zero_le N]
  have hbase : 2 ^ inputHeight N ≤ (N + 2) ^ 4 := by
    apply (two_pow_inputHeight_le N).trans
    calc
      _ ≤ (N + 2) ^ 2 * (N + 2) ^ 2 := Nat.mul_le_mul_right _ h4
      _ = _ := by ring
  calc
    2 ^ (16384 * inputHeight N + 5 + 1) = (2 ^ inputHeight N) ^ 16384 * 2 ^ 6 := by
      rw [show 16384 * inputHeight N + 5 + 1 = inputHeight N * 16384 + 6 by omega, pow_add, pow_mul]
    _ ≤ ((N + 2) ^ 4) ^ 16384 * (N + 2) ^ 6 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase _) (Nat.pow_le_pow_left (by omega) _)
    _ = (N + 2) ^ (4 * 16384 + 6) := by
      generalize (16384 : ℕ) = exponent
      rw [← pow_mul, ← pow_add]
    _ = (N + 2) ^ 65542 := congrArg (fun exponent : ℕ => (N + 2) ^ exponent) (by decide)

end EditApproximation

end OAI
