import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOnlineWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalRepresentativeWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalOnline

namespace OAI

/-! All selected scales execute rounding, the center guard, and the complete
sampled optimizer. The list contains at most one action per tested scale. -/

namespace EditApproximation
namespace BinaryFraction

def preparedLocalOnlineScaleBitBudget (M P B S : ℕ) : ℕ :=
  let W := B + 4
  100 * (W + 2) ^ 2 + (500 * (W + 1) ^ 2 + 1) +
    localEligibilityBitBudget W + preparedOnlineBitBudget M P W S + B + 4

def preparedLocalOnlineBitBudget (M P B S : ℕ) : ℕ :=
  queryExponentsBitBudget B + (B + 1) * (preparedLocalOnlineScaleBitBudget M P B S + 3) + 1

theorem preparedLocalOnlineScaleWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H e B E S : ℕ)
    (hPpos : 0 < P) (hMpos : 0 < M)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (heScale : e ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hdBits : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (hKBits : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B)
    (hInteger : ∀ b r, Nat.size (integer b r) ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B) (heta : eta.width ≤ B) (hkappa : kappa.width ≤ B)
    (hparent : ∀ r, (parentInitial r).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B) (hinitial : ∀ i q, (initial i q).width ≤ B)
    (htable : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (hetaValue : |eta.value| ≤ E) (hkappaValue : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hvalues : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value)
    (hS : 2 ≤ S) (hMS : M ≤ S) (hPS : P ≤ S) (hES : E ≤ S) (htS : t ≤ S)
    (hBS : 3 * (B + 4) + 4 ≤ S) (hvS : (40 * P + 2) ^ (2 * M) ≤ S)
    (hcartS : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S)
    (hKS : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S) :
    (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hPpos tau a eta kappa
      parentInitial child initial table t integer query).2 ≤ preparedLocalOnlineScaleBitBudget M P B S := by
  let W := B + 4
  let spacing := seedGridSpacingWithWork (2 ^ e) P
  let center := roundStateWithWork (bitWordValue spacing.1)
    (seedGridSpacingWithWork_pos (2 ^ e) P hPpos) query
  have hb : Nat.size (2 ^ e) + 2 ≤ W := by rw [Nat.size_pow]; dsimp only [W]; omega
  have hspacing := seedGridSpacingWithWork_bounds (2 ^ e) P W (by omega) (by dsimp only [W]; omega)
  have hspacingBits : Nat.size (bitWordValue spacing.1) ≤ W := by
    rw [seedGridSpacingWithWork_value _ _ hPpos]
    have hh : max 1 (2 ^ e / P) = 1 ∨ max 1 (2 ^ e / P) = 2 ^ e / P := max_choice _ _
    rcases hh with hh | hh
    · rw [seedGridSpacing, hh, Nat.size_one]
      dsimp only [W]
      omega
    · rw [seedGridSpacing, hh]
      exact (Nat.size_le_size (Nat.div_le_self _ _)).trans (by omega)
  have hround := roundStateWithWork_cost (bitWordValue spacing.1)
    (seedGridSpacingWithWork_pos (2 ^ e) P hPpos) query W hspacingBits (by dsimp only [W]; omega)
  have hguard := centerEligibilityWithWork_cost (2 ^ e) F W a (parentInitial center.1)
    (by dsimp only [W]; omega) hb (by dsimp only [W]; omega)
    (ha.trans (by dsimp only [W]; omega)) ((hparent _).trans (by dsimp only [W]; omega))
  have honline := preparedOnlineWithWork_cost source target parent P F exponent H (2 ^ e) W E S
    (Nat.two_pow_pos _) hPpos hMpos tau eta kappa child initial table t center.1
    (integer (2 ^ e) center.1) (by dsimp only [W]; omega)
    (by dsimp only [W]; omega) (by dsimp only [W]; omega) (by dsimp only [W]; omega)
    hb (by dsimp only [W]; omega) (by dsimp only [W]; omega) (by dsimp only [W]; omega)
    (by dsimp only [W]; omega) (by dsimp only [W]; omega) (by dsimp only [W]; omega)
    ((hInteger _ _).trans (by dsimp only [W]; omega))
    (htau.trans (by dsimp only [W]; omega)) (heta.trans (by dsimp only [W]; omega))
    (hkappa.trans (by dsimp only [W]; omega))
    (fun i q => (hchild i q).trans (by dsimp only [W]; omega))
    (fun i q => (hinitial i q).trans (by dsimp only [W]; omega))
    (fun s hs i q => (htable s hs i q).trans (by dsimp only [W]; omega))
    hetaValue hkappaValue hvalues hS hMS hPS hES htS hBS hvS hcartS hKS
  have hs : spacing.2 ≤ 100 * (W + 2) ^ 2 := hspacing.2
  have hr : center.2 ≤ 500 * (W + 1) ^ 2 + 1 := hround
  unfold preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · change spacing.2 + center.2 + (centerEligibilityWithWork (2 ^ e) F a (parentInitial center.1)).2 +
      (preparedOnlineWithWork source target parent P F exponent H (2 ^ e) (Nat.two_pow_pos e) hPpos
        tau eta kappa child initial table t center.1 (integer (2 ^ e) center.1)).2 + e + 4 ≤ _
    unfold preparedLocalOnlineScaleBitBudget
    change _ ≤ 100 * (W + 2) ^ 2 + (500 * (W + 1) ^ 2 + 1) +
      localEligibilityBitBudget W + preparedOnlineBitBudget M P W S + B + 4
    omega
  · change spacing.2 + center.2 + (centerEligibilityWithWork (2 ^ e) F a (parentInitial center.1)).2 + e + 3 ≤ _
    unfold preparedLocalOnlineScaleBitBudget
    change _ ≤ 100 * (W + 2) ^ 2 + (500 * (W + 1) ^ 2 + 1) +
      localEligibilityBitBudget W + preparedOnlineBitBudget M P W S + B + 4
    omega

theorem preparedLocalOnlineActionsWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H B E S : ℕ)
    (hPpos : 0 < P) (hMpos : 0 < M)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hdBits : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (hKBits : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B)
    (hInteger : ∀ b r, Nat.size (integer b r) ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B) (heta : eta.width ≤ B) (hkappa : kappa.width ≤ B)
    (hparent : ∀ r, (parentInitial r).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B) (hinitial : ∀ i q, (initial i q).width ≤ B)
    (htable : ∀ s ≤ t + 1, ∀ i q, (table s (i, q)).width ≤ B)
    (hetaValue : |eta.value| ≤ E) (hkappaValue : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (hvalues : ∀ s ≤ t + 1, ∀ i q, 0 ≤ (table s (i, q)).value ∧
      (table s (i, q)).value ≤ (initial i q).value)
    (hS : 2 ≤ S) (hMS : M ≤ S) (hPS : P ≤ S) (hES : E ≤ S) (htS : t ≤ S)
    (hBS : 3 * (B + 4) + 4 ≤ S) (hvS : (40 * P + 2) ^ (2 * M) ≤ S)
    (hcartS : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S)
    (hKS : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S) :
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hPpos tau a eta kappa
      parentInitial child initial table t integer query).2 ≤ preparedLocalOnlineBitBudget M P B S := by
  let scales := queryExponentsWithWork N F a (parentInitial query)
  have hs := queryExponentsWithWork_bounds N F B a (parentInitial query) hB hN hF ha (hparent query)
  have hc (e : ℕ) (heMem : e ∈ scales.1) :
      (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hPpos tau a eta kappa
        parentInitial child initial table t integer query).2 ≤ preparedLocalOnlineScaleBitBudget M P B S := by
    have heRange := heMem
    change e ∈ (queryExponentsWithWork N F a (parentInitial query)).1 at heRange
    simp only [queryExponentsWithWork, filterWithWork_value] at heRange
    have heB : e ≤ B := by
      have hh := List.mem_range.mp (List.mem_filter.mp heRange).1
      rw [Nat.size_eq_bits_len] at hh
      omega
    exact preparedLocalOnlineScaleWithWork_cost source target parent P F exponent H e B E S
      hPpos hMpos tau a eta kappa parentInitial child initial table t integer query
      hB heB hnx hny hMb hP hF he hH hdBits hKBits hInteger htau ha heta hkappa hparent
      hchild hinitial htable hetaValue hkappaValue hvalues hS hMS hPS hES htS hBS hvS hcartS hKS
  have hf := filterMapWithWork_cost
    (fun e => preparedLocalOnlineScaleWithWork source target parent P F exponent H e hPpos
      tau a eta kappa parentInitial child initial table t integer query) scales.1
    (preparedLocalOnlineScaleBitBudget M P B S) hc
  have hfc := hf.trans (Nat.mul_le_mul_right _ hs.2)
  change scales.2 + (filterMapWithWork
    (fun e => preparedLocalOnlineScaleWithWork source target parent P F exponent H e hPpos
      tau a eta kappa parentInitial child initial table t integer query) scales.1).2 + 1 ≤ _
  have hsc : scales.2 ≤ queryExponentsBitBudget B := hs.1
  unfold preparedLocalOnlineBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
