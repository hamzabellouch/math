import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSourceCost
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupKeyCost
import OAI.Combinatorics.EditApproximation.Queries.QuerySourceBufferBounds

namespace OAI

namespace EditApproximation

theorem groupScalarKeys_fst_mem (M F Q : ℕ) (groups : List (ℕ × (ℕ × ℕ)))
    (key : GroupScalarKey M F Q) (hk : key ∈ groupScalarKeys M F Q groups) : key.1 ∈ groups := by
  obtain ⟨group, hg, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨scale, _, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨sample, _, rfl⟩ := List.mem_map.mp hk
  exact hg

namespace BinaryFraction

theorem queryGroupKeySize_bound {n : ℕ} (M N F Q exponent eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hes : 7 + eM + eF ≤ B) (he : exponent + 1 ≤ B)
    (hn : Nat.size n ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value)
    (key : GroupScalarKey M F Q)
    (hk : key.1 ∈ (queryGroupKeysWithWork N F exponent a value q).1) :
    queryGroupKeySize key ≤ 40 * B + 500 := by
  have hFpos : 1 ≤ F := by rw [hFdef]; exact Nat.succ_le_of_lt (Nat.two_pow_pos _)
  have hk' := (queryGroupKeysWithWork_bounds N F exponent B a value q hB hN hF hFpos he hn ha hv hw).2.2 key.1 hk
  obtain ⟨hb, ⟨eb, heb⟩, hleft, hright⟩ := hk'
  have hlen : (groupDyadicScales M key.1.1 F).length = 7 + eM + eF := by
    have h := congrArg List.length (computedGroupScales_value M key.1.1 F eM eb eF hMdef heb hFdef)
    simpa only [List.length_map, groupScalesWithWork_length, nat_value] using h.symm
  have hscale : Nat.size key.2.1.val ≤ B := by
    have hv' : key.2.1.val ≤ B := by
      have hi : key.2.1.val < (groupDyadicScales M key.1.1 F).length := key.2.1.isLt
      have hl : (groupDyadicScales M key.1.1 F).length ≤ B := by rw [hlen]; exact hes
      exact (Nat.le_of_lt hi).trans hl
    exact (Nat.size_le_size hv').trans (Nat.size_le.mpr (Nat.lt_two_pow_self))
  have hsample : Nat.size key.2.2.val ≤ B := by
    have hi := key.2.2.isLt
    have hc : groupSampleCount M Q key.1.1 (groupDyadicScaleAt M key.1.1 F key.2.1) ≤ M := Nat.min_le_left _ _
    exact (Nat.size_le_size (show key.2.2.val ≤ M by omega)).trans hM
  unfold queryGroupKeySize
  omega

theorem queryGroupSourceKeysWithWork_width {n : ℕ} (M N F Q exponent eM eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (a value : BinaryFraction) (q : TargetInterval n)
    (hB : 7 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hes : 7 + eM + eF ≤ B) (he : exponent + 1 ≤ B)
    (hn : Nat.size n ≤ B) (ha : a.width ≤ B) (hv : value.width ≤ B) (hw : 0 ≤ value.value) :
    ∀ key ∈ (queryGroupSourceKeysWithWork M N F Q exponent eM eF hMdef hFdef a value q).1,
      queryGroupKeySize key ≤ 40 * B + 500 := by
  intro key hk
  rw [queryGroupSourceKeysWithWork_value] at hk
  apply queryGroupKeySize_bound M N F Q exponent eM eF B hMdef hFdef a value q
    hB hN hF hM hes he hn ha hv hw key
  rw [queryGroupKeysWithWork_value]
  exact groupScalarKeys_fst_mem M F Q _ key hk

end BinaryFraction
end EditApproximation

end OAI
