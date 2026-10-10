import OAI.Combinatorics.EditApproximation.Coarse.CoarseInputGuard

namespace OAI

namespace EditApproximation

theorem coarsePreparedSlicesWithWork_cost (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi A S : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length)
    (hsbits : Nat.size source.length ≤ A) (htbits : Nat.size target.length ≤ A)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ S) :
    (coarsePreparedSlicesWithWork source target sourceLo sourceHi targetLo targetHi).2 ≤
      1000 * (A + 1) + (3 * (sourceHi - sourceLo) + 2) * (40 * (A + 1) + S) := by
  have hg := coarseInputGuardWithWork_cost sourceLo sourceHi targetLo targetHi A
    ((Nat.size_le_size (hslo.trans hshi)).trans hsbits) ((Nat.size_le_size hshi).trans hsbits)
    ((Nat.size_le_size (htlo.trans hthi)).trans htbits) ((Nat.size_le_size hthi).trans htbits)
  by_cases hlong : 2 * (sourceHi - sourceLo) < targetHi - targetLo
  · simp only [coarsePreparedSlicesWithWork, coarseInputGuardWithWork_value, hlong, decide_true, ite_true]
    exact hg.trans (Nat.le_add_right _ _)
  · have hs := coarseRangeCopyWithWork_input_cost source sourceLo sourceHi A S hslo hshi hsbits
      (fun a ha => hsymbol a (List.mem_append_left target ha))
    have ht := coarseRangeCopyWithWork_input_cost target targetLo targetHi A S htlo hthi htbits
      (fun a ha => hsymbol a (List.mem_append_right source ha))
    simp only [coarsePreparedSlicesWithWork, coarseInputGuardWithWork_value, hlong, decide_false, Bool.false_eq_true, ite_false]
    have hm := Nat.mul_le_mul_right (40 * (A + 1) + S)
      (show (sourceHi - sourceLo + 1) + (targetHi - targetLo + 1) ≤
        3 * (sourceHi - sourceLo) + 2 by omega)
    nlinarith only [hg, hs, ht, hm]

theorem coarsePreparedSlicesWithWork_height_bound (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi H : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length)
    (hH : 100 ≤ H) (hsbits : Nat.size source.length ≤ H ^ 3)
    (htbits : Nat.size target.length ≤ H ^ 3)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ H ^ 3) :
    (coarsePreparedSlicesWithWork source target sourceLo sourceHi targetLo targetHi).2 ≤
      H ^ 6 * (sourceHi - sourceLo + 1) := by
  have hc := coarsePreparedSlicesWithWork_cost source target sourceLo sourceHi targetLo targetHi
    (H ^ 3) (H ^ 3) hslo hshi htlo hthi hsbits htbits hsymbol
  have hp : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
  have hs : 5000 ≤ H ^ 3 := by
    have h := Nat.pow_le_pow_left hH 3
    norm_num at h
    omega
  have hm : 5000 * H ^ 3 ≤ H ^ 6 := by
    calc
      _ ≤ H ^ 3 * H ^ 3 := Nat.mul_le_mul_right _ hs
      _ = _ := by rw [← pow_add]
  have hmul := Nat.mul_le_mul_right (sourceHi - sourceLo + 1) hm
  nlinarith only [hc, hp, hmul, Nat.zero_le (sourceHi - sourceLo)]

end EditApproximation

end OAI
