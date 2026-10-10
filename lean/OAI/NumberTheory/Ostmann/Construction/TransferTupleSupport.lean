import OAI.NumberTheory.Ostmann.Construction.TransferAdditiveProduct

namespace OAI

/-! # Local denominator units from the actual output tuple's coprimality -/

namespace Ostmann

open scoped BigOperators

theorem transferred_left_denominators {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (h : H) : (∏ k, R k).Coprime (L h) ∧
      (tupleCofactor L h * ∏ y, U y).Coprime (L h) := by
  have hR : (L h).Coprime (∏ k, R k) := Nat.coprime_prod_right_iff.mpr (by
    intro k _
    exact @hc (.inl (true, h)) (.inl (false, k)) (by simp))
  have hU : (L h).Coprime (∏ y, U y) := Nat.coprime_prod_right_iff.mpr (by
    intro y _
    exact @hc (.inl (true, h)) (.inr y) (by simp))
  have hL : Pairwise (fun h k => (L h).Coprime (L k)) := by
    intro h k hhk
    exact @hc (.inl (true, h)) (.inl (true, k)) (by simpa using hhk)
  exact ⟨hR.symm, (tupleCofactor_coprime L hL h).mul_left hU.symm⟩

theorem transferred_right_denominators {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (h : H) : (∏ k, L k).Coprime (R h) ∧
      (tupleCofactor R h * ∏ y, U y).Coprime (R h) := by
  have hL : (R h).Coprime (∏ k, L k) := Nat.coprime_prod_right_iff.mpr (by
    intro k _
    exact @hc (.inl (false, h)) (.inl (true, k)) (by simp))
  have hU : (R h).Coprime (∏ y, U y) := Nat.coprime_prod_right_iff.mpr (by
    intro y _
    exact @hc (.inl (false, h)) (.inr y) (by simp))
  have hR : Pairwise (fun h k => (R h).Coprime (R k)) := by
    intro h k hhk
    exact @hc (.inl (false, h)) (.inl (false, k)) (by simpa using hhk)
  exact ⟨hL.symm, (tupleCofactor_coprime R hR h).mul_left hU.symm⟩

theorem transferred_outside_denominators {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    (hc : Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)))
    (y : Y) : (∏ h, L h).Coprime (U y) ∧ (∏ h, R h).Coprime (U y) ∧
      (tupleCofactor U y).Coprime (U y) := by
  have hL : (U y).Coprime (∏ h, L h) := Nat.coprime_prod_right_iff.mpr (by
    intro h _
    exact @hc (.inr y) (.inl (true, h)) (by simp))
  have hR : (U y).Coprime (∏ h, R h) := Nat.coprime_prod_right_iff.mpr (by
    intro h _
    exact @hc (.inr y) (.inl (false, h)) (by simp))
  have hU : Pairwise (fun y z => (U y).Coprime (U z)) := by
    intro y z hyz
    exact @hc (.inr y) (.inr z) (by simpa using hyz)
  exact ⟨hL.symm, hR.symm, tupleCofactor_coprime U hU y⟩

end Ostmann

end OAI
