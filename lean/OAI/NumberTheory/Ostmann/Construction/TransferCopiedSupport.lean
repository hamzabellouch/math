import OAI.NumberTheory.Ostmann.Construction.TransferCompletePhase
import OAI.NumberTheory.Ostmann.Construction.TransferOutputSupport

namespace OAI

/-! # The copied tuple inherits exactly the support required by the phase identity -/

namespace Ostmann

open scoped BigOperators

theorem transferredLabels_pairwise {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    (hL : Pairwise (fun h k => (L h).Coprime (L k)))
    (hR : Pairwise (fun h k => (R h).Coprime (R k)))
    (hU : Pairwise (fun y z => (U y).Coprime (U z)))
    (hLR : (∏ h, L h).Coprime (∏ h, R h))
    (hLU : (∏ h, L h).Coprime (∏ y, U y))
    (hRU : (∏ h, R h).Coprime (∏ y, U y)) :
    Pairwise (fun i j => (transferredLabels L R U i).Coprime (transferredLabels L R U j)) := by
  have hLR' (h k : H) : (L h).Coprime (R k) :=
    (hLR.coprime_dvd_left (Finset.dvd_prod_of_mem L (Finset.mem_univ h))).coprime_dvd_right
      (Finset.dvd_prod_of_mem R (Finset.mem_univ k))
  have hLU' (h : H) (y : Y) : (L h).Coprime (U y) :=
    (hLU.coprime_dvd_left (Finset.dvd_prod_of_mem L (Finset.mem_univ h))).coprime_dvd_right
      (Finset.dvd_prod_of_mem U (Finset.mem_univ y))
  have hRU' (h : H) (y : Y) : (R h).Coprime (U y) :=
    (hRU.coprime_dvd_left (Finset.dvd_prod_of_mem R (Finset.mem_univ h))).coprime_dvd_right
      (Finset.dvd_prod_of_mem U (Finset.mem_univ y))
  intro i j hij
  cases i with
  | inl i =>
    obtain ⟨ti, h⟩ := i
    cases j with
    | inl j =>
      obtain ⟨tj, k⟩ := j
      cases ti <;> cases tj
      · exact hR (by simpa using hij)
      · exact (hLR' k h).symm
      · exact hLR' h k
      · exact hL (by simpa using hij)
    | inr y =>
      cases ti
      · exact hRU' h y
      · exact hLU' h y
  | inr y =>
    cases j with
    | inl j =>
      obtain ⟨t, h⟩ := j
      cases t
      · exact (hRU' h y).symm
      · exact (hLU' h y).symm
    | inr z => exact hU (by simpa using hij)

theorem transferredLabels_pivot_coprime {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ) (M : ℕ)
    (hL : M.Coprime (∏ h, L h)) (hR : M.Coprime (∏ h, R h))
    (hU : M.Coprime (∏ y, U y)) :
    ∀ i, M.Coprime (transferredLabels L R U i) := by
  intro i
  cases i with
  | inl i =>
    obtain ⟨t, h⟩ := i
    cases t
    · exact hR.coprime_dvd_right (Finset.dvd_prod_of_mem R (Finset.mem_univ h))
    · exact hL.coprime_dvd_right (Finset.dvd_prod_of_mem L (Finset.mem_univ h))
  | inr y => exact hU.coprime_dvd_right (Finset.dvd_prod_of_mem U (Finset.mem_univ y))

theorem prime_large_frequency_unit {p : ℕ} [Fact p.Prime] (s : ℤ)
    (hs : s ≠ 0) (hlarge : s.natAbs < p) : IsUnit (s : ZMod p) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd s p).mp hz
  have hle := Int.natAbs_le_of_dvd_ne_zero hd hs
  simp only [Int.natAbs_natCast] at hle
  exact (not_le_of_gt hlarge) hle

theorem transferredLabels_frequency_unit {H Y : Type*}
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (s : ℤ) (hs : s ≠ 0)
    (hL : ∀ h, s.natAbs < L h) (hR : ∀ h, s.natAbs < R h) (hU : ∀ y, s.natAbs < U y) :
    ∀ i, IsUnit (s : ZMod (transferredLabels L R U i)) := by
  intro i
  cases i with
  | inl i =>
    obtain ⟨t, h⟩ := i
    cases t
    · exact prime_large_frequency_unit (p := R h) s hs (hR h)
    · exact prime_large_frequency_unit (p := L h) s hs (hL h)
  | inr y => exact prime_large_frequency_unit (p := U y) s hs (hU y)

end Ostmann

end OAI
