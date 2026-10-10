import OAI.NumberTheory.Ostmann.Construction.ConstituentUniqueRootEnergy
import OAI.NumberTheory.Ostmann.Construction.FullWeightFrequencies

namespace OAI

/-! # Every live final term has nonzero frequencies, including at its leaves -/
namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem constituentPrimeTerm_nonzero_frequencies {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hXlo : 1 < X * lo)
    (center : ∀ p : ℕ, ZMod p) (t : FrequencyTree ℤ n)
    (q : SurvivingConstituent role size n → P)
    (hq : constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) center t q ≠ 0) :
    NonzeroInternalFrequencies n t ∧ ∀ a ∈ allFrequencyList n t, a ≠ 0 := by
  have hv := constituentPrimeTerm_nonzero_valid role size χ κ pivot n P hP childBound
    pivotBound ranges (scheduleFourierLeaf role ψ X lo hi) center t q hq
  refine ⟨hv.nonzero_internal _ _ _ _, ?_⟩
  have hw := (mul_ne_zero_iff.mp hq).1
  exact fullAtomFourierWeight_all_frequencies_ne_zero role childBound pivotBound ranges
    ψ X lo hi hX hXlo n _ t hw

theorem finite_frequency_range_data (P : Finset ℕ) (hP : P.Nonempty) (R : ℝ) (V : ℕ)
    (hlarge : ∀ p ∈ P, V < p) (hupper : ∀ p ∈ P, (p : ℝ) ≤ R)
    (n : ℕ) (t : FrequencyTree ℤ n)
    (hz : ∀ a ∈ allFrequencyList n t, a ≠ 0)
    (hfreq : ∀ a ∈ allFrequencyList n t, a.natAbs ≤ V) :
    (∀ p ∈ P, ∀ a ∈ allFrequencyList n t, 0 < a.natAbs ∧ a.natAbs < p) ∧
      ∀ a ∈ allFrequencyList n t, |(a : ℝ)| ≤ R := by
  constructor
  · intro p hp a ha
    exact ⟨Int.natAbs_pos.mpr (hz a ha), (hfreq a ha).trans_lt (hlarge p hp)⟩
  · intro a ha
    obtain ⟨p, hp⟩ := hP
    have hh : (a.natAbs : ℝ) ≤ R :=
      (Nat.cast_le.mpr (hfreq a ha)).trans ((Nat.cast_le.mpr (hlarge p hp).le).trans (hupper p hp))
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh

end Ostmann

end OAI
