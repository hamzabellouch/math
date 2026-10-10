import OAI.NumberTheory.Ostmann.Construction.ConstituentCoreEnergy
import OAI.NumberTheory.Ostmann.Construction.ConstituentPrimeFrequencySupport

namespace OAI

/-! # Every live matched core has the actual nonzero Fourier frequencies -/
namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

theorem constituentCharacterCore_nonzero_frequencies {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hX : 0 < X) (hXlo : 1 < X * lo)
    (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D)
    (hq : constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) hist u M (l, d) ≠ 0) :
    NonzeroInternalFrequencies n (hist d) ∧ ∀ a ∈ allFrequencyList n (hist d), a ≠ 0 := by
  have hv := constituentCharacterCore_nonzero_valid role size χ κ pivot n P hP childBound
    pivotBound ranges (scheduleFourierLeaf role ψ X lo hi) hist u M l d hq
  refine ⟨hv.nonzero_internal _ _ _ _, ?_⟩
  unfold constituentCharacterCore at hq
  have hw := (mul_ne_zero_iff.mp hq).1
  unfold constituentUnweightedTransferWeight at hw
  split_ifs at hw
  · exact fullAtomFourierWeight_all_frequencies_ne_zero role childBound pivotBound ranges
      ψ X lo hi hX hXlo n _ (hist d) hw
  · exact False.elim (hw rfl)

end Ostmann

end OAI
