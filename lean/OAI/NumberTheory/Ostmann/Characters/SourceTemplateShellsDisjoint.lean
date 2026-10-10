import OAI.NumberTheory.Ostmann.Characters.SourceTemplateShells

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template HigherBiasSourceWord HigherBiasSourceRoleBounds
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem configurationPrimeShells_nonword_eq_cell {k Q : ℕ} (cfg : SourceConfiguration k)
    (m : ℕ) (bulk top E : Finset (PrimeUpTo Q))
    (i : SourceConstituent cfg m) (hi : (schedule k 0).role i.1 ≠ .word) :
    ∃ a,configurationPrimeShells cfg m bulk top E i = configurationCells E cfg a := by
  rcases i with ⟨⟨r,b⟩,a⟩
  unfold configurationPrimeShells
  erw [sourcePrimeShells_half]
  cases r with
  | word => exact False.elim (hi rfl)
  | anchor j big =>
    refine ⟨cellCoordinateEquiv cfg (.inl (anchorCoordinate j big)),?_⟩
    exact Fin.append_right _ _ _
  | pivot j =>
    refine ⟨cellCoordinateEquiv cfg (.inr ⟨j.castSucc,Fin.cast (sourceWidth_pivot cfg m j) a⟩),?_⟩
    exact Fin.append_right _ _ _
  | filler =>
    refine ⟨cellCoordinateEquiv cfg (.inr ⟨Fin.last k,a⟩),?_⟩
    exact Fin.append_right _ _ _

theorem scheduledPrimeShells_nonword_eq_cell {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (bulk top E : Finset (PrimeUpTo Q))
    (i : (schedule k j).Constituent (sourceWidth cfg m))
    (hi : (schedule k j).role i.1 ≠ .word) :
    ∃ a,scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j i =
      configurationCells E cfg a := by
  rw [scheduledPrimeShells_eq_origin]
  apply configurationPrimeShells_nonword_eq_cell cfg m bulk top E
  rw [scheduledConstituentOrigin_role]
  exact hi

theorem scheduledPrimeShells_nonword_disjoint {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (bulk top E : Finset (PrimeUpTo Q))
    (hc : ∀ a,Disjoint (configurationCells E cfg a) bulk)
    (i : (schedule k j).Constituent (sourceWidth cfg m))
    (hi : (schedule k j).role i.1 ≠ .word) :
    Disjoint (scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j i) bulk := by
  obtain ⟨a,ha⟩ := scheduledPrimeShells_nonword_eq_cell cfg m j bulk top E i hi
  rw [ha]
  exact hc a

theorem scheduledPrimeShells_word_top {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (bulk top E : Finset (PrimeUpTo Q))
    (i : (schedule k j).Constituent (sourceWidth cfg m))
    (hi : (schedule k j).role i.1 = .word) (ha : m ≤ i.2.val) :
    scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) j i = top := by
  rcases i with ⟨i,a⟩
  rw [scheduledPrimeShells_word cfg m j bulk top E i hi a]
  change m ≤ a.val at ha
  have hav : a.val = m := by
    have ht : a.val < m+1 := by simpa only [hi,sourceWidth_word] using a.isLt
    omega
  have hf : (⟨a.val,by simpa only [hi,sourceWidth_word] using a.isLt⟩ : Fin (m+1)) =
      Fin.natAdd m (0:Fin 1) := by apply Fin.ext; simpa using hav
  rw [hf,roleShells,Fin.append_right]

theorem scheduledPrimeShells_nonbulk_disjoint {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (bulk top E : Finset (PrimeUpTo Q))
    (hc : ∀ a,Disjoint (configurationCells E cfg a) bulk) (ht : Disjoint top bulk)
    (i : (schedule k j).Constituent (sourceWidth cfg m))
    (hi : (schedule k j).role i.1 ≠ .word ∨ m ≤ i.2.val) :
    Disjoint (scheduledPrimeShells k (sourceWidth cfg m)
      (configurationPrimeShells cfg m bulk top E) j i) bulk := by
  by_cases hw : (schedule k j).role i.1 = .word
  · rw [scheduledPrimeShells_word_top cfg m j bulk top E i hw (hi.resolve_left (not_not.mpr hw))]
    exact ht
  · exact scheduledPrimeShells_nonword_disjoint cfg m j bulk top E hc i hw

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
