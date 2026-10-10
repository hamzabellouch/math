import OAI.Algebra.Finitistic.Selected.SelectedFiniteAmplitude
import OAI.Algebra.Finitistic.Bar.IntegerCountObject
import OAI.Algebra.Finitistic.Iteration.BinomialVanishing

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.SelectedCountCohomology
open SelectedOrdinaryAlgebra SelectedBaseIterates
local instance : HasDerivedCategory.{1} (ModuleCat.{0} D) :=
  HasDerivedCategory.standard (ModuleCat.{0} D)

/-- The original summand with exactly r square-zero factors in the actual bar complex. -/
abbrev count (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :=
  DerivedBar.ParityBridge.countObject ℂ D X (input Y) r

/-- Its exact standard integer-shift identification with the genuine derived iterate. -/
def comparison (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (object Y r)⟦(r : ℤ)⟧ ≅ count Y r :=
  DerivedBar.ParityBridge.countObjectComparison ℂ D X (input Y) r

theorem isZero_iff (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    IsZero (count Y r) ↔ IsZero (object Y r) :=
  (comparison Y r).isZero_iff.symm.trans
    (ExternalTensor.Binomial.isZero_shift_iff (object Y r) (r : ℤ))

theorem bounded (Y : FiniteSelectionFamily.S.{0}) (r : ℕ) :
    (count Y r).IsGE (-((r * (3 * length + 5) : ℕ) : ℤ)) ∧
    (count Y r).IsLE (-(r : ℤ)) := by
  have := (SelectedFiniteAmplitude.bounded Y r).1
  have := (SelectedFiniteAmplitude.bounded Y r).2
  have : ((object Y r)⟦(r : ℤ)⟧).IsGE (-((r * (3 * length + 5) : ℕ) : ℤ)) := by
    apply DerivedCategory.TStructure.t.isGE_shift (object Y r)
      (-((r * (3 * length + 4) : ℕ) : ℤ)) (r : ℤ)
      (-((r * (3 * length + 5) : ℕ) : ℤ)) ?_
    push_cast
    ring
  have : ((object Y r)⟦(r : ℤ)⟧).IsLE (-(r : ℤ)) :=
    DerivedCategory.TStructure.t.isLE_shift (object Y r) 0 (r : ℤ) (-(r : ℤ)) (by omega)
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso (comparison Y r) _,
    DerivedCategory.TStructure.t.isLE_of_iso (comparison Y r) _⟩

/-- Every surviving iterate contributes a nonzero original count class in a
homological degree at least r, with an explicit finite upper bound. -/
theorem nonzero_degree (Y : FiniteSelectionFamily.S.{0}) (r : ℕ)
    (h : ¬ IsZero (object Y r)) :
    ∃ n : ℕ, r ≤ n ∧ n ≤ r * (3 * length + 5) ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj (count Y r)) := by
  have := (bounded Y r).1
  have := (bounded Y r).2
  by_contra hn
  push Not at hn
  have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) i).obj (count Y r)) := by
    by_cases hi : i ≤ 0
    · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
      by_cases hlo : r ≤ n
      · by_cases hhi : n ≤ r * (3 * length + 5)
        · exact hn n hlo hhi
        · exact DerivedCategory.isZero_of_isGE _ (-((r * (3 * length + 5) : ℕ) : ℤ))
            (-(n : ℤ)) (by omega)
      · exact DerivedCategory.isZero_of_isLE _ (-(r : ℤ)) (-(n : ℤ)) (by omega)
    · exact DerivedCategory.isZero_of_isLE _ (-(r : ℤ)) i (by omega)
  have : (count Y r).IsLE (-1) := (DerivedCategory.isLE_iff _ _).mpr (fun i _ => hz i)
  have : (count Y r).IsGE 0 := (DerivedCategory.isGE_iff _ _).mpr (fun i _ => hz i)
  apply h
  apply (isZero_iff Y r).mp
  apply (IsZero.iff_id_eq_zero _).mpr
  exact DerivedCategory.TStructure.t.zero (𝟙 _) (-1) 0 (by omega)
end LittleFinitistic.SelectedCountCohomology

end

end OAI
