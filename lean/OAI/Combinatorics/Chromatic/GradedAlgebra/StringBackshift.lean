import Mathlib
import OAI.Combinatorics.Chromatic.Walls.StringPositiveFactor

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WallUnits WeightedTorusSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I→ℕ)) (k : S → ℤ)
variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
variable (he : ∀d,Admissible (stringEnergy a dim k d))

omit [Fintype I] [DecidableEq I] in
include hτ in
lemma stringEnergy_backshift (d : I→ℕ) (x : StringCounts a dim d) :
    stringEnergy a dim (fun s=>k s-2*(t s:ℤ)) d x=
      stringEnergy a dim k d x-2*τ d := by
  have H:=stringEnergy_shift a t dim τ hτ (fun s=>k s-2*(t s:ℤ)) d x
  have hk : (fun s=>k s-2*(t s:ℤ)+2*(t s:ℤ))=k := by funext s; ring
  rw [hk] at H
  omega

omit [Fintype I] [DecidableEq I] in
include hτ he in
lemma backshiftString_admissible (d : I→ℕ) :
    Admissible (stringEnergy a dim (fun s=>k s-2*(t s:ℤ)) d) :=
  admissible_injective (admissible_shift (he d) (-(2*τ d))) id Function.injective_id
    (fun x=>by simpa only [sub_eq_add_neg,id_eq,Equiv.refl_apply] using
      (stringEnergy_backshift a t dim k τ hτ d x).symm)

omit [Fintype I] [DecidableEq I] in
include hτ he in
lemma backshiftString_series (d : I→ℕ) :
    stringSeries a dim (fun s=>k s-2*(t s:ℤ))
      (backshiftString_admissible a t dim k τ hτ he) d=
    stringSeries a dim k he d*HahnSeries.single (2*τ d) (1:ℚ) := by
  rw [stringSeries,stringSeries,←neg_neg (2*τ d),←series_shift]
  apply series_equiv _ _ (Equiv.refl _)
  intro x
  exact (by simpa only [sub_eq_add_neg,id_eq,Equiv.refl_apply] using (stringEnergy_backshift a t dim k τ hτ d x).symm)

include hτ he in
lemma backstripString_series (d : I→ℕ) :
    stringSeries a dim k he d=
      ∑s : DimensionSplit d,
        stripSeries a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ
          (backshiftString_admissible a t dim k τ hτ he) s.left *
        stringSeries a dim (fun s=>k s-2*(t s:ℤ))
          (backshiftString_admissible a t dim k τ hτ he) s.right := by
  have H:=stringStrip_series a t dim (fun s=>k s-2*(t s:ℤ)) τ hτ
    (backshiftString_admissible a t dim k τ hτ he) d
  have hk : (fun s=>k s-2*(t s:ℤ)+2*(t s:ℤ))=k := by funext s; ring
  simpa only [hk,stringSeries] using H
end
end ElementaryPositivity.UnitSelections

end

end OAI
