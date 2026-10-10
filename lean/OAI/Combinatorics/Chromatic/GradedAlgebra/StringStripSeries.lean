import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNThreshold
import OAI.Combinatorics.Chromatic.QuantumTorus.StringStripDimension

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S → ℕ) (t : S → ℕ) (dim : S → (I → ℕ)) (k : S → ℤ)
variable (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
variable (he : ∀d,Admissible (stringEnergy a dim k d))

include hτ he in
omit [Fintype I] [DecidableEq I] in
lemma shiftedString_admissible (d : I → ℕ) :
    Admissible (stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d) :=
  admissible_injective (admissible_shift (he d) (2*τ d)) id Function.injective_id
    (fun x=>(stringEnergy_shift a t dim τ hτ k d x).symm)

include hτ he in
omit [Fintype I] [DecidableEq I] in
lemma stripEnergy_admissible (d : I → ℕ) : Admissible (stripEnergy a t dim k d) :=
  admissible_injective (shiftedString_admissible a t dim k τ hτ he d)
    (stripInsert a t dim d) (stripInsert_injective a t dim d) (stripInsert_energy a t dim k d)

def stripSeries (d : I → ℕ) : LaurentSeries ℚ :=
  series _ (stripEnergy_admissible a t dim k τ hτ he d)

include hτ he in
lemma stringStrip_series (d : I → ℕ) :
    series (stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d)
      (shiftedString_admissible a t dim k τ hτ he d)=
      ∑s : DimensionSplit d,stripSeries a t dim k τ hτ he s.left*
        series (stringEnergy a dim k s.right) (he s.right) := by
  classical
  let f (s : DimensionSplit d) (p : StripCounts a t dim s.left × StringCounts a dim s.right) :=
    stripEnergy a t dim k s.left p.1+stringEnergy a dim k s.right p.2
  have hf : ∀s,Admissible (f s) := fun s=>admissible_prod
    (stripEnergy_admissible a t dim k τ hτ he s.left) (he s.right)
  rw [series_equiv (shiftedString_admissible a t dim k τ hτ he d)
    (admissible_sigma f hf) (stringStripDimensionEquiv a t dim d)
    (fun x=>(stringStripDimension_energy a t dim k d x).symm),series_sigma f hf]
  apply Finset.sum_congr rfl
  intro s hs
  exact (series_mul (stripEnergy_admissible a t dim k τ hτ he s.left) (he s.right)).symm

include hτ he in

theorem stringStrip_scaled (d : I → ℕ) :
    series (stringEnergy a dim k d) (he d)*HahnSeries.single (-(2*τ d)) (1:ℚ)=
      ∑s : DimensionSplit d,stripSeries a t dim k τ hτ he s.left*
        series (stringEnergy a dim k s.right) (he s.right) := by
  rw [←series_shift]
  have H : (fun x : StringCounts a dim d=>stringEnergy a dim k d x+2*τ d)=
      stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d :=
    funext (fun x=>(stringEnergy_shift a t dim τ hτ k d x).symm)
  simp only [H]
  exact stringStrip_series a t dim k τ hτ he d

end
end ElementaryPositivity.UnitSelections

end

end OAI
