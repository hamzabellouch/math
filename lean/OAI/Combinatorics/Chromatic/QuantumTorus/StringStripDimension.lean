import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.DimensionGrid
import OAI.Combinatorics.Chromatic.Shuffle.SymmetricSpace
import OAI.Combinatorics.Chromatic.Walls.StringStrip

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle
noncomputable section
variable {S I : Type*} (a : S → ℕ) (t : S → ℕ) (dim : S → (I → ℕ))

abbrev StringCounts (d : I → ℕ) :=
  DimensionCounts (fun x : S×ℕ=>a x.1≠0) (fun x=>dim x.1) d
abbrev StripCounts (d : I → ℕ) :=
  DimensionCounts (fun x : HeadLevel t=>a x.1≠0) (fun x=>dim x.1) d

def stringStripDimensionEquiv (d : I → ℕ) :
    StringCounts a dim d ≃ Σs : DimensionSplit d,StripCounts a t dim s.left × StringCounts a dim s.right :=
  ((stringStripEquiv a t).subtypeEquiv (fun _=>by
    rw [countDimension,stringStrip_dimension]
    rfl)).trans (dimensionProduct (countDimension _ (fun x : HeadLevel t=>dim x.1))
      (countDimension _ (fun x : S×ℕ=>dim x.1)) d).symm

def stringEnergy (k : S → ℤ) (d : I → ℕ) (x : StringCounts a dim d) : ℤ :=
  countEnergy _ (fun x=>k x.1-2*(x.2:ℤ)) x.val

def stripEnergy (k : S → ℤ) (d : I → ℕ) (x : StripCounts a t dim d) : ℤ :=
  countEnergy _ (fun x=>k x.1+2*(t x.1:ℤ)-2*(x.2.val:ℤ)) x.val

lemma stringStripDimension_energy (k : S → ℤ) (d : I → ℕ) (x : StringCounts a dim d) :
    stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d x=
      stripEnergy a t dim k (stringStripDimensionEquiv a t dim d x).1.left
        (stringStripDimensionEquiv a t dim d x).2.1+
      stringEnergy a dim k (stringStripDimensionEquiv a t dim d x).1.right
        (stringStripDimensionEquiv a t dim d x).2.2 :=
  stringStrip_energy a t k x.val

lemma stringEnergy_shift (τ : (I→ℕ) →+ ℤ) (hτ : ∀s,(t s:ℤ)=τ (dim s))
    (k : S → ℤ) (d : I → ℕ) (x : StringCounts a dim d) :
    stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d x=
      stringEnergy a dim k d x+2*τ d := by
  have H : (fun x : S×ℕ=>k x.1+2*(t x.1:ℤ)-2*(x.2:ℤ))=
      (fun x=>k x.1-2*(x.2:ℤ)+(2 • τ) (dim x.1)) := by
    funext x
    rw [hτ]
    simp only [AddMonoidHom.nsmul_apply,nsmul_eq_mul]
    ring
  change countEnergy _ _ x.val=_
  rw [H,countEnergy_shift,x.property]
  rfl

def stripInsert (d : I → ℕ) (x : StripCounts a t dim d) : StringCounts a dim d :=
  ⟨(stringStripEquiv a t).symm (x.val,zeroCount _),by
    change (_:S×ℕ→₀ℕ).sum _=d
    rw [stringStrip_dimension a t dim]
    simp only [Equiv.apply_symm_apply,zeroCount,Finsupp.sum_zero_index,add_zero]
    exact x.property⟩

lemma stripInsert_injective (d : I → ℕ) : Function.Injective (stripInsert a t dim d) := by
  intro x y H
  apply Subtype.ext
  have H':=congrArg (fun z : StringCounts a dim d=> (stringStripEquiv a t z.val).1) H
  simpa only [stripInsert,Equiv.apply_symm_apply] using H'

lemma stripInsert_energy (k : S → ℤ) (d : I → ℕ) (x : StripCounts a t dim d) :
    stringEnergy a dim (fun s=>k s+2*(t s:ℤ)) d (stripInsert a t dim d x)=
      stripEnergy a t dim k d x := by
  change ((stringStripEquiv a t).symm (x.val,zeroCount _)).val.sum
    (fun z n=>n • (k z.1+2*(t z.1:ℤ)-2*(z.2:ℤ)))=_
  rw [stringStrip_energy a t k]
  simp only [Equiv.apply_symm_apply,zeroCount,Finsupp.sum_zero_index,add_zero]
  rfl

end
end ElementaryPositivity.UnitSelections

end

end OAI
