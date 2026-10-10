import OAI.NumberTheory.Ostmann.Construction.CanonicalFrame
import OAI.NumberTheory.Ostmann.Construction.JoinedRemaining
import OAI.NumberTheory.Ostmann.Construction.PivotFrequencyReindex

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

def joinedNumerator (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x y : RemainingSample sources T giant) (v w : ℤ) : ℤ :=
  Arithmetic.reversalNumerator v w (remainingProduct sources T giant x:ℤ)
    (remainingProduct sources T giant y:ℤ)

theorem canonicalFrame_joined (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (giant : PrimeSource) (l : ℕ)
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (s : ℤ) (v w : AllowedFrequency V l)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l))) :
    let T := Template.current seed l
    let us := assignedSlots sources (Template.extracted (l+1) T) u
    let hp := assignedSlots sources (Template.remainder (l+1) T) x.2
    let hm := assignedSlots sources (Template.remainder (l+1) T) y.2
    let a := joinedRemainingState sources (Template.remainder (l+1) T) giant x y s
    let p := reversalPivot (joinedNumerator sources (Template.remainder (l+1) T) giant x y v.val w.val)
      (us.map SmallSlot.value).prod s
    canonicalFrame sources seed V l a v w u=
      ⟨a,p,us,hp,hm,remainingState sources T (l+1) giant p u x v.val,
        remainingState sources T (l+1) giant p u y w.val⟩ := by
  have hx := assignedSlots_length sources (Template.remainder (l+1) (Template.current seed l)) x.2
  dsimp only
  unfold canonicalFrame
  dsimp only [joinedRemainingState]
  rw [←hx,List.take_left,List.drop_left]
  rfl

end Ostmann.Construction

end

end OAI
