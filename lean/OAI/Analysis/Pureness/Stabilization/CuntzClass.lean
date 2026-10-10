import OAI.Analysis.Pureness.Stabilization.RankCyclic

namespace OAI
noncomputable section
open scoped ENNReal
namespace CuntzTrace
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def cuntzSetoid : Setoid (Positive A) where
  r a b := CuntzBelow a b ∧ CuntzBelow b a
  iseqv := ⟨fun a => ⟨CuntzBelow.refl a, CuntzBelow.refl a⟩,
    fun h => h.symm, fun h k => ⟨h.1.trans k.1, k.2.trans h.2⟩⟩

def CuntzClass := Quotient (cuntzSetoid A)

namespace CuntzClass
variable {A}
def mk (a : Positive A) : CuntzClass A := Quotient.mk (cuntzSetoid A) a

instance : LE (CuntzClass A) := ⟨Quotient.lift₂ CuntzBelow (by
  intro a b a' b' ha hb
  apply propext
  exact ⟨fun h => ha.2.trans (h.trans hb.1), fun h => ha.1.trans (h.trans hb.2)⟩)⟩

@[simp] theorem mk_le_mk (a b : Positive A) : mk a ≤ mk b ↔ CuntzBelow a b := Iff.rfl

instance : PartialOrder (CuntzClass A) where
  le_refl q := Quotient.inductionOn q (fun a => CuntzBelow.refl a)
  le_trans q r s := Quotient.inductionOn₃ q r s (fun a b c h k =>
    (mk_le_mk a c).mpr (((mk_le_mk a b).mp h).trans ((mk_le_mk b c).mp k)))
  le_antisymm q r := Quotient.inductionOn₂ q r (fun _ _ h k => Quotient.sound ⟨h, k⟩)

@[simp] theorem mk_eq_mk_iff (a b : Positive A) :
    mk a = mk b ↔ CuntzBelow a b ∧ CuntzBelow b a := Quotient.eq

end CuntzClass
namespace ExtendedTrace
variable {A}

def cuntzRank (τ : ExtendedTrace A) : CuntzClass A →o ℝ≥0∞ where
  toFun := Quotient.lift τ.rank (fun _ _ h => τ.rank_eq_of_cuntzEquivalent h.1 h.2)
  monotone' := by
    intro q r
    exact Quotient.inductionOn₂ q r (fun a b h => τ.rank_le_of_cuntzBelow ((CuntzClass.mk_le_mk a b).mp h))

@[simp] theorem cuntzRank_mk (τ : ExtendedTrace A) (a : Positive A) :
    τ.cuntzRank (CuntzClass.mk a) = τ.rank a := rfl

end ExtendedTrace
end CuntzTrace

end

end OAI
