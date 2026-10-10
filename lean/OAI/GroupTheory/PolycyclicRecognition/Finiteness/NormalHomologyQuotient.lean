import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InnerHomologyAction

namespace OAI

/-! # The quotient action on normal-subgroup homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (A : Rep ℤ G)

theorem normalHomologyMap_subgroup (i : ℕ) (a : N) :
    normalHomologyMap ℤ N A i (a : G) = 𝟙 _ := by
  change groupHomology.map _ _ i = _
  have h := groupHomology.map_congr
    (A := Rep.res N.subtype A) (B := Rep.res N.subtype A)
    (f := (MulAut.conjNormal (H := N) (a : G)).toMonoidHom)
    (g := (MulAut.conj a).toMonoidHom)
    (φ := normalHomologyCoefficient ℤ N A (a : G))
    (ψ := innerHomologyCoefficient (Rep.res N.subtype A) a)
    (by ext n; rfl) (by rfl) i
  exact h.trans (innerHomologyMap_eq_id (Rep.res N.subtype A) a i)

def quotientHomologyAction (i : ℕ) : Rep ℤ (G ⧸ N) :=
  Rep.of (QuotientGroup.lift N (normalHomologyAction ℤ N A i).ρ (by
    intro a ha
    change (normalHomologyMap ℤ N A i a).hom = 1
    rw [normalHomologyMap_subgroup N A i ⟨a, ha⟩]
    rfl))

end PolycyclicRecognition

end

end OAI
