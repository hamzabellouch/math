import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledRecenter
import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularOrdinaryTree

namespace OAI

/-! Recentered trees keep the original physical packets and weighted
angular density tests when evaluated at the original reference slope. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
variable (t M : ℝ) (hM : 0≤M)
  (hshear : ∀ j l, |(P.rowSlope j l-t)*P.length j/P.width|≤1)
  (hcarrier : ∀ j l k, |P.frequency k*(P.rowSlope j l-t)*P.length j|≤M)

@[simp] theorem recenter_physicalPacket_reference (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (z : ℝ×ℝ) :
    (P.recenter t M hM hshear hcarrier).physicalPacket t j l u k z=
      P.physicalPacket 0 j l u k z := by
  have h := (P.recenter t M hM hshear hcarrier).physicalPacket_slopeShear t
    j l u k ((slopeShear t).symm z)
  rw [MeasurableEquiv.apply_symm_apply,P.recenter_physicalPacket,
    MeasurableEquiv.apply_symm_apply] at h
  exact h

@[simp] theorem recenter_densityTile (cell : ∀ j, P.labels j → ℤ) (q : P.PacketIndex) :
    (P.recenter t M hM hshear hcarrier).densityTile t cell q=P.densityTile 0 cell q := by
  rcases q with ⟨j,l,u⟩
  unfold densityTile
  congr 1
  rw [P.recenter_actualX,P.recenter_actualZ]
  simp only [zero_mul,add_zero,sub_add_cancel]

@[simp] theorem recenter_ordinaryDensity (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (w tau : ℝ) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (q : P.PacketIndex) :
    (P.recenter t M hM hshear hcarrier).ordinaryDensity t cell grid w tau E u q=
      P.ordinaryDensity 0 cell grid w tau E u q := by
  unfold ordinaryDensity
  rw [P.recenter_densityTile]
  rfl

@[simp] theorem recenter_treeConstant (C : ℝ) (B K : ℕ) (Lip : ℝ) :
    (P.recenter t M hM hshear hcarrier).ordinaryTreeConstant C B K Lip=
      P.ordinaryTreeConstant C B K Lip := rfl

theorem recenter_treeValue
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℂ) (z : ℝ×ℝ) :
    (P.recenter t M hM hshear hcarrier).physicalTreeSelectorValue t c selector z=
      P.physicalTreeSelectorValue 0 c selector z := by
  unfold physicalTreeSelectorValue
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  funext k
  exact congrArg (fun a : ℂ => (c j l u).ofLp k*selector j l k*a)
    (P.recenter_physicalPacket_reference t M hM hshear hcarrier j l u k z)

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
