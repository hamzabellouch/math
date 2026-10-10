import OAI.Combinatorics.PolynomialVacuum.Pairing.DecoratedStack
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackSeams

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

omit [NeZero M] in
theorem decoration_product [NeZero M] (c : StackCoordinates M H) (L k : ℕ) (hL : L<H) (κ : ℂ) :
    (∏j : Fin H,seamDecoration L k κ j (c.1 j.castSucc))=
      (κ/zeta)^cylinderBlockCharge k (c.1 ⟨L,by omega⟩) := by
  rw [Finset.prod_eq_single (⟨L,hL⟩ : Fin H)]
  · simp only [seamDecoration,ite_true]
    rfl
  · intro j _ hj
    exact ite_eq_right (fun he=>hj (Fin.ext he))
  · simp

theorem closed_stack_local_shape (c : ClosedStack M H) :
    stackLocalWeight c.val.val.1 c.val.val.2.1 c.val.val.2.2=
      xStar^(activeSites (coordinatesCurrent c.val.val)).card*
        loopTurnPhase (flowTurn (coordinatesCurrent c.val.val)) := by
  have he:=domainWeight_closed (bandSites M H) (coordinatesCurrent c.val.val)
    (empty_stack_legal c.val c.property) (empty_stack_active c.val.val c.property)
  rw [domainWeight,uniformSeamWeight] at he
  change (∏v∈bandSites M H,localCurrentWeight (stackCurrent c.val.val.1 c.val.val.2.1 c.val.val.2.2) v)*_= _ at he
  rw [stack_local_domain] at he
  exact mul_right_cancel₀ (zpow_ne_zero _ (by simp [zeta_eq_I])) he

 

theorem decorated_weight_current (c : ClosedStack M H) (L k : ℕ) (hL : L<H) (κ : ℂ) :
    decoratedStackWeight (seamTwists H L) (seamDecoration L k κ) c.val.val=
      currentWeight (coordinatesCurrent c.val.val) (0,L) (-(k : ZMod M),L) κ := by
  unfold decoratedStackWeight
  rw [Finset.prod_mul_distrib,decoration_product _ L k hL κ,stack_twist_product,
    stack_block_potential _ (empty_stack_legal c.val c.property),closed_stack_local_shape]
  unfold currentWeight currentPhase threeSeamFactor
  change _=xStar^(activeSites (coordinatesCurrent c.val.val)).card*
    (loopTurnPhase (flowTurn (coordinatesCurrent c.val.val))*
      zeta^(-potential (coordinatesCurrent c.val.val) (0,L))*
      (zeta⁻¹)^(potential (coordinatesCurrent c.val.val) (0,L)-topHom (coordinatesCurrent c.val.val))*
      (κ/zeta)^(potential (coordinatesCurrent c.val.val) (-(k : ZMod M),L)-potential (coordinatesCurrent c.val.val) (0,L)))
  ring

end PolynomialVacuumCylinder

end OAI
