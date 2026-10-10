import Mathlib
import OAI.Probability.BinarySweep.Conditional.AugmentedBlock
import OAI.Probability.BinarySweep.MatrixBounds.HilbertBlockTrace

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

abbrev inducedPlacementAverage (z : ℝ) :=
  groupAverage (coindHilbertRep (blockPerm e) σ
    (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
    (fun a => (conditionalGroupLaw H z a:ℂ))

def placementFiberMoment (z : ℝ) (q : ℕ) (x y : Placement H k 0) : ℝ :=
  if hp : 0<placementKernel H z x y then
    let g := realizePlacement H z x (placementIdentification H k y) hp
    evenMoment q (groupAverage (augmentedRepresentation H x g e σ)
      (fun a => (conditionalGroupLaw (augmentByChoice H x g) z a:ℂ)))
  else 0

lemma realizedOutputIndex (z : ℝ) (x y : Placement H k 0)
    (hp : 0<placementKernel H z x y) :
    augmentedOutputIndex H x (realizePlacement H z x (placementIdentification H k y) hp)=y := by
  apply (placementIdentification H k).injective
  rw [←placementBijection_index]
  exact realizePlacement_spec H z x (placementIdentification H k y) hp

lemma inducedPlacementBlock_root {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) {q : ℕ} (hq : 0<q)
    (x y : Placement H k 0) :
    evenMoment q (hilbertBlock (inducedPlacementAverage H e σ z) y x)^(((2*q:ℕ):ℝ)⁻¹) =
      placementKernel H z x y * (placementFiberMoment H e σ z q x y)^(((2*q:ℕ):ℝ)⁻¹) := by
  by_cases hp : 0<placementKernel H z x y
  · unfold placementFiberMoment
    rw [dite_eq_left hp]
    have he := placementBlock_moment_root H e σ hz hz1 hσ hq x
      (realizePlacement H z x (placementIdentification H k y) hp)
    rw [realizedOutputIndex H z x y hp] at he
    exact he
  · have he : placementKernel H z x y=0 :=
      le_antisymm (le_of_not_gt hp) (placementKernel_nonneg H hz hz1 x y)
    rw [he,zero_mul,placementBlock_zero H e σ hz hz1 x y he]
    have hq0 : q≠0 := hq.ne'
    simp [evenMoment,hq0]

theorem induced_placement_cycle_bound {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) {q : ℕ} (hq : 0<q) :
    evenMoment q (inducedPlacementAverage H e σ z) ≤
      ∑x : Fin (2*q) → Placement H k 0,
        (∏j, placementEdge H z (decide (j.val%2≠0)) (x j) (x (finRotate (2*q) j))) *
        ∏j, (if j.val%2=0 then
          placementFiberMoment H e σ z q (x j) (x (finRotate (2*q) j))
        else placementFiberMoment H e σ z q (x (finRotate (2*q) j)) (x j))^(((2*q:ℕ):ℝ)⁻¹) := by
  refine (evenMoment_blocks_le hq (inducedPlacementAverage H e σ z)).trans_eq ?_
  apply Finset.sum_congr rfl
  intro x _
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases he : j.val%2=0
  · simp only [placementEdge,decide_eq_true_eq,ne_eq,he,not_true_eq_false,ite_false,ite_true]
    exact inducedPlacementBlock_root H e σ hz hz1 hσ hq _ _
  · simp only [placementEdge,decide_eq_true_eq,ne_eq,he,not_false_eq_true,ite_true,ite_false]
    exact inducedPlacementBlock_root H e σ hz hz1 hσ hq _ _

end BinaryCoordinateSweeps

end

end OAI
