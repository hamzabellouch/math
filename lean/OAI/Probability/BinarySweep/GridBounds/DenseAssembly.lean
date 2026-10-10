import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.GenericHookAux
import OAI.Probability.BinarySweep.YoungTheory.PhysicalHookInduced
import OAI.Probability.BinarySweep.Conditional.CycleAugmentation

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Irrep Representation Young GridSplit Signed

def EnumeratedMomentBound (q : ℕ) {b : ℕ} (bits : Fin b → ℕ) (z : ℝ) : Prop :=
  ∀ h : ℕ, ∀ H : PathFamily bits h, ∀ α : (Fintype.card (FreeSlot H 0)).Partition,
    evenMoment q (groupAverage (partitionHilbertRep α)
      (fun a => (conditionalGroupLaw H z ((Fintype.equivFin _).symm.permCongr a):ℂ))) ≤
      Real.exp (-cExponent (gridSize bits)*typeF α+
        eExponent (gridSize bits)*h*Real.log (gridSize bits)-pathCost H)

def diagramF (μ : YoungDiagram) : ℝ := Real.log (Module.finrank ℂ (SpechtSpace μ))

lemma moment_divide_dimension {D T B : ℝ} (hD : 0<D) (h : D*T≤Real.exp B) :
    T≤Real.exp (B-Real.log D) := by
  have hh : T*D≤Real.exp B := by rwa [mul_comm]
  have he := (le_div_iff₀ hD).mpr hh
  rwa [←Real.exp_log hD,←Real.exp_sub] at he

lemma dense_of_auxiliary_hook {m n h r : ℕ} (s q t : ℕ) (hq : 0<q)
    (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
    (hd : ∀j, bits j≤2*r) (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0)
    (z : ℝ) (hz : 0≤z) (hzr : z≤linePerturbationRadius r)
    (hhook : ∀ h' : ℕ, ∀ HH : PathFamily bits h',
      ∀ ee : Cell (hookPart μ t) ≃ FreeSlot HH 0,
      evenMoment q (groupAverage ((hilbertSpecht (hookPart μ t)).comp
        ee.symm.permCongrHom.toMonoidHom) (fun a => (conditionalGroupLaw HH z a:ℂ)))≤
        Real.exp (-(cExponent s+inductionGap s)*diagramF (hookPart μ t)+
          (eExponent s-inductionGap s)*h'*Real.log s-pathCost HH+(s:ℝ)^(9/10:ℝ))) :
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*diagramF (hookPart μ t)+
        (eExponent s-inductionGap s)*(h+Fintype.card (Cell (southeast μ t)))*Real.log s+
        (s:ℝ)^(9/10:ℝ)-pathCost H+
        Real.log 4*Fintype.card (Cell (southeast μ t))*(m+n)-diagramF (southeast μ t)) := by
  let k := Fintype.card (Cell (southeast μ t))
  let f := hookPlacementBasis H μ t e
  let σ := hilbertSpecht (hookPart μ t)
  let B := -(cExponent s+inductionGap s)*diagramF (hookPart μ t)+
    (eExponent s-inductionGap s)*(h+k)*Real.log s+(s:ℝ)^(9/10:ℝ)
  have hf (x y : Placement H k 0) (hp : 0<placementKernel H z x y) :
      placementFiberMoment H f σ z q x y ≤
        Real.exp (B-placementTransitionCost H z x (placementIdentification H k y)) := by
    let g := realizePlacement H z x (placementIdentification H k y) hp
    have hb := hhook (h+k) (augmentByChoice H x g) (augmentedInputBasis H x g f)
    unfold placementFiberMoment
    rw [dite_eq_left hp]
    change evenMoment q (groupAverage (augmentedRepresentation H x g f σ) _)≤_
    change evenMoment q (groupAverage ((hilbertSpecht (hookPart μ t)).comp
      (augmentedInputBasis H x g f).symm.permCongrHom.toMonoidHom) _)≤_ at hb ⊢
    refine hb.trans_eq ?_
    unfold placementTransitionCost
    rw [dite_eq_left (show 0<placementProbability H z x (placementIdentification H k y) from hp)]
    congr 1
    dsimp [B,diagramF]
    push_cast
    ring
  have hi := induced_placement_of_hook_bound H f σ hd hz hzr
    (hilbertSpecht_unitary (hookPart μ t)) hq B hf
  have hm := (conditional_hook_induced_moment_le H μ t e z q).trans hi
  have hD : (0:ℝ)<Module.finrank ℂ (SpechtSpace (southeast μ t)) := by
    rw [←hilbertSpecht_finrank]
    exact_mod_cast irreducible_finrank_pos (hilbertSpecht (southeast μ t))
  refine (moment_divide_dimension hD hm).trans_eq ?_
  congr 1
  dsimp [B,k,diagramF]
  push_cast
  ring

theorem dense_branch_operator_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h r : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    (∀j, bits j≤2*r) →
    ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
    ∀ μ : YoungDiagram, ∀ e : Cell μ ≃ FreeSlot H 0, ∀z : ℝ,
    0≤z → z≤linePerturbationRadius r →
    EnumeratedMomentBound q (leftBits bits) z → EnumeratedMomentBound q (rightBits bits) z →
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*diagramF (hookPart μ t)+
        (eExponent s-inductionGap s)*(h+Fintype.card (Cell (southeast μ t)))*Real.log s+
        (s:ℝ)^(9/10:ℝ)-pathCost H+
        Real.log 4*Fintype.card (Cell (southeast μ t))*(m+n)-diagramF (southeast μ t)) := by
  filter_upwards [specht_hook_auxiliary_eventually q hq] with s hs
  intro m n h r bits H hsize hu hv hub hvb hd t ht hts μ e z hz hzr hR hC
  apply dense_of_auxiliary_hook s q t (by omega) bits H hd μ e z hz hzr
  intro h' HH ee
  exact hs m n h' bits HH hsize hu hv hub hvb t ht hts
    (hookPart μ t) (hookPart_inHook μ t) ee z
    (fun y a => hR _ (rowFamily bits HH y) a.val)
    (fun x a => hC _ (columnFamily bits HH x) a.val)

end BinaryCoordinateSweeps

end

end OAI
