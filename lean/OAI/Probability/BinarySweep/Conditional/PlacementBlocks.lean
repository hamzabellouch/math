import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.HookInducedMoment

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation Equiv Equiv.Perm

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  (e : A ⊕ B ≃ X)

abbrev PlacementComplement (x : B ↪ X) := {u : X // u ∉ Set.range x}

def placementComplementEquiv (x : B ↪ X) : A ≃ PlacementComplement x where
  toFun a := ⟨placementSection e x (e (Sum.inl a)), by
    rintro ⟨b,hb⟩
    have he := (placementSection e x).injective ((placementSection_apply e x b).trans hb)
    exact Sum.inl_ne_inr (e.injective he).symm⟩
  invFun u := (e.symm ((placementSection e x)⁻¹ u.val)).getLeft (by
    cases h : e.symm ((placementSection e x)⁻¹ u.val) with
    | inl _ => rfl
    | inr b =>
      exfalso
      apply u.property
      refine ⟨b,?_⟩
      have hh := congrArg (fun t => placementSection e x (e t)) h
      simpa only [e.apply_symm_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply,
        show placementSection e x (e (Sum.inr b)) = x b from placementSection_apply e x b] using hh.symm)
  left_inv a := by
    simp only [Equiv.Perm.inv_def,Equiv.symm_apply_apply,e.symm_apply_apply,Sum.getLeft_inl]
  right_inv u := by
    apply Subtype.ext
    have hl : (e.symm ((placementSection e x)⁻¹ u.val)).isLeft := by
      cases h : e.symm ((placementSection e x)⁻¹ u.val) with
      | inl _ => rfl
      | inr b =>
        exfalso
        apply u.property
        refine ⟨b,?_⟩
        have hh := congrArg (fun t => placementSection e x (e t)) h
        simpa only [e.apply_symm_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply,
        show placementSection e x (e (Sum.inr b)) = x b from placementSection_apply e x b] using hh.symm
    change placementSection e x (e (Sum.inl ((e.symm ((placementSection e x)⁻¹ u.val)).getLeft _))) = u.val
    rw [show Sum.inl ((e.symm ((placementSection e x)⁻¹ u.val)).getLeft hl) =
      e.symm ((placementSection e x)⁻¹ u.val) from Sum.inl_getLeft _ hl]
    simp

omit [Fintype X] in
lemma placementCoset_index (a : Equiv.Perm X) (y : B ↪ X) :
    cosetIndexAction (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e) a y = y.trans a.symm.toEmbedding := by
  let c := (cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
    (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)
  have he : blockPerm e c.1 * (placementSection e c.2)⁻¹ = (placementSection e y)⁻¹*a :=
    (cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).apply_symm_apply _
  have hi := congrArg (fun g : Equiv.Perm X => g⁻¹) he
  ext b
  have hb := Equiv.congr_fun hi (basePlacement e b)
  simp only [mul_inv_rev,inv_inv,Equiv.Perm.mul_apply,← map_inv,placementSection_apply] at hb
  change placementSection e c.2 ((blockPerm e c.1⁻¹) (e (Sum.inr b))) = _ at hb
  rw [blockPerm_inr] at hb
  exact (placementSection_apply e c.2 b).symm.trans hb

omit [Fintype X] in
lemma placementCoset_subgroup (a : Equiv.Perm X) (y : B ↪ X) :
    blockPerm e ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)).1 =
      (placementSection e y)⁻¹*a*placementSection e (y.trans a.symm.toEmbedding) := by
  have he := (cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
    (placement_cosets_bijective e)).apply_symm_apply ((placementSection e y)⁻¹*a)
  change blockPerm e _ * (placementSection e _)⁻¹ = _ at he
  have hi := placementCoset_index e a y
  change ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
    (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)).2 = _ at hi
  rw [hi] at he
  exact (mul_inv_eq_iff_eq_mul.mp he)

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (σ : Representation ℂ (Equiv.Perm A) W)

omit [Fintype X] in
lemma placement_hilbertBlock (a : Equiv.Perm X) (x y : B ↪ X) :
    hilbertBlock (coindHilbertRep (blockPerm e) σ (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e) a) y x =
      if x.trans a.toEmbedding = y then
        σ ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
          (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)).1 else 0 := by
  rw [hilbertBlock_coind,placementCoset_index]
  congr 1
  apply propext
  constructor
  · intro h
    ext b
    have hb := congrArg (fun x : B ↪ X => a (x b)) h
    exact hb.symm.trans (by simp)
  · intro h
    ext b
    have hb := congrArg (fun x : B ↪ X => a⁻¹ (x b)) h
    simpa using hb.symm

end BinaryCoordinateSweeps.Irrep

end

end OAI
