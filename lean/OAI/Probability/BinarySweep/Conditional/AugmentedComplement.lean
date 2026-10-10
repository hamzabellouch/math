import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungPlacement
import OAI.Probability.BinarySweep.Trajectories.TrajectoryComplement
import OAI.Probability.BinarySweep.Conditional.ComplementBlocks

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g₀ : ConditionalChoices H)

def augmentedOutputIndex : Placement H k 0 :=
  x.trans (remainingPerm H g₀.val g₀.property).toEmbedding

lemma augmentedOutputIndex_physical :
    (augmentedPlacement H x g₀ (Fin.last b)).trans (freeIdentification H).symm.toEmbedding =
      augmentedOutputIndex H x g₀ := by
  apply Function.Embedding.ext
  intro i
  apply (freeIdentification H).injective
  simp only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
  change augmentedPlacement H x g₀ (Fin.last b) i=
    (freeIdentification H) ((freeIdentification H).symm (remainingBijection H g₀.val g₀.property (x i)))
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact congrArg (fun a : Equiv.Perm (GridSlot bits) => a (x i).val) (gridPartialSweep_last bits g₀.val)

def augmentationInputComplement : FreeSlot (augmentByChoice H x g₀) 0 ≃ PlacementComplement x :=
  (augmentationFreeEquiv H x g₀ 0).trans
    (complementMap (Equiv.refl _) _ x (by
      simpa only [Equiv.refl_toEmbedding,Function.Embedding.trans_refl] using augmentedPlacement_zero H x g₀))

def augmentationOutputComplement : FreeSlot (augmentByChoice H x g₀) (Fin.last b) ≃
    PlacementComplement (augmentedOutputIndex H x g₀) :=
  (augmentationFreeEquiv H x g₀ (Fin.last b)).trans
    (complementMap (freeIdentification H).symm _ _ (augmentedOutputIndex_physical H x g₀))

lemma augmentationInputComplement_val (w : FreeSlot (augmentByChoice H x g₀) 0) :
    (augmentationInputComplement H x g₀ w).val.val=w.val := rfl

lemma augmentationOutputComplement_val (w : FreeSlot (augmentByChoice H x g₀) (Fin.last b)) :
    (augmentationOutputComplement H x g₀ w).val=
      (freeIdentification H).symm (augmentationFreeEquiv H x g₀ (Fin.last b) w).val := rfl

lemma augmentedOutputIndex_event (g : ConditionalChoices H) :
    x.trans (remainingPerm H g.val g.property).toEmbedding=augmentedOutputIndex H x g₀ ↔
      pathEvent (augmentByChoice H x g₀) g.val := by
  rw [← placementEvent_iff_augmentation H x g₀ g]
  constructor
  · intro he
    apply Function.Embedding.ext
    intro i
    apply (freeIdentification H).symm.injective
    exact congrArg (fun y : Placement H k 0 => y i) he
  · intro he
    apply Function.Embedding.ext
    intro i
    exact congrArg (fun y : Placement H k (Fin.last b) => (freeIdentification H).symm (y i)) he

lemma augmented_event (g : ConditionalChoices (augmentByChoice H x g₀)) :
    x.trans (remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property)).toEmbedding =
      augmentedOutputIndex H x g₀ :=
  (augmentedOutputIndex_event H x g₀ ((augmentByChoice_extension H x g₀).restrictChoice g)).mpr g.property

lemma augmentation_complement_square (g : ConditionalChoices (augmentByChoice H x g₀))
    (w : FreeSlot (augmentByChoice H x g₀) 0) :
    augmentationOutputComplement H x g₀
      (remainingBijection (augmentByChoice H x g₀) g.val g.property w) =
      complementMap (remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))
        x (augmentedOutputIndex H x g₀)
        (augmented_event H x g₀ g)
        (augmentationInputComplement H x g₀ w) := by
  apply Subtype.ext
  rw [augmentationOutputComplement_val,complementMap_val]
  exact congrArg (freeIdentification H).symm (augmented_gridSweep H x g₀ g w)

variable {A : Type*} [Fintype A] (e : A ⊕ Fin k ≃ FreeSlot H 0)

def augmentedInputBasis : A ≃ FreeSlot (augmentByChoice H x g₀) 0 :=
  (placementComplementEquiv e x).trans (augmentationInputComplement H x g₀).symm

def augmentedOutputBasis : A ≃ FreeSlot (augmentByChoice H x g₀) (Fin.last b) :=
  (placementComplementEquiv e (augmentedOutputIndex H x g₀)).trans
    (augmentationOutputComplement H x g₀).symm

lemma augmented_subgroup_bijection (g : ConditionalChoices (augmentByChoice H x g₀)) :
    ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm
        ((placementSection e (augmentedOutputIndex H x g₀))⁻¹*
          remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))).1 =
      ((augmentedInputBasis H x g₀ e).trans
        (remainingBijection (augmentByChoice H x g₀) g.val g.property)).trans
          (augmentedOutputBasis H x g₀ e).symm := by
  rw [placement_subgroup_complement e
    (remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))
    x (augmentedOutputIndex H x g₀) (augmented_event H x g₀ g)]
  ext a
  apply (placementComplementEquiv e (augmentedOutputIndex H x g₀)).injective
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply,augmentedInputBasis,augmentedOutputBasis,
    Equiv.symm_trans_apply]
  exact (augmentation_complement_square H x g₀ g
    ((augmentationInputComplement H x g₀).symm (placementComplementEquiv e x a))).symm.trans
      (by rfl)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

 def subPlacement (A : Finset I) (x : I ↪ X) : A ↪ X :=
  (Function.Embedding.subtype (fun i => i∈A)).trans x

omit [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] in
lemma subPlacement_move (A : Finset I) (g : Equiv.Perm X) (x : I ↪ X) :
    subPlacement A (movePlacement g x)=movePlacement g (subPlacement A x) := rfl

def placementMoveEquiv (g : Equiv.Perm X) : (I ↪ X) ≃ (I ↪ X) :=
  (Equiv.refl I).embeddingCongr g

omit [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] in
lemma move_sub_eq_iff (A : Finset I) (g : Equiv.Perm X)
    (x : I ↪ X) (u : A ↪ X) :
    subPlacement A (movePlacement g x)=u ↔ subPlacement A x=movePlacement g⁻¹ u := by
  rw [subPlacement_move]
  constructor
  · intro h
    have he := congrArg (movePlacement g⁻¹) h
    simpa only [← movePlacement_mul,inv_mul_cancel,movePlacement_one] using he
  · intro h
    rw [h,← movePlacement_mul,mul_inv_cancel,movePlacement_one]

def placementMarginal (A : Finset I) : ((I ↪ X) → ℂ) →ₗ[ℂ] ((A ↪ X) → ℂ) where
  toFun v u := ∑x : I ↪ X, if subPlacement A x=u then v x else 0
  map_add' v w := by
    funext u
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  map_smul' c v := by
    funext u
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp

omit [DecidableEq I] in
lemma placementMarginal_intertwines (A : Finset I) (g : Equiv.Perm X)
    (v : (I ↪ X) → ℂ) :
    placementMarginal A (placementRep g v)=placementRep g (placementMarginal A v) := by
  funext u
  change (∑x : I ↪ X, if subPlacement A x=u then v (movePlacement g⁻¹ x) else 0) =
    ∑x : I ↪ X, if subPlacement A x=movePlacement g⁻¹ u then v x else 0
  rw [← (placementMoveEquiv (I:=I) g).sum_comp
    (fun x => if subPlacement A x=u then v (movePlacement g⁻¹ x) else 0)]
  apply Finset.sum_congr rfl
  intro x _
  change (if subPlacement A (movePlacement g x)=u then
    v (movePlacement g⁻¹ (movePlacement g x)) else 0)=_
  simp only [move_sub_eq_iff,← movePlacement_mul,inv_mul_cancel,movePlacement_one]

variable (μ : YoungDiagram)

theorem spechtPlacement_marginal_zero (A : Finset (Tail μ))
    (hA : A≠Finset.univ) (v : SpechtSpace μ) :
    placementMarginal A (spechtPlacement μ v)=0 := by
  let f := (placementMarginal A).comp (spechtPlacement μ)
  have hcard : Fintype.card A < Fintype.card (Cell μ) - μ.rowLen 0 := by
    rw [← card_tail]
    simp only [Fintype.card_coe]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA)
  have hf : ∀g w, f (spechtRep μ g w)=placementRep g (f w) := by
    intro g w
    simp only [f,LinearMap.comp_apply,spechtPlacement_intertwines,placementMarginal_intertwines]
  have he := no_short_placement_intertwiner μ hcard f hf
  exact congrArg (fun f => f v) he

end BinaryCoordinateSweeps.Young

end

end OAI
