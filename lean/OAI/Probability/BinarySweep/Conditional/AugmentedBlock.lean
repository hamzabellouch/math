import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.LinearEvenMoment
import OAI.Probability.BinarySweep.SparseBounds.ConditionalCentered

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g₀ : ConditionalChoices H)
  {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

def augmentedFrame : Equiv.Perm A :=
  ((augmentedInputBasis H x g₀ e).trans (freeIdentification (augmentByChoice H x g₀))).trans
    (augmentedOutputBasis H x g₀ e).symm

def augmentedRepresentation : Representation ℂ (Equiv.Perm (FreeSlot (augmentByChoice H x g₀) 0)) W :=
  σ.comp (augmentedInputBasis H x g₀ e).symm.permCongrHom.toMonoidHom

lemma augmented_subgroup_perm (g : ConditionalChoices (augmentByChoice H x g₀)) :
    ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm
        ((placementSection e (augmentedOutputIndex H x g₀))⁻¹*
          remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))).1 =
      augmentedFrame H x g₀ e * (augmentedInputBasis H x g₀ e).symm.permCongr
        (remainingPerm (augmentByChoice H x g₀) g.val g.property) := by
  rw [augmented_subgroup_bijection]
  ext a
  simp only [augmentedFrame,Equiv.Perm.mul_apply,Equiv.permCongr_apply,Equiv.trans_apply,
    Equiv.symm_symm,Equiv.apply_symm_apply,remainingPerm]

omit [FiniteDimensional ℂ W] in
lemma placementBlock_expectation (z : ℝ) (y : Placement H k 0) :
    hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) y x =
    ∑g : ConditionalChoices H, conditionalChoiceWeight H z g •
      (if x.trans (remainingPerm H g.val g.property).toEmbedding=y then
        σ ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
          (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*
            remainingPerm H g.val g.property)).1 else 0) := by
  have hs (r : ℝ) (T : W →ₗ[ℂ] W) : (r:ℂ) • T = r • T :=
    algebraMap_smul ℂ r T
  calc
    _ = ∑a, conditionalGroupLaw H z a •
        hilbertBlock (coindHilbertRep (blockPerm e) σ (fun x => (placementSection e x)⁻¹)
          (placement_cosets_bijective e) a) y x := by
      ext v
      simp only [groupAverage,hilbertBlock,LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
      apply Finset.sum_congr rfl
      intro a _
      exact algebraMap_smul ℂ (conditionalGroupLaw H z a) _
    _ = _ := by
      rw [conditionalGroupLaw_expectation]
      apply Finset.sum_congr rfl
      intro g _
      rw [placement_hilbertBlock]
      split_ifs <;> rfl

omit [FiniteDimensional ℂ W] in
theorem augmented_block_average (z : ℝ)
    (hp : conditionalNormalizer (augmentByChoice H x g₀) z≠0) :
    hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) (augmentedOutputIndex H x g₀) x =
    (conditionalNormalizer (augmentByChoice H x g₀) z / conditionalNormalizer H z) •
      (σ (augmentedFrame H x g₀ e) *
        groupAverage (augmentedRepresentation H x g₀ e σ)
          (fun a => (conditionalGroupLaw (augmentByChoice H x g₀) z a:ℂ))) := by
  rw [placementBlock_expectation]
  have he := (augmentByChoice_extension H x g₀).conditional_sum z hp
    (fun g => σ ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm ((placementSection e (augmentedOutputIndex H x g₀))⁻¹*
        remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))).1)
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr rfl
    intro g _
    by_cases hg : pathEvent (augmentByChoice H x g₀) g.val
    · rw [dite_eq_left hg,ite_eq_left ((augmentedOutputIndex_event H x g₀ g).mpr hg)]
    · rw [dite_eq_right hg,ite_eq_right (fun he => hg ((augmentedOutputIndex_event H x g₀ g).mp he)),smul_zero]
  · congr 1
    simp_rw [augmented_subgroup_perm,map_mul]
    rw [groupAverage]
    have hh := conditionalGroupLaw_expectation (augmentByChoice H x g₀) z
      (fun a => augmentedRepresentation H x g₀ e σ a)
    have hc : (∑a, (conditionalGroupLaw (augmentByChoice H x g₀) z a:ℂ) •
        augmentedRepresentation H x g₀ e σ a) =
        ∑g : ConditionalChoices (augmentByChoice H x g₀),
          conditionalChoiceWeight (augmentByChoice H x g₀) z g •
            augmentedRepresentation H x g₀ e σ (remainingPerm (augmentByChoice H x g₀) g.val g.property) := by
      refine Eq.trans ?_ hh
      apply Finset.sum_congr rfl
      intro a _
      exact algebraMap_smul ℂ (conditionalGroupLaw (augmentByChoice H x g₀) z a)
        (augmentedRepresentation H x g₀ e σ a)
    rw [hc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_smul_comm]
    rfl

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma placementBijection_index (x : Placement H k 0) (g : ConditionalChoices H) :
    placementBijection H k g x = placementIdentification H k (augmentedOutputIndex H x g) := by
  apply Function.Embedding.ext
  intro i
  change remainingBijection H g.val g.property (x i) =
    freeIdentification H ((freeIdentification H).symm (remainingBijection H g.val g.property (x i)))
  exact (Equiv.apply_symm_apply _ _).symm

lemma placementKernel_ratio (z : ℝ) (x : Placement H k 0) (g : ConditionalChoices H) :
    placementKernel H z x (augmentedOutputIndex H x g) =
      conditionalNormalizer (augmentByChoice H x g) z / conditionalNormalizer H z := by
  unfold placementKernel
  rw [← placementBijection_index H x g,placementProbability_augmentation,
    pathExtension_event_ratio (augmentByChoice_extension H x g)]

lemma placementKernel_output_pos {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (x : Placement H k 0) (g : ConditionalChoices H) :
    0<placementKernel H z x (augmentedOutputIndex H x g) := by
  rw [placementKernel_ratio]
  exact div_pos (conditionalNormalizer_pos _ hz hz1) (conditionalNormalizer_pos _ hz hz1)

variable {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

omit [FiniteDimensional ℂ W] in
lemma placementBlock_zero {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (x y : Placement H k 0) (hp : placementKernel H z x y=0) :
    hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) y x = 0 := by
  rw [placementBlock_expectation]
  apply Finset.sum_eq_zero
  intro g _
  have hn : x.trans (remainingPerm H g.val g.property).toEmbedding ≠ y := by
    intro he
    have ht := placementKernel_output_pos H hz hz1 x g
    change 0<placementKernel H z x (x.trans (remainingPerm H g.val g.property).toEmbedding) at ht
    rw [he,hp] at ht
    exact (lt_irrefl 0 ht)
  rw [ite_eq_right hn,smul_zero]

lemma placementBlock_moment {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) (q : ℕ)
    (x : Placement H k 0) (g : ConditionalChoices H) :
    evenMoment q (hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) (augmentedOutputIndex H x g) x) =
    (placementKernel H z x (augmentedOutputIndex H x g))^(2*q) *
      evenMoment q (groupAverage (augmentedRepresentation H x g e σ)
        (fun a => (conditionalGroupLaw (augmentByChoice H x g) z a:ℂ))) := by
  rw [augmented_block_average H x g e σ z (conditionalNormalizer_pos _ hz hz1).ne',
    evenMoment_smul,evenMoment_unitary_left]
  · rw [placementKernel_ratio]
  · rw [unitary_rep_adjoint σ hσ,←map_mul,inv_mul_cancel,map_one]

lemma placementBlock_moment_root {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) {q : ℕ} (hq : 0<q)
    (x : Placement H k 0) (g : ConditionalChoices H) :
    evenMoment q (hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) (augmentedOutputIndex H x g) x)^(((2*q:ℕ):ℝ)⁻¹) =
    placementKernel H z x (augmentedOutputIndex H x g) *
      evenMoment q (groupAverage (augmentedRepresentation H x g e σ)
        (fun a => (conditionalGroupLaw (augmentByChoice H x g) z a:ℂ)))^(((2*q:ℕ):ℝ)⁻¹) := by
  rw [placementBlock_moment H e σ hz hz1 hσ]
  have hp := (placementKernel_output_pos H hz hz1 x g).le
  rw [Real.mul_rpow (pow_nonneg hp _) (evenMoment_nonneg _ _),
    ← Real.rpow_natCast,← Real.rpow_mul hp]
  have hn : ((2*q:ℕ):ℝ)≠0 := by positivity
  rw [mul_inv_cancel₀ hn,Real.rpow_one]

end BinaryCoordinateSweeps

end

end OAI
