import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.SumDite
import OAI.Probability.BinarySweep.Trajectories.PathExtension
import OAI.Probability.BinarySweep.Conditional.PlacementBlocks

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X]

def complementMap (f : X ≃ Y) (x : B ↪ X) (y : B ↪ Y)
    (hf : x.trans f.toEmbedding=y) : PlacementComplement x ≃ PlacementComplement y where
  toFun u := ⟨f u.val,by
    rintro ⟨b,hb⟩
    apply u.property
    refine ⟨b,f.injective ?_⟩
    exact (congrArg (fun y : B ↪ Y => y b) hf).trans hb⟩
  invFun u := ⟨f.symm u.val,by
    rintro ⟨b,hb⟩
    apply u.property
    refine ⟨b,?_⟩
    exact (congrArg (fun y : B ↪ Y => y b) hf).symm.trans
      ((congrArg f hb).trans (f.apply_symm_apply _))⟩
  left_inv u := Subtype.ext (f.symm_apply_apply _)
  right_inv u := Subtype.ext (f.apply_symm_apply _)

omit [Fintype B] [Fintype X] in
lemma complementMap_val (f : X ≃ Y) (x : B ↪ X) (y : B ↪ Y)
    (hf : x.trans f.toEmbedding=y) (u : PlacementComplement x) :
    (complementMap f x y hf u).val=f u.val := rfl

omit [Fintype B] [Fintype X] in
lemma placement_inverse_event (a : Equiv.Perm X) (x y : B ↪ X)
    (he : x.trans a.toEmbedding=y) : y.trans a.symm.toEmbedding=x := by
  ext b
  change a.symm (y b)=x b
  rw [← he]
  exact a.symm_apply_apply _

omit [Fintype A] [Fintype B] [Fintype X] in
lemma blockPerm_inl (e : A ⊕ B ≃ X) (a : Equiv.Perm A) (u : A) :
    blockPerm e a (e (Sum.inl u))=e (Sum.inl (a u)) := by
  change e (Equiv.sumCongr a (1:Equiv.Perm B) (e.symm (e (Sum.inl u))))=_
  rw [e.symm_apply_apply]
  rfl

omit [Fintype X] in
lemma placement_subgroup_complement (e : A ⊕ B ≃ X) (a : Equiv.Perm X)
    (x y : B ↪ X) (he : x.trans a.toEmbedding=y) :
    ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)).1 =
      ((placementComplementEquiv e x).trans (complementMap a x y he)).trans
        (placementComplementEquiv e y).symm := by
  have hh := placementCoset_subgroup e a y
  rw [placement_inverse_event a x y he] at hh
  ext u
  apply (placementComplementEquiv e y).injective
  apply Subtype.ext
  have hu := congrArg (placementSection e y) (Equiv.congr_fun hh (e (Sum.inl u)))
  simp only [blockPerm_inl,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
    Equiv.apply_symm_apply] at hu
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  change placementSection e y (e (Sum.inl _)) = a (placementSection e x (e (Sum.inl u)))
  simpa only [Equiv.Perm.inv_def] using hu

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h h' : ℕ} {bits : Fin b → ℕ}
variable {H : PathFamily bits h} {H' : PathFamily bits h'}

def PathExtension.restrictChoice (E : PathExtension H H')
    (g : ConditionalChoices H') : ConditionalChoices H :=
  ⟨g.val,E.pathEvent_mono g.property⟩

lemma PathExtension.choiceWeight (E : PathExtension H H') (z : ℝ)
    (hpos : conditionalNormalizer H' z ≠ 0) (g : ConditionalChoices H') :
    conditionalChoiceWeight H z (E.restrictChoice g) =
      (conditionalNormalizer H' z / conditionalNormalizer H z) *
        conditionalChoiceWeight H' z g := by
  unfold conditionalChoiceWeight PathExtension.restrictChoice
  simp only
  field_simp

lemma PathExtension.sum_restrict {V : Type*} [AddCommMonoid V]
    (E : PathExtension H H') (f : ConditionalChoices H' → V) :
    (∑g : ConditionalChoices H,
      if hg : pathEvent H' g.val then f ⟨g.val,hg⟩ else 0) =
      ∑g : ConditionalChoices H',f g := by
  have hL := sum_dite_zero (pathEvent H)
    (fun (g : GridChoices bits) (_ : pathEvent H g) =>
      if hg' : pathEvent H' g then f ⟨g,hg'⟩ else 0)
  have hR := sum_dite_zero (pathEvent H') (fun g hg => f ⟨g,hg⟩)
  refine Eq.trans ?_ (Eq.trans hL.symm (Eq.trans ?_ (Eq.trans hR ?_)))
  · apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro g _
    by_cases hg : pathEvent H' g
    · simp only [hg,E.pathEvent_mono hg,dite_eq_left]
    · simp [hg]
  · apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _
    rfl

lemma PathExtension.conditional_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : PathExtension H H') (z : ℝ) (hpos : conditionalNormalizer H' z ≠ 0)
    (f : ConditionalChoices H' → V) :
    (∑g : ConditionalChoices H,
      if hg : pathEvent H' g.val then conditionalChoiceWeight H z g • f ⟨g.val,hg⟩ else 0) =
      (conditionalNormalizer H' z / conditionalNormalizer H z) •
        ∑g : ConditionalChoices H', conditionalChoiceWeight H' z g • f g := by
  rw [Finset.smul_sum]
  simp_rw [← mul_smul]
  rw [← E.sum_restrict (fun g =>
    ((conditionalNormalizer H' z / conditionalNormalizer H z) *
      conditionalChoiceWeight H' z g) • f g)]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs with hg
  · rw [← E.choiceWeight z hpos ⟨g.val,hg⟩]
    rfl
  · rfl

end BinaryCoordinateSweeps

end

end OAI
