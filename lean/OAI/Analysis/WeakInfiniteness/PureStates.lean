import Mathlib
import OAI.Analysis.WeakInfiniteness.States

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology ComplexOrder

section States

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def realStateSpace : Set (WeakDual ℝ (selfAdjoint A)) :=
  {f | ‖WeakDual.toStrongDual f‖ ≤ 1 ∧ f 1=1}

omit [PartialOrder A] [StarOrderedRing A] in
lemma realStateSpace_isCompact : IsCompact (realStateSpace A) := by
  have h := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ (selfAdjoint A)) 1).inter_right
    (isClosed_eq (WeakDual.eval_continuous (1 : selfAdjoint A))
      (continuous_const : Continuous (fun _ : WeakDual ℝ (selfAdjoint A) => (1 : ℝ))))
  convert h using 1
  ext f
  change (‖WeakDual.toStrongDual f‖ ≤ 1 ∧ f 1=1) ↔
    (dist (WeakDual.toStrongDual f) 0 ≤ 1 ∧ f 1=1)
  have hd := dist_zero_right (WeakDual.toStrongDual f)
  rw [hd]

variable {A}

def realStateEvaluation (b : selfAdjoint A) : WeakDual ℝ (selfAdjoint A) →L[ℝ] ℝ where
  toFun f := f b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := WeakDual.eval_continuous b

omit [PartialOrder A] [StarOrderedRing A] in
lemma realState_le_norm {f : WeakDual ℝ (selfAdjoint A)} (hf : f ∈ realStateSpace A)
    (b : selfAdjoint A) : f b ≤ ‖b‖ := by
  calc
    f b ≤ ‖f b‖ := Real.le_norm_self _
    _ ≤ ‖WeakDual.toStrongDual f‖*‖b‖ := (WeakDual.toStrongDual f).le_opNorm _
    _ ≤ 1*‖b‖ := mul_le_mul_of_nonneg_right hf.1 (norm_nonneg _)
    _ = ‖b‖ := one_mul _

lemma exists_norming_real_state [Nontrivial A] (b : A) (hb : 0 ≤ b) :
    ∃ f ∈ realStateSpace A,f ⟨b,hb.isSelfAdjoint⟩=‖b‖ := by
  let b' : selfAdjoint A := ⟨b,hb.isSelfAdjoint⟩
  have hn : ‖b'+1‖=‖b‖+1 := norm_add_one_of_nonneg b hb
  obtain ⟨f,hf,hfb⟩ := exists_dual_vector ℝ (b'+1) (by rw [hn]; positivity)
  have hf1 : f 1 ≤ 1 := calc
    f 1 ≤ ‖f 1‖ := Real.le_norm_self _
    _ ≤ ‖f‖*‖(1 : selfAdjoint A)‖ := f.le_opNorm _
    _ = 1 := by rw [hf]; change 1*‖(1 : A)‖=1; simp
  have hfb' : f b' ≤ ‖b‖ := calc
    f b' ≤ ‖f b'‖ := Real.le_norm_self _
    _ ≤ ‖f‖*‖b'‖ := f.le_opNorm _
    _ = ‖b‖ := by rw [hf,one_mul]; rfl
  rw [map_add,hn] at hfb
  change f b'+f 1=‖b‖+1 at hfb
  have hfone : f 1=1 := by linarith
  have hfnorm : f b'=‖b‖ := by linarith
  refine ⟨f,⟨hf.le,hfone⟩,hfnorm⟩

theorem exists_extreme_norming_real_state [Nontrivial A] (b : A) (hb : 0 ≤ b) :
    ∃ f ∈ (realStateSpace A).extremePoints ℝ,f ⟨b,hb.isSelfAdjoint⟩=‖b‖ := by
  let b' : selfAdjoint A := ⟨b,hb.isSelfAdjoint⟩
  let S := {f ∈ realStateSpace A | ∀ g ∈ realStateSpace A,g b' ≤ f b'}
  have hexposed : IsExposed ℝ (realStateSpace A) S := by
    intro _
    exact ⟨realStateEvaluation b',rfl⟩
  obtain ⟨g,hg,hgb⟩ := exists_norming_real_state b hb
  have hS : S.Nonempty := by
    refine ⟨g,hg,?_⟩
    intro k hk
    rw [hgb]
    exact realState_le_norm hk b'
  let : LocallyConvexSpace ℝ (WeakDual ℝ (selfAdjoint A)) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℝ (selfAdjoint A))))
  obtain ⟨f,hf⟩ := (hexposed.isCompact (realStateSpace_isCompact A)).extremePoints_nonempty hS
  refine ⟨f,hexposed.isExtreme.extremePoints_subset_extremePoints hf,?_⟩
  apply le_antisymm (realState_le_norm hf.1.1 b')
  change ‖b‖ ≤ f b'
  rw [← hgb]
  exact hf.1.2 g hg

def realStateComplexification (f : WeakDual ℝ (selfAdjoint A))
    (hf : f ∈ realStateSpace A) : A →ₚ[ℂ] ℂ :=
  positiveComplexification (WeakDual.toStrongDual f) hf.1 hf.2

lemma realStateComplexification_apply (f : WeakDual ℝ (selfAdjoint A))
    (hf : f ∈ realStateSpace A) (b : selfAdjoint A) :
    realStateComplexification f hf (b : A)=(f b : ℂ) :=
  positiveComplexification_apply _ _ _ _

lemma realStateComplexification_one (f : WeakDual ℝ (selfAdjoint A))
    (hf : f ∈ realStateSpace A) : realStateComplexification f hf 1=1 := by
  change realStateComplexification f hf ((1 : selfAdjoint A) : A)=1
  rw [realStateComplexification_apply,hf.2,Complex.ofReal_one]

end States

end

end WeakPureInfiniteness
end

end OAI
