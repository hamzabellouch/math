import OAI.GroupTheory.PolycyclicRecognition.Geometry.PresentationRotation

namespace OAI

/-! # Exactness at the completed connecting maps -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteCohomology_boundary_exact (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology (p + 1) S.X₁)
    (hx : shiftedCompletedCohomologyMap (p + 1) S.f x = 0) :
    ∃ y : ShiftedCompletedCohomology p S.X₃, shiftedCompleteBoundary p S hS y = x := by
  let R := presentationRotation S hS
  let hR := presentationRotation_shortExact S hS
  let z := shiftedCompletedCohomologyMap (p + 1) (rotationInl S) x
  have hz : shiftedCompletedCohomologyMap (p + 1) R.g z = 0 := by
    change shiftedCompletedCohomologyMap (p + 1) (rotationProjection S hS)
      (shiftedCompletedCohomologyMap (p + 1) (rotationInl S) x) = 0
    rw [← shiftedCompletedCohomologyMap_comp_apply, rotationInl_projection]
    exact hx
  obtain ⟨a, ha⟩ := shiftedCompleteCohomology_middle_exact (p + 1) R hR z hz
  change ShiftedCompletedCohomology (p + 1) (normalizedSyzygy S.X₃) at a
  refine ⟨shiftedSyzygyAddEquiv p S.X₃ a, ?_⟩
  rw [shiftedCompleteBoundary_apply, AddEquiv.symm_apply_apply]
  have h := congrArg (shiftedCompletedCohomologyMap (p + 1) (rotationFst S)) ha
  change shiftedCompletedCohomologyMap (p + 1) (rotationFst S)
    (shiftedCompletedCohomologyMap (p + 1) (rotationInclusion S hS) a) =
      shiftedCompletedCohomologyMap (p + 1) (rotationFst S)
        (shiftedCompletedCohomologyMap (p + 1) (rotationInl S) x) at h
  rw [← shiftedCompletedCohomologyMap_comp_apply, ← shiftedCompletedCohomologyMap_comp_apply,
    rotationInclusion_fst, rotationInl_fst] at h
  have hi := ConcreteCategory.congr_hom ((shiftedCompletedCohomologyFunctor (p + 1)).map_id S.X₁) x
  exact h.trans hi

theorem presentationKernelMap_normalized_stable (A : Rep.{0} ℤ G) :
    stableRepresentationClass _ _
        (presentationKernelMap (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A)) =
      stableRepresentationClass _ _ (𝟙 (normalizedSyzygy A)) := by
  have h := normalizedSyzygy_stable_of_lift (𝟙 A)
    (presentationFreeLift (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A))
    (by
      have h := presentationFreeLift_g (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A)
      change presentationFreeLift (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A) ≫
        normalizedFreeAugmentation A = normalizedFreeAugmentation A at h
      exact h.trans (Category.comp_id (normalizedFreeAugmentation A)).symm)
    (presentationKernelMap (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A))
    (presentationKernelMap_f (normalizedSyzygySequence A) (normalizedSyzygySequence_shortExact A))
  change stableRepresentationClass _ _ (normalizedSyzygyFunctor.map (𝟙 A)) = _ at h
  rw [CategoryTheory.Functor.map_id] at h
  exact h.symm

theorem shiftedCompleteBoundary_rotation (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology p S.X₂) :
    shiftedSyzygyAddEquiv p S.X₃
      (shiftedCompleteBoundary p (presentationRotation S hS) (presentationRotation_shortExact S hS) x) =
        -shiftedCompletedCohomologyMap p S.g x := by
  let F := shiftedCompletedCohomologyFunctor (p + 1) (G := G)
  let a : normalizedSyzygy S.X₂ ⟶ normalizedSyzygy S.X₃ :=
    presentationKernelMap (presentationRotation S hS) (presentationRotation_shortExact S hS)
  let b : normalizedSyzygy S.X₃ ⟶ normalizedSyzygy S.X₃ :=
    presentationKernelMap (normalizedSyzygySequence S.X₃) (normalizedSyzygySequence_shortExact S.X₃)
  change shiftedSyzygyAddEquiv p S.X₃
    (shiftedCompletedCohomologyMap (p + 1) a ((shiftedSyzygyAddEquiv p S.X₂).symm x)) = _
  have h := shiftedCompleteFunctor_map_eq_of_stable_eq (p + 1) _ _
    (presentationKernelMap_stable_natural (presentationRotation_shortExact S hS)
      (normalizedSyzygySequence_shortExact S.X₃) (rotationToNormalized S hS))
  change F.map (normalizedSyzygyMap S.g ≫ b) = F.map (a ≫ (-𝟙 (normalizedSyzygy S.X₃))) at h
  have hn := shiftedCompleteFunctor_map_eq_of_stable_eq (p + 1) _ _
    (presentationKernelMap_normalized_stable S.X₃)
  change F.map b = F.map (𝟙 (normalizedSyzygy S.X₃)) at hn
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hn,
    CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_neg,
    CategoryTheory.Functor.map_id, Preadditive.comp_neg, Category.comp_id] at h
  have he := congrArg ModuleCat.Hom.hom h
  change shiftedCompletedCohomologyMap (p + 1) (normalizedSyzygyMap S.g) =
    -shiftedCompletedCohomologyMap (p + 1) a at he
  have hv := LinearMap.congr_fun he ((shiftedSyzygyAddEquiv p S.X₂).symm x)
  change shiftedCompletedCohomologyMap (p + 1) (normalizedSyzygyMap S.g)
      ((shiftedSyzygyAddEquiv p S.X₂).symm x) =
    -(shiftedCompletedCohomologyMap (p + 1) a ((shiftedSyzygyAddEquiv p S.X₂).symm x)) at hv
  have hv' := congrArg Neg.neg hv
  simp only [neg_neg] at hv'
  rw [← hv', map_neg, shiftedSyzygyEquiv_natural, AddEquiv.apply_symm_apply]

theorem rotation_complete_retract (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G))
    (x : ShiftedCompletedCohomology p (rotationMiddle S)) :
    shiftedCompletedCohomologyMap p (rotationInl S)
      (shiftedCompletedCohomologyMap p (rotationFst S) x) = x := by
  rw [← shiftedCompletedCohomologyMap_comp_apply]
  have h := shiftedCompleteFunctor_map_eq_of_stable_eq p _ _ (rotation_fst_inl_stable S)
  rw [CategoryTheory.Functor.map_id] at h
  exact ConcreteCategory.congr_hom h x

theorem rotation_complete_inclusion_zero (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (x : ShiftedCompletedCohomology p (normalizedSyzygy S.X₃))
    (hx : shiftedCompletedCohomologyMap p (presentationKernelMap S hS) x = 0) :
    shiftedCompletedCohomologyMap p (rotationInclusion S hS) x = 0 := by
  let z := shiftedCompletedCohomologyMap p (rotationInclusion S hS) x
  have hz : shiftedCompletedCohomologyMap p (rotationFst S) z = 0 := by
    change shiftedCompletedCohomologyMap p (rotationFst S)
      (shiftedCompletedCohomologyMap p (rotationInclusion S hS) x) = 0
    rw [← shiftedCompletedCohomologyMap_comp_apply, rotationInclusion_fst]
    exact hx
  change z = 0
  rw [← rotation_complete_retract p S z, hz, map_zero]

theorem shiftedCompleteCohomology_map_boundary_exact (p : ℕ)
    (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact)
    (x : ShiftedCompletedCohomology p S.X₃) (hx : shiftedCompleteBoundary p S hS x = 0) :
    ∃ y : ShiftedCompletedCohomology p S.X₂, shiftedCompletedCohomologyMap p S.g y = x := by
  let a := (shiftedSyzygyAddEquiv p S.X₃).symm x
  have ha : shiftedCompletedCohomologyMap (p + 1) (presentationKernelMap S hS) a = 0 := hx
  have hj := rotation_complete_inclusion_zero (p + 1) S hS a ha
  obtain ⟨b, hb⟩ := shiftedCompleteCohomology_boundary_exact p
    (presentationRotation S hS) (presentationRotation_shortExact S hS) a hj
  change ShiftedCompletedCohomology p S.X₂ at b
  refine ⟨-b, ?_⟩
  have h := shiftedCompleteBoundary_rotation p S hS b
  rw [hb, show shiftedSyzygyAddEquiv p S.X₃ a = x from
    (shiftedSyzygyAddEquiv p S.X₃).apply_symm_apply x] at h
  rw [map_neg]
  exact h.symm

end PolycyclicRecognition

end

end OAI
