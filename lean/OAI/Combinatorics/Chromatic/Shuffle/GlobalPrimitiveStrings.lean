import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalPBWBasis
import OAI.Combinatorics.Chromatic.Shuffle.GlobalLocalPrimitives
import OAI.Combinatorics.Chromatic.Walls.DirectSumSubtype

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable local instance (d : I → ℕ) (W : ℤ) : AddCommGroup (primitiveSpace a c η hc θ Fact.out d W) := Submodule.addCommGroup _
noncomputable local instance (d : I → ℕ) (W : ℤ) : Module ℚ (primitiveSpace a c η hc θ Fact.out d W) := Submodule.module _

abbrev NonzeroSlopeWeight := {k : SlopeWeight c η hc θ // k.1.val≠0}

noncomputable def localPrimitiveInclusion (k : NonzeroSlopeWeight c η hc θ) :
    primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2 →ₗ[ℚ]
      unitalComponent a c η hc θ k.val :=
  (unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).symm.toLinearMap ∘ₗ
    (primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2).subtype

lemma localPrimitiveInclusion_injective (k : NonzeroSlopeWeight c η hc θ) :
    Function.Injective (localPrimitiveInclusion a c η hc θ k) :=
  (unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).symm.injective.comp Subtype.val_injective

noncomputable def localPrimitiveGlobal (k : NonzeroSlopeWeight c η hc θ) :
    primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2 →ₗ[ℚ] UnitalShuffle a c η hc θ :=
  DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k.val ∘ₗ localPrimitiveInclusion a c η hc θ k

lemma localPrimitiveGlobal_mem (k : NonzeroSlopeWeight c η hc θ)
    (x : primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) :
    localPrimitiveGlobal a c η hc θ k x ∈ globalPrimitives a c η hc θ := by
  apply (globalPrimitive_iff_local a c η hc θ k.val.1 k.property k.val.2 _).mpr
  change unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2
    ((unitalGradeNonzeroEquiv a c η hc θ k.val.1.val k.property k.val.2).symm x.val)∈_
  rw [LinearEquiv.apply_symm_apply]
  exact x.property

noncomputable def localPrimitiveSumToGlobal :
    (⨁ k : NonzeroSlopeWeight c η hc θ,primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) →ₗ[ℚ]
      UnitalShuffle a c η hc θ :=
  subfamilyInclusion (unitalComponent a c η hc θ) (fun k=>k.1.val≠0) ∘ₗ
    DirectSum.lmap (localPrimitiveInclusion a c η hc θ)

lemma localPrimitiveSumToGlobal_injective : Function.Injective (localPrimitiveSumToGlobal a c η hc θ) :=
  (subfamilyInclusion_injective (unitalComponent a c η hc θ) (fun k=>k.1.val≠0)).comp
    ((DirectSum.lmap_injective _).mpr (localPrimitiveInclusion_injective a c η hc θ))

lemma localPrimitiveSumToGlobal_lof (k : NonzeroSlopeWeight c η hc θ)
    (x : primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) :
    localPrimitiveSumToGlobal a c η hc θ (DirectSum.lof ℚ _
      (fun k : NonzeroSlopeWeight c η hc θ=>primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) k x)=
      localPrimitiveGlobal a c η hc θ k x := by
  change subfamilyInclusion (unitalComponent a c η hc θ) (fun k=>k.1.val≠0)
    (DirectSum.lmap (localPrimitiveInclusion a c η hc θ)
      (DirectSum.lof ℚ _ _ k x))=_
  rw [DirectSum.lmap_lof]
  simp only [subfamilyInclusion,DirectSum.toModule_lof,localPrimitiveGlobal,LinearMap.comp_apply]

abbrev GlobalStringIndex := Σ k : NonzeroSlopeWeight c η hc θ,
  Σ _ : ℕ,StringBaseIndex a c η hc θ Fact.out k.val.1.val k.val.2

noncomputable def globalStringFamily (i : GlobalStringIndex a c η hc θ) : UnitalShuffle a c η hc θ :=
  localPrimitiveGlobal a c η hc θ i.1
    (homogeneousPrimitiveStringBasis a c η hc θ Fact.out i.1.val.1.val i.1.val.2 i.1.property i.2)

lemma globalStringFamily_mem (i : GlobalStringIndex a c η hc θ) :
    globalStringFamily a c η hc θ i ∈ globalPrimitives a c η hc θ :=
  localPrimitiveGlobal_mem a c η hc θ i.1 _

lemma globalStringFamily_weight (i : GlobalStringIndex a c η hc θ) :
    globalStringFamily a c η hc θ i ∈ globalHomogeneous a c η hc θ i.1.val :=
  ⟨localPrimitiveInclusion a c η hc θ i.1 _,rfl⟩

lemma globalStringFamily_independent : LinearIndependent ℚ (globalStringFamily a c η hc θ) := by
  have hh := directSum_map_independent
    (fun k : NonzeroSlopeWeight c η hc θ=>primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2)
    (fun k=>homogeneousPrimitiveStringBasis a c η hc θ Fact.out k.val.1.val k.val.2 k.property)
    (fun k=>(homogeneousPrimitiveStringBasis a c η hc θ Fact.out k.val.1.val k.val.2 k.property).linearIndependent)
    (localPrimitiveSumToGlobal a c η hc θ) (localPrimitiveSumToGlobal_injective a c η hc θ)
  have he : globalStringFamily a c η hc θ=(fun i : GlobalStringIndex a c η hc θ=>
      localPrimitiveSumToGlobal a c η hc θ (DirectSum.lof ℚ _ _ i.1
      (homogeneousPrimitiveStringBasis a c η hc θ Fact.out i.1.val.1.val i.1.val.2 i.1.property i.2))) := by
    funext i
    exact (localPrimitiveSumToGlobal_lof a c η hc θ i.1 _).symm
  rw [he]
  exact hh

lemma localPrimitiveGlobal_mem_span (k : NonzeroSlopeWeight c η hc θ)
    (x : primitiveSpace a c η hc θ Fact.out k.val.1.val k.val.2) :
    localPrimitiveGlobal a c η hc θ k x∈Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ)) := by
  have he := congrArg (Submodule.map (localPrimitiveGlobal a c η hc θ k))
    (homogeneousPrimitiveStringBasis a c η hc θ Fact.out k.val.1.val k.val.2 k.property).span_eq
  rw [Submodule.map_span,Submodule.map_top] at he
  have hx : localPrimitiveGlobal a c η hc θ k x∈LinearMap.range (localPrimitiveGlobal a c η hc θ k) := ⟨x,rfl⟩
  rw [←he] at hx
  apply Submodule.span_mono (s:=_) (t:=Set.range (globalStringFamily a c η hc θ)) ?_ hx
  rintro y ⟨z,⟨i,rfl⟩,rfl⟩
  exact ⟨⟨k,i⟩,rfl⟩

lemma homogeneousPrimitive_mem_stringSpan (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k)
    (hx : DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x∈globalPrimitives a c η hc θ) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x∈Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ)) := by
  by_cases hd : k.1.val=0
  · rw [zeroDimension_lof_scalar a c η hc θ k hd x,globalPrimitive_counit a c η hc θ hx,zero_smul]
    exact Submodule.zero_mem _
  · let y : primitiveSpace a c η hc θ Fact.out k.1.val k.2 :=
      ⟨unitalGradeNonzeroEquiv a c η hc θ k.1.val hd k.2 x,
        (globalPrimitive_iff_local a c η hc θ k.1 hd k.2 x).mp hx⟩
    have h:=localPrimitiveGlobal_mem_span a c η hc θ ⟨k,hd⟩ y
    change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k
      ((unitalGradeNonzeroEquiv a c η hc θ k.1.val hd k.2).symm
        (unitalGradeNonzeroEquiv a c η hc θ k.1.val hd k.2 x))∈_ at h
    rwa [LinearEquiv.symm_apply_apply] at h

lemma globalStringFamily_span :
    Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ))=globalPrimitives a c η hc θ := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx=>by obtain ⟨i,rfl⟩:=hx; exact globalStringFamily_mem a c η hc θ i)
  · intro x hx
    rw [←globalPrimitiveLog_on_primitive a c η hc θ hx]
    have hm : ∀ y : UnitalShuffle a c η hc θ,globalPrimitiveLog a c η hc θ y∈
        Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ)) := by
      intro y
      induction y using DirectSum.induction_on with
      | zero => simpa only [map_zero] using (Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ))).zero_mem
      | add y z hy hz => simpa only [map_add] using (Submodule.span ℚ (Set.range (globalStringFamily a c η hc θ))).add_mem hy hz
      | of k y =>
        obtain ⟨z,hz⟩ := globalPrimitiveLog_homogeneous a c η hc θ k y
        change globalPrimitiveLog a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k y)∈_
        change DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k z=globalPrimitiveLog a c η hc θ _ at hz
        rw [←hz]
        apply homogeneousPrimitive_mem_stringSpan a c η hc θ k z
        rw [hz]
        exact (mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ _)
    exact hm x

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable instance globalStringIndexLinearOrder : LinearOrder (GlobalStringIndex a c η hc θ) :=
  linearOrderOfSTO WellOrderingRel

noncomputable def globalStringPBWBasis :
    Module.Basis (PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)) ℚ
      (UnitalShuffle a c η hc θ) :=
  primitiveBasisPBW a c η hc θ (globalStringFamily a c η hc θ) (fun i=>i.1.val)
    (globalStringFamily_weight a c η hc θ) (globalStringFamily_mem a c η hc θ)
    (globalStringFamily_span a c η hc θ) (globalStringFamily_independent a c η hc θ)

lemma globalStringPBWBasis_apply (l : PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)) :
    globalStringPBWBasis a c η hc θ l=primitiveWord a c η hc θ (globalStringFamily a c η hc θ) l.val :=
  primitiveBasisPBW_apply a c η hc θ _ _ _ _ _ _ l

lemma globalStringPBWBasis_weight (l : PBWWord a c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val)) :
    globalStringPBWBasis a c η hc θ l∈globalHomogeneous a c η hc θ
      (wordWeight c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val) l.val) := by
  rw [globalStringPBWBasis_apply]
  exact primitiveWord_homogeneous a c η hc θ _ _ (globalStringFamily_weight a c η hc θ) l.val

end ElementaryPositivity.RawShuffle

end

end OAI
