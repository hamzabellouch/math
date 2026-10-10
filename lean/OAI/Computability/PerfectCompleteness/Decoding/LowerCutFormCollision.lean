import OAI.Computability.PerfectCompleteness.Decoding.LowerCutScalarProjectionLemmas

namespace OAI

section

namespace PerfectCompleteness.LowerCutFormCollision

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n height t : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (inside : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)

def nativeScalar (f : H inside) :
    HierarchicalDecoderTables.LowerH (CutSlotAssembly.fill path outside inside) upper level d :=
  LowerCutDecoderForm.spaceEquiv path (CutSlotAssembly.fill path outside inside)
    upper level d hnode
    (CutNativeForms.spaceCast (CleanPhysicalReplay.cutSlots_fill path outside inside).symm f)

def nativeForm
    (answer : HierarchicalDecoderTables.Answer
      (CutSlotAssembly.fill path outside inside) upper level d) :
    ChildBilinearCollisionTransfer.ParentForm inside :=
  CutNativeForms.formCast (CleanPhysicalReplay.cutSlots_fill path outside inside)
    (LowerCutDecoderForm.form path (CutSlotAssembly.fill path outside inside)
      upper level d hnode answer)

private theorem formCast_apply_inverse
    {source target : Slots branch (height + 1) → Fin t → MixedSupport.Slot}
    (h : source = target) (F : ChildBilinearCollisionTransfer.ParentForm source)
    (f g : H target) :
    CutNativeForms.formCast h F f g =
      F (CutNativeForms.spaceCast h.symm f) (CutNativeForms.spaceCast h.symm g) := by
  cases h
  rfl

theorem nativeForm_apply
    (answer : HierarchicalDecoderTables.Answer
      (CutSlotAssembly.fill path outside inside) upper level d) (f g : H inside) :
    nativeForm path outside inside upper level d hnode answer f g =
      OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (CutSlotAssembly.fill path outside inside) upper level d) answer
        (nativeScalar path outside inside upper level d hnode f)
        (nativeScalar path outside inside upper level d hnode g) := by
  unfold nativeForm
  rw [formCast_apply_inverse]
  rfl

variable (projected : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (projection : ∀ s k, MixedSupport.Projection (inside s k) (projected s k))

theorem nativeScalar_HPullback (f : H projected) :
    nativeScalar path outside inside upper level d hnode (HPullback projection f) =
      HPullback (ChildBlockProjection.nodeProjection
        (CutProjectionAssembly.fillProjection path outside inside projected projection)
        (HierarchicalLeftDecoder.LowerNode upper level d))
        (nativeScalar path outside projected upper level d hnode f) :=
  LowerCutScalarProjection.spaceEquiv_fill_HPullback path outside inside projected
    upper level d hnode projection f

theorem restricted_on_native
    (answer₀ answer₁ : Option (HierarchicalDecoderTables.Answer
      (CutSlotAssembly.fill path outside inside) upper level d))
    (U : Submodule F2 (H inside)) (hU : U ≤ LinearMap.range (HPullback projection))
    (hcollision : BilinearCollisionTransfer.restrictedCollision
      (answer₀.map (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (CutSlotAssembly.fill path outside inside) upper level d)))
      (answer₁.map (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (CutSlotAssembly.fill path outside inside) upper level d)))
      (LinearMap.range (HPullback (ChildBlockProjection.nodeProjection
        (CutProjectionAssembly.fillProjection path outside inside projected projection)
        (HierarchicalLeftDecoder.LowerNode upper level d)))) = true) :
    BilinearCollisionTransfer.restrictedCollision
      (answer₀.map (nativeForm path outside inside upper level d hnode))
      (answer₁.map (nativeForm path outside inside upper level d hnode)) U = true := by
  obtain ⟨F, G, hF, hG, heq⟩ := of_decide_eq_true hcollision
  cases answer₀ with
  | none => cases hF
  | some a₀ =>
      cases answer₁ with
      | none => cases hG
      | some a₁ =>
          have hF' := Option.some.inj hF
          have hG' := Option.some.inj hG
          rw [← hF', ← hG'] at heq
          apply decide_eq_true
          refine ⟨nativeForm path outside inside upper level d hnode a₀,
            nativeForm path outside inside upper level d hnode a₁, rfl, rfl, ?_⟩
          intro f hf g hg
          rw [nativeForm_apply, nativeForm_apply]
          obtain ⟨f', hf'⟩ := hU hf
          obtain ⟨g', hg'⟩ := hU hg
          have hfmem : nativeScalar path outside inside upper level d hnode f ∈
              LinearMap.range (HPullback (ChildBlockProjection.nodeProjection
                (CutProjectionAssembly.fillProjection path outside inside projected projection)
                (HierarchicalLeftDecoder.LowerNode upper level d))) := by
            refine ⟨nativeScalar path outside projected upper level d hnode f', ?_⟩
            rw [← nativeScalar_HPullback, hf']
          have hgmem : nativeScalar path outside inside upper level d hnode g ∈
              LinearMap.range (HPullback (ChildBlockProjection.nodeProjection
                (CutProjectionAssembly.fillProjection path outside inside projected projection)
                (HierarchicalLeftDecoder.LowerNode upper level d))) := by
            refine ⟨nativeScalar path outside projected upper level d hnode g', ?_⟩
            rw [← nativeScalar_HPullback, hg']
          exact heq _ hfmem _ hgmem

end
end PerfectCompleteness.LowerCutFormCollision

end

end OAI
