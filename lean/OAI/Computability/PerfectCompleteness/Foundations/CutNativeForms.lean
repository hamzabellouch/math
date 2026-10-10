import OAI.Computability.PerfectCompleteness.Construction.SourceLocalOddLists
import OAI.Computability.PerfectCompleteness.Foundations.CutSlotAssembly

namespace OAI

section

namespace PerfectCompleteness.CutNativeForms

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces

variable {branch : Nat → Nat} {n k t : Nat}

theorem nodeSlots_fill (lower : Nodes branch n)
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (inside : Slots branch (Nodes.height lower) → Fin t → MixedSupport.Slot) :
    nodeSlots (CutSlotAssembly.fill (Nodes.path lower) outside inside) lower = inside := by
  funext s
  exact CutSlotAssembly.fill_at_cut (Nodes.path lower) outside inside s

theorem nodeSlots_fill_of_agree (lower : Nodes branch n)
    (p : Path branch n (Nodes.height lower))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (inside : Slots branch (Nodes.height lower) → Fin t → MixedSupport.Slot)
    (hag : ∀ s, p.slotEmbedding s = (Nodes.path lower).slotEmbedding s) :
    nodeSlots (CutSlotAssembly.fill p outside inside) lower = inside := by
  funext s
  change CutSlotAssembly.fill p outside inside ((Nodes.path lower).slotEmbedding s) = inside s
  rw [← hag s]
  exact CutSlotAssembly.fill_at_cut p outside inside s

section Equality

variable {a b c d : Slots branch k → Fin t → MixedSupport.Slot}

def spaceCast (hab : a = b) : H a ≃ₗ[F2] H b := by
  cases hab
  exact LinearEquiv.refl F2 (H a)

def squareCast (hab : a = b) : squareSpace (H a) ≃ₗ[F2] squareSpace (H b) := by
  cases hab
  exact LinearEquiv.refl F2 (squareSpace (H a))

def dualCast (hab : a = b) (z : Module.Dual F2 (squareSpace (H a))) :
    Module.Dual F2 (squareSpace (H b)) := by
  cases hab
  exact z

def formCast (hab : a = b) (F : SourceLocalOddLists.Form a) : SourceLocalOddLists.Form b := by
  cases hab
  exact F

@[simp] theorem dualCast_apply (hab : a = b)
    (z : Module.Dual F2 (squareSpace (H a))) (f : squareSpace (H a)) :
    dualCast hab z (squareCast hab f) = z f := by
  cases hab
  rfl

@[simp] theorem formCast_apply (hab : a = b) (F : SourceLocalOddLists.Form a)
    (f g : H a) : formCast hab F (spaceCast hab f) (spaceCast hab g) = F f g := by
  cases hab
  rfl

theorem squareCast_product (hab : a = b) (f g : H a) :
    squareCast hab (OddListExtraction.productElement (H a) f g) =
      OddListExtraction.productElement (H b) (spaceCast hab f) (spaceCast hab g) := by
  cases hab
  rfl

theorem formCast_multiplication (hab : a = b)
    (z : Module.Dual F2 (squareSpace (H a))) :
    formCast hab (OddListExtraction.multiplicationForm (H a) z) =
      OddListExtraction.multiplicationForm (H b) (dualCast hab z) := by
  cases hab
  rfl

theorem formRank_formCast (hab : a = b) (F : SourceLocalOddLists.Form a) :
    OddListExtraction.formRank (H b) (formCast hab F) =
      OddListExtraction.formRank (H a) F := by
  cases hab
  rfl

theorem squareCast_one (hab : a = b)
    (ha : (1 : Domain a → F2) ∈ squareSpace (H a))
    (hb : (1 : Domain b → F2) ∈ squareSpace (H b)) :
    squareCast hab ⟨1, ha⟩ = ⟨1, hb⟩ := by
  cases hab
  rfl

theorem dualCast_one (hab : a = b) (z : Module.Dual F2 (squareSpace (H a)))
    (ha : (1 : Domain a → F2) ∈ squareSpace (H a))
    (hb : (1 : Domain b → F2) ∈ squareSpace (H b)) :
    dualCast hab z ⟨1, hb⟩ = z ⟨1, ha⟩ := by
  cases hab
  rfl

def oneElement (slots : Slots branch k → Fin t → MixedSupport.Slot)
    (hbranch : ∀ j < k, 0 < branch j) : squareSpace (H slots) :=
  ⟨(1 : Domain slots → F2), TreeSourceSpaces.one_mem_squareSpace slots hbranch⟩

theorem dualCast_normalized (hab : a = b) (hbranch : ∀ j < k, 0 < branch j)
    (z : Module.Dual F2 (squareSpace (H a)))
    (hnorm : z (oneElement a hbranch) = 1) :
    dualCast hab z (oneElement b hbranch) = 1 := by
  cases hab
  exact hnorm

def projectionCast (hab : a = b) (hcd : c = d)
    (p : ∀ s j, MixedSupport.Projection (a s j) (c s j)) :
    ∀ s j, MixedSupport.Projection (b s j) (d s j) := by
  cases hab
  cases hcd
  exact p

theorem spaceCast_HPullback (hab : a = b) (hcd : c = d)
    (p : ∀ s j, MixedSupport.Projection (a s j) (c s j)) (f : H c) :
    spaceCast hab (HPullback p f) =
      HPullback (projectionCast hab hcd p) (spaceCast hcd f) := by
  cases hab
  cases hcd
  rfl

theorem formCast_projection_agreement (hab : a = b) (hcd : c = d)
    (p : ∀ s j, MixedSupport.Projection (a s j) (c s j))
    (F : SourceLocalOddLists.Form a) (G : SourceLocalOddLists.Form c)
    (hagree : ∀ f g, G f g = F (HPullback p f) (HPullback p g)) :
    ∀ f g, formCast hcd G f g = formCast hab F
      (HPullback (projectionCast hab hcd p) f)
      (HPullback (projectionCast hab hcd p) g) := by
  cases hab
  cases hcd
  exact hagree

theorem dualCast_projection_agreement (hab : a = b) (hcd : c = d)
    (p : ∀ s j, MixedSupport.Projection (a s j) (c s j))
    (z : Module.Dual F2 (squareSpace (H a))) (G : SourceLocalOddLists.Form c)
    (hagree : ∀ f g, G f g = OddListExtraction.multiplicationForm (H a) z
      (HPullback p f) (HPullback p g)) :
    ∀ f g, formCast hcd G f g =
      OddListExtraction.multiplicationForm (H b) (dualCast hab z)
        (HPullback (projectionCast hab hcd p) f)
        (HPullback (projectionCast hab hcd p) g) := by
  cases hab
  cases hcd
  exact hagree

end Equality

section Native

variable (lower : Nodes branch n) (p : Path branch n (Nodes.height lower))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (inside : Slots branch (Nodes.height lower) → Fin t → MixedSupport.Slot)
  (hag : ∀ s, p.slotEmbedding s = (Nodes.path lower).slotEmbedding s)

def nativeDual
    (z : Module.Dual F2 (squareSpace (H (nodeSlots (CutSlotAssembly.fill p outside inside) lower)))) :
    Module.Dual F2 (squareSpace (H inside)) :=
  dualCast (nodeSlots_fill_of_agree lower p outside inside hag) z

def nativeForm
    (F : SourceLocalOddLists.Form (nodeSlots (CutSlotAssembly.fill p outside inside) lower)) :
    SourceLocalOddLists.Form inside :=
  formCast (nodeSlots_fill_of_agree lower p outside inside hag) F

theorem nativeForm_multiplication
    (z : Module.Dual F2 (squareSpace (H (nodeSlots (CutSlotAssembly.fill p outside inside) lower)))) :
    nativeForm lower p outside inside hag
      (OddListExtraction.multiplicationForm
        (H (nodeSlots (CutSlotAssembly.fill p outside inside) lower)) z) =
      OddListExtraction.multiplicationForm (H inside) (nativeDual lower p outside inside hag z) :=
  formCast_multiplication (nodeSlots_fill_of_agree lower p outside inside hag) z

theorem nativeForm_rank
    (F : SourceLocalOddLists.Form (nodeSlots (CutSlotAssembly.fill p outside inside) lower)) :
    OddListExtraction.formRank (H inside) (nativeForm lower p outside inside hag F) =
      OddListExtraction.formRank (H (nodeSlots (CutSlotAssembly.fill p outside inside) lower)) F :=
  formRank_formCast (nodeSlots_fill_of_agree lower p outside inside hag) F

theorem nativeDual_normalized (hbranch : ∀ j < Nodes.height lower, 0 < branch j)
    (z : Module.Dual F2 (squareSpace (H (nodeSlots (CutSlotAssembly.fill p outside inside) lower))))
    (hnorm : z (oneElement
      (nodeSlots (CutSlotAssembly.fill p outside inside) lower) hbranch) = 1) :
    nativeDual lower p outside inside hag z (oneElement inside hbranch) = 1 :=
  dualCast_normalized (nodeSlots_fill_of_agree lower p outside inside hag) hbranch z hnorm

variable (outside' : Slots branch n → Fin t → MixedSupport.Slot)
  (inside' : Slots branch (Nodes.height lower) → Fin t → MixedSupport.Slot)

def nativeProjection
    (projection : ∀ s j, MixedSupport.Projection
      (nodeSlots (CutSlotAssembly.fill p outside inside) lower s j)
      (nodeSlots (CutSlotAssembly.fill p outside' inside') lower s j)) :
    ∀ s j, MixedSupport.Projection (inside s j) (inside' s j) :=
  projectionCast (nodeSlots_fill_of_agree lower p outside inside hag)
    (nodeSlots_fill_of_agree lower p outside' inside' hag) projection

theorem nativeForm_projection_agreement
    (projection : ∀ s j, MixedSupport.Projection
      (nodeSlots (CutSlotAssembly.fill p outside inside) lower s j)
      (nodeSlots (CutSlotAssembly.fill p outside' inside') lower s j))
    (F : SourceLocalOddLists.Form (nodeSlots (CutSlotAssembly.fill p outside inside) lower))
    (G : SourceLocalOddLists.Form (nodeSlots (CutSlotAssembly.fill p outside' inside') lower))
    (hagree : ∀ f g, G f g = F (HPullback projection f) (HPullback projection g)) :
    ∀ f g, nativeForm lower p outside' inside' hag G f g =
      nativeForm lower p outside inside hag F
        (HPullback (nativeProjection lower p outside inside hag outside' inside' projection) f)
        (HPullback (nativeProjection lower p outside inside hag outside' inside' projection) g) :=
  formCast_projection_agreement (nodeSlots_fill_of_agree lower p outside inside hag)
    (nodeSlots_fill_of_agree lower p outside' inside' hag) projection F G hagree

theorem nativeDual_projection_agreement
    (projection : ∀ s j, MixedSupport.Projection
      (nodeSlots (CutSlotAssembly.fill p outside inside) lower s j)
      (nodeSlots (CutSlotAssembly.fill p outside' inside') lower s j))
    (z : Module.Dual F2 (squareSpace (H (nodeSlots (CutSlotAssembly.fill p outside inside) lower))))
    (G : SourceLocalOddLists.Form (nodeSlots (CutSlotAssembly.fill p outside' inside') lower))
    (hagree : ∀ f g, G f g = OddListExtraction.multiplicationForm
      (H (nodeSlots (CutSlotAssembly.fill p outside inside) lower)) z
        (HPullback projection f) (HPullback projection g)) :
    ∀ f g, nativeForm lower p outside' inside' hag G f g =
      OddListExtraction.multiplicationForm (H inside) (nativeDual lower p outside inside hag z)
        (HPullback (nativeProjection lower p outside inside hag outside' inside' projection) f)
        (HPullback (nativeProjection lower p outside inside hag outside' inside' projection) g) :=
  dualCast_projection_agreement (nodeSlots_fill_of_agree lower p outside inside hag)
    (nodeSlots_fill_of_agree lower p outside' inside' hag) projection z G hagree

end Native

end
end PerfectCompleteness.CutNativeForms

end

end OAI
