import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentExtensionFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionMap

namespace OAI

/-! # Extending a nilpotent lattice to the full nonsplit extension

Only the nilpotent kernel is completed here. The original quotient, section,
and all of its defects are retained exactly.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)

/-- The original and completed factor systems agree on the kernel lattice. -/
def extensionFactorMap :
    FactorExtension (GroupExtensionSection.factorSystem S σ hσ) →*
      FactorExtension (C.extensionFactorSystem S σ hσ) :=
  FactorExtension.map _ _ (C.lattice.subtype.comp C.equiv.toMonoidHom)
    (fun q n => (C.automorphism_on_lattice (S.conjAct (σ q)) n).symm)
    (fun _ _ => rfl)

theorem extensionFactorMap_injective : Function.Injective (C.extensionFactorMap S σ hσ) :=
  FactorExtension.map_injective _ _ _ _ _ (Subtype.val_injective.comp C.equiv.injective)

/-- A faithful map of the original nonsplit extension into the group with
completed nilpotent kernel and unchanged quotient. -/
def extensionEmbedding : G →* FactorExtension (C.extensionFactorSystem S σ hσ) :=
  (C.extensionFactorMap S σ hσ).comp (GroupExtensionSection.mulEquiv S σ hσ).toMonoidHom

theorem extensionEmbedding_injective : Function.Injective (C.extensionEmbedding S σ hσ) :=
  (C.extensionFactorMap_injective S σ hσ).comp (GroupExtensionSection.mulEquiv S σ hσ).injective

/-- This range description retains the full quotient and only restricts the
nilpotent coordinate to its constructed lattice. -/
theorem mem_extensionEmbedding_range (a : FactorExtension (C.extensionFactorSystem S σ hσ)) :
    a ∈ (C.extensionEmbedding S σ hσ).range ↔ a.left ∈ C.lattice := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (C.equiv _).property
  · intro ha
    obtain ⟨n, hn⟩ := C.equiv.surjective ⟨a.left, ha⟩
    let b : FactorExtension (GroupExtensionSection.factorSystem S σ hσ) := ⟨n, a.right⟩
    refine ⟨(GroupExtensionSection.mulEquiv S σ hσ).symm b, ?_⟩
    change C.extensionFactorMap S σ hσ
      ((GroupExtensionSection.mulEquiv S σ hσ) ((GroupExtensionSection.mulEquiv S σ hσ).symm b)) = a
    rw [MulEquiv.apply_symm_apply]
    apply FactorExtension.ext
    · exact congrArg Subtype.val hn
    · rfl

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
