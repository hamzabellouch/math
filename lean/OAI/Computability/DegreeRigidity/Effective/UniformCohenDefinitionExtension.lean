import OAI.Computability.DegreeRigidity.Representation.HomogeneousDegreeExtension
import OAI.Computability.DegreeRigidity.Effective.UniformCohenDefinitionSymmetry

namespace OAI

namespace TuringRigidity.RelativeConstructible
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing BoundedForcing
open CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem uniform_cohen_definition_extension (M A I ρ : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hA : A ∈ M) (hI : I ∈ M) (hρ : ρ ∈ M)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{0}) (hX : X ∈ M)
    (φ : ElementaryModel.SentenceForm)
    (G₀ : GenericFilter (Conditions (conditions A))) (hG₀ : GroundGeneric M G₀)
    (h₀ : OwnDegreeExtension (genericExtensionSet M (conditions A) G₀.carrier) I ρ
      (definedSubset (level (groundReals (genericExtensionSet M (conditions A) G₀.carrier)) δ)
        φ (fun _ : Fin φ.bound => X))) :
    ∃ f : Name (Conditions (conditions A)), f.encode (label (conditions A)) ∈ M ∧
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M (conditions A) G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X) ∧
        OwnDegreeExtension (genericExtensionSet M (conditions A) G.carrier) I ρ (f.val G.carrier) := by
  have hc := conditions_mem M A hM hT hA
  obtain ⟨f,hf,hfv,hinv⟩ := uniform_ordinal_definition_symmetric M (conditions A)
    hM hT hc δ hδ X hX φ
  have hf₀ : OwnDegreeExtension (genericExtensionSet M (conditions A) G₀.carrier) I ρ
      (f.val G₀.carrier) := by rw [hfv G₀ hG₀]; exact h₀
  have hall := degree_extension_all_generics M (conditions A) I ρ hM hT hct hc hI hρ
    (InternalCohenBitFlip.internally_homogeneous M A hM hT hA) f hf hinv G₀ hG₀ hf₀
  exact ⟨f,hf,fun G hG => ⟨hfv G hG,hall G hG⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
