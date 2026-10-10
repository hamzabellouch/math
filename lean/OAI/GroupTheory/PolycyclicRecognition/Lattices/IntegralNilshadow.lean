import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralSemisimpleTwist
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnipotentFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Lattices.KernelCompletionAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemTwistAction

namespace OAI

/-! # Constructing the nilshadow of an integral abelian extension

Both the section and the removed action are constructed from the original
extension. The twisted group has a nilpotent real completion of the correct
dimension. Its removed action extends, and the original group embeds faithfully
in the corresponding semidirect product. The quotient here is still integral.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L] [Group G] {n : ℕ}

structure IntegralNilshadowData (E : GroupExtension L G (IntegralLatticeGroup n)) where
  sectionMap : E.Section
  normalized : sectionMap 1 = 1
  removed : IntegralLatticeGroup n →* MulAut L
  commutes : ∀ q r, Commute
    ((GroupExtensionSection.factorSystem E sectionMap normalized).action q) (removed r)
  fixes : ∀ q r s, removed q
    ((GroupExtensionSection.factorSystem E sectionMap normalized).factor r s) =
      (GroupExtensionSection.factorSystem E sectionMap normalized).factor r s
  smooth : ∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (removed q)
  twist_smooth : ∀ q, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞
    (((GroupExtensionSection.factorSystem E sectionMap normalized).twist removed commutes fixes).action q)
  twist_nilpotent : Group.IsNilpotent (FactorExtension
    ((GroupExtensionSection.factorSystem E sectionMap normalized).twist removed commutes fixes))
  completion : NilpotentKernelCompletion (FactorExtension.inl
    ((GroupExtensionSection.factorSystem E sectionMap normalized).twist removed commutes fixes))
  dimension : completion.dimension = Module.finrank ℝ L + n

theorem exists_integralNilshadowData (E : GroupExtension L G (IntegralLatticeGroup n))
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)) :
    Nonempty (IntegralNilshadowData E) := by
  obtain ⟨σ, hσ, χ, hc, hf, hχ, hT, hu⟩ := integral_semisimple_twist E hsmooth
  let R := GroupExtensionSection.factorSystem E σ hσ
  let T := R.twist χ hc hf
  let qs := List.ofFn (integralLatticeGenerator n)
  have hgen : Subgroup.closure {q | q ∈ qs} = ⊤ := by
    convert integralLatticeGenerator_closure n using 2
    ext q
    exact List.mem_ofFn
  have hnil : Group.IsNilpotent (FactorExtension T) :=
    factorSystem_nilpotent_of_unipotent T hT qs hgen (by
      intro q hq
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact hu i)
  let := hnil
  obtain ⟨C, hC⟩ := nilpotent_integral_kernel_completion_with_dimension
    (FactorExtension.groupExtension T) (factorSystem_conjugation_smooth T hT)
  exact ⟨⟨σ, hσ, χ, hc, hf, hχ, hT, hnil, C, hC⟩⟩

namespace IntegralNilshadowData
variable {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)
omit [LieRing.IsNilpotent L]

abbrev system := GroupExtensionSection.factorSystem E D.sectionMap D.normalized
abbrev twistedSystem := D.system.twist D.removed D.commutes D.fixes
abbrev integralAction := factorTwistAction D.system D.removed D.commutes D.fixes

theorem integralAction_kernel_smooth (q : IntegralLatticeGroup n) :
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, D.completion.carrier)) ∞
      ((D.completion.embed.comp (D.integralAction q).toMonoidHom).comp
        (FactorExtension.inl D.twistedSystem)) := by
  exact D.completion.kernel_smooth.comp (D.smooth q)

def completedAction : IntegralLatticeGroup n →* MulAut D.completion.carrier :=
  D.completion.extendedAction D.integralAction D.integralAction_kernel_smooth

theorem completedAction_smooth (q : IntegralLatticeGroup n) :
    ContMDiff (𝓘(ℝ, D.completion.carrier)) (𝓘(ℝ, D.completion.carrier)) ∞ (D.completedAction q) :=
  D.completion.extendedAction_smooth D.integralAction D.integralAction_kernel_smooth q

def completionSemidirectMap :
    (FactorExtension D.twistedSystem ⋊[D.integralAction] IntegralLatticeGroup n) →*
      (D.completion.carrier ⋊[D.completedAction] IntegralLatticeGroup n) :=
  SemidirectProduct.map D.completion.embed (MonoidHom.id _) (by
    intro q
    apply MonoidHom.ext
    intro x
    exact (D.completion.extendedAction_embed D.integralAction
      D.integralAction_kernel_smooth q x).symm)

def originalEmbedding : G →*
    (D.completion.carrier ⋊[D.completedAction] IntegralLatticeGroup n) :=
  D.completionSemidirectMap.comp
    ((factorTwistGraph D.system D.removed D.commutes D.fixes).comp
      (GroupExtensionSection.mulEquiv E D.sectionMap D.normalized).toMonoidHom)

theorem originalEmbedding_injective : Function.Injective D.originalEmbedding := by
  have hC : Function.Injective D.completionSemidirectMap := by
    intro a b h
    apply SemidirectProduct.ext
    · apply D.completion.injective
      exact congrArg (fun z => z.left) h
    · exact congrArg (fun z => z.right) h
  exact hC.comp ((factorTwistGraph_injective D.system D.removed D.commutes D.fixes).comp
    (GroupExtensionSection.mulEquiv E D.sectionMap D.normalized).injective)

end IntegralNilshadowData
end PolycyclicRecognition

end

end OAI
