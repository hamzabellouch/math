import Mathlib
import OAI.GroupTheory.SimpleOvergroups.RingAssemblyTools
import OAI.GroupTheory.SimpleOvergroups.SourceModel

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups.SourceModel
open scoped Classical TensorProduct FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open ContextualEncoding SemanticEncoding EffectiveNames RingAssembly

variable {G : Type} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))
local instance : LinearOrder (Control.Sector Sigma (Bool × family.Γ) (ParameterMachine.State family.Q (index s h))) :=
  ParameterCode.finiteOrder (index s h)

 theorem realizes_processor : Word.Realizes KAlphabet (KMachine s h) (tableNormal (processor s h)) :=
  index_fixed s h ▸ family.realizes (index s h)

def rawCopy : L s h →ₙ* K s h :=
  Quotient.rawMap (processor s h) wf (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h)
 theorem rawCopy_injective : Function.Injective (rawCopy s h) :=
  Quotient.rawMap_injective (processor s h) wf (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h)
 theorem rawCopy_ne_one (x : L s h) : rawCopy s h x ≠ 1 :=
  Quotient.rawMap_ne_one (processor s h) wf (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h) x
 theorem rawCopy_ne_zero (x : L s h) : rawCopy s h x ≠ 0 :=
  Quotient.rawMap_ne_zero (processor s h) wf (index_good s h) (index_stable s h)
    KAlphabet (KMachine s h) family.decode (realizes_processor s h) x

def i : Astar s h →ₙₐ[ZMod 2] B s h := Contracted.embedding (rawCopy s h)
 theorem i_injective : Function.Injective (i s h) :=
  Contracted.embedding_injective (rawCopy s h) (rawCopy_injective s h) (rawCopy_ne_zero s h)
 theorem one_not_mem_i : (1 : B s h) ∉ Set.range (i s h) :=
  Contracted.one_not_mem_range (rawCopy s h) (rawCopy_ne_one s h)

def κ : B s h ⊗[ZMod 2] MonoidAlgebra (ZMod 2) PartialAffine.monoid →ₐ[ZMod 2] Astar s h :=
  (Contracted.map (codeProduct₀ s h)).comp (ZeroProduct.tensorMap (ZMod 2) (K s h) PartialAffine.monoid)
 theorem κ_injective : Function.Injective (κ s h) :=
  (Contracted.map_injective (codeProduct₀ s h) (codeProduct_injective s h)).comp
    (ZeroProduct.tensorMap_bijective (ZMod 2) (K s h) PartialAffine.monoid).1

def ξ : B s h ⊗[ZMod 2] MonoidAlgebra (ZMod 2) PartialAffine.monoid →ₙₐ[ZMod 2] B s h :=
  (i s h).comp (κ s h).toNonUnitalAlgHom
 theorem ξ_injective : Function.Injective (ξ s h) := (i_injective s h).comp (κ_injective s h)

def φ : B s h →ₙ+* B s h := binaryPhi (ξ s h)
 theorem φ_injective : Function.Injective (φ s h) := binaryPhi_injective (ξ s h) (ξ_injective s h)
def binary : CompressedSplittings.BinaryData (φ s h) := binaryData (ξ s h)

def e : B s h := i s h 1
 theorem e_idempotent : IsIdempotentElem (e s h) := supportIdempotent (i s h : Astar s h →ₙ+* B s h)
 theorem e_nonzero : e s h ≠ 0 := by
  intro he
  exact one_ne_zero (i_injective s h (he.trans (map_zero (i s h)).symm))
 theorem e_ne_one : e s h ≠ 1 := fun he => one_not_mem_i s h ⟨1,he⟩

def cornerMap : Astar s h →+* (e_idempotent s h).Corner := toCorner (i s h : Astar s h →ₙ+* B s h)
 theorem cornerMap_injective : Function.Injective (cornerMap s h) := toCorner_injective _ (i_injective s h)

abbrev Generators := CommonCompiler.FiniteLetter Sigma family.Γ family.Q (index s h)
def Relations : FreeAlgebra (ZMod 2) (Generators s h) → FreeAlgebra (ZMod 2) (Generators s h) → Prop :=
  ContractedPresentation.Rel (ZMod 2) (Generators s h) (Word.Rel KAlphabet (KMachine s h)) [.zero]

def presentation : RingQuot (Relations s h) ≃ₐ[ZMod 2] B s h :=
  ContractedPresentation.equivalence (ZMod 2) (Generators s h) (Word.Rel KAlphabet (KMachine s h))
    (MulEquiv.refl (K s h)) [.zero] rfl
 theorem relations_finite : {p : FreeAlgebra (ZMod 2) (Generators s h) × FreeAlgebra (ZMod 2) (Generators s h) |
      Relations s h p.1 p.2}.Finite :=
  ContractedPresentation.finite_relations (ZMod 2) (Generators s h) (Word.Rel KAlphabet (KMachine s h))
    [.zero] (Word.rules_finite KAlphabet (KMachine s h))

def presentationMap : FreeAlgebra (ZMod 2) (Generators s h) →ₐ[ZMod 2] B s h :=
  (presentation s h).toAlgHom.comp (RingQuot.mkAlgHom (ZMod 2) (Relations s h))
 theorem presentationMap_surjective : Function.Surjective (presentationMap s h) :=
  (presentation s h).surjective.comp (RingQuot.mkAlgHom_surjective (ZMod 2) (Relations s h))
 theorem presentationMap_kernel : TwoSidedIdeal.ker (presentationMap s h).toRingHom =
      TwoSidedIdeal.span (differences (Relations s h)) := by
  rw [←ker_ringQuot]
  ext a
  simp only [TwoSidedIdeal.mem_ker]
  change presentation s h (RingQuot.mkAlgHom (ZMod 2) (Relations s h) a)=0 ↔
    RingQuot.mkRingHom (Relations s h) a=0
  rw [←RingQuot.mkAlgHom_coe (ZMod 2) (Relations s h)]
  exact (presentation s h).map_eq_zero_iff

end SimpleFInftyOvergroups.SourceModel
end

end OAI
