import OAI.Analysis.KadisonSimilarity.Representation.ConcretePredualDuality
import OAI.Analysis.KadisonSimilarity.Tracial.PredualGNSNormality

namespace OAI

/-! Normality of a trace restricts to a concrete von Neumann subalgebra.
Restriction sends each vector functional to the same vector functional,
and therefore preserves their closed span. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder
open BoundedHochschild

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N M : VonNeumannAlgebra H} (hNM : N ≤ M)

def concreteInclusionCLM : N.toStarSubalgebra →L[ℂ] M.toStarSubalgebra :=
  { (StarSubalgebra.inclusion hNM).toLinearMap with
    cont := by
      change Continuous (fun a : N.toStarSubalgebra =>
        (⟨(a : H →L[ℂ] H), hNM a.property⟩ : M.toStarSubalgebra))
      exact continuous_subtype_val.subtype_mk _ }

def normalRestriction : StrongDual ℂ M.toStarSubalgebra →L[ℂ]
    StrongDual ℂ N.toStarSubalgebra :=
  (ContinuousLinearMap.compL ℂ N.toStarSubalgebra M.toStarSubalgebra ℂ).flip
    (concreteInclusionCLM hNM)

@[simp] theorem normalRestriction_apply (φ : StrongDual ℂ M.toStarSubalgebra)
    (a : N.toStarSubalgebra) :
    normalRestriction hNM φ a = φ (StarSubalgebra.inclusion hNM a) := rfl

@[simp] theorem normalRestriction_coefficient (x y : H) :
    normalRestriction hNM (normalCoefficient M x y) = normalCoefficient N x y := rfl

theorem normalRestriction_mem (φ : StrongDual ℂ M.toStarSubalgebra)
    (hφ : φ ∈ normalFunctionalSpace M) :
    normalRestriction hNM φ ∈ normalFunctionalSpace N := by
  have hspan : Submodule.span ℂ (Set.range fun xy : H × H => normalCoefficient M xy.1 xy.2) ≤
      (normalFunctionalSpace N).toSubmodule.comap (normalRestriction hNM).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change normalRestriction hNM (normalCoefficient M x y) ∈ normalFunctionalSpace N
    rw [normalRestriction_coefficient]
    exact (predualCoefficient N x y).property
  exact closure_minimal hspan
    ((normalFunctionalSpace N).isClosed.preimage (normalRestriction hNM).continuous) hφ

def predualRestriction : ConcretePredual M →L[ℂ] ConcretePredual N :=
  (((normalRestriction hNM).comp (normalFunctionalSpace M).toSubmodule.subtypeL).codRestrict
    (normalFunctionalSpace N).toSubmodule (fun φ => normalRestriction_mem hNM φ φ.property))

@[simp] theorem predualRestriction_apply (φ : ConcretePredual M) (a : N.toStarSubalgebra) :
    (predualRestriction hNM φ : StrongDual ℂ N.toStarSubalgebra) a =
      (φ : StrongDual ℂ M.toStarSubalgebra) (StarSubalgebra.inclusion hNM a) := rfl

def includedPositiveTrace (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    N.toStarSubalgebra →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (τ.toLinearMap.comp (StarSubalgebra.inclusion hNM).toLinearMap)
    (fun _a ha => τ.map_nonneg ha)

@[simp] theorem includedPositiveTrace_apply (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (a : N.toStarSubalgebra) :
    includedPositiveTrace hNM τ a = τ (StarSubalgebra.inclusion hNM a) := rfl

theorem includedPositiveTrace_normal (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hτ : TraceInPredual (concretePredualEquiv M) τ) :
    TraceInPredual (concretePredualEquiv N) (includedPositiveTrace hNM τ) := by
  obtain ⟨φ, hφ⟩ := hτ
  refine ⟨predualRestriction hNM φ, fun a => ?_⟩
  rw [concretePredualEquiv_symm_apply, predualRestriction_apply, includedPositiveTrace_apply]
  exact hφ (StarSubalgebra.inclusion hNM a)

theorem includedPositiveTrace_hasNormalGNS (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hτ : TraceInPredual (concretePredualEquiv M) τ)
    (htr : ∀ a b, τ (a * b) = τ (b * a)) :
    HasNormalGNS (includedPositiveTrace hNM τ) := by
  apply hasNormalGNS_of_predual (concretePredualEquiv N) _
    (includedPositiveTrace_normal hNM τ hτ)
  intro a b
  simpa only [includedPositiveTrace_apply, map_mul] using
    htr (StarSubalgebra.inclusion hNM a) (StarSubalgebra.inclusion hNM b)

end KadisonSimilarity

end

end OAI
