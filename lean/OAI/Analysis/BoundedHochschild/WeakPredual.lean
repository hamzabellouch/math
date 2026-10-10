import OAI.Analysis.BoundedHochschild.PositiveOrbitCompactness
import Mathlib.Analysis.LocallyConvex.WeakSpace

namespace OAI

/-! The normal dual, with its weak-star topology, is the weak predual. -/

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The normal-functional embedding with both weak topologies. -/
def weakPredualMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (x : WeakSpace ℂ X) : WeakDual ℂ M :=
  StrongDual.toWeakDual (predualEmbedding e ((toWeakSpace ℂ X).symm x))

@[simp] lemma weakPredualMap_apply (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (x : WeakSpace ℂ X) (a : M) :
    weakPredualMap e x a = star (e.symm a ((toWeakSpace ℂ X).symm x)) := rfl

lemma weakPredualMap_continuous (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Continuous (weakPredualMap e) := by
  apply WeakDual.continuous_of_continuous_eval
  intro a
  exact (WeakBilin.eval_continuous (topDualPairing ℂ X).flip (e.symm a)).star

/-- Evaluating against every algebra element recovers the weak topology on
its predual; hence the normal embedding is a topological embedding. -/
theorem weakPredualMap_isEmbedding (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Topology.IsEmbedding (weakPredualMap e) := by
  let g (F : WeakDual ℂ M) (f : StrongDual ℂ X) : ℂ := star (F (e f))
  have hg : Continuous g := continuous_pi (fun f => (WeakDual.eval_continuous (e f)).star)
  have heq : g ∘ weakPredualMap e = fun x : WeakSpace ℂ X =>
      fun f : StrongDual ℂ X => f ((toWeakSpace ℂ X).symm x) := by
    funext x f
    simp only [Function.comp_apply, g, weakPredualMap_apply, e.symm_apply_apply, star_star]
  apply Topology.IsEmbedding.of_comp (weakPredualMap_continuous e) hg
  rw [heq]
  exact WeakBilin.isEmbedding (B := (topDualPairing ℂ X).flip) (fun x y h => by
    apply (toWeakSpace ℂ X).symm.injective
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro f
    exact congrArg (fun L : StrongDual ℂ X →ₗ[ℂ] ℂ => L f) h)

lemma range_weakPredualMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    Set.range (weakPredualMap e) =
      {F : WeakDual ℂ M | WeakDual.toStrongDual F ∈ normalDual e} := by
  ext F
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(toWeakSpace ℂ X).symm x, rfl⟩
  · intro hF
    obtain ⟨x, hx⟩ := hF
    refine ⟨toWeakSpace ℂ X x, ?_⟩
    exact congrArg StrongDual.toWeakDual hx

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

/-- The positive unitary orbit has a compact realization in the weak predual. -/
theorem normal_positive_predual_orbit_compact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    IsCompact ((weakPredualMap e) ⁻¹'
      weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))) := by
  obtain ⟨hc, hn⟩ := normal_positive_orbit_compact e hfinite ψ hψ
  apply (weakPredualMap_isEmbedding e).isInducing.isCompact_preimage' hc
  intro F hF
  rw [range_weakPredualMap]
  exact hn F hF

end KadisonRingrose
end BoundedHochschild

end

end OAI
