import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.ConormalPairing

variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem prescribed_values_of_independent {v : I → E}
    (hv : LinearIndependent K v) (a : I → K) :
    ∃ f : E →ₗ[K] K, ∀ i, f (v i) = a i := by
  obtain ⟨f, hf⟩ := LinearMap.dualMap_surjective_of_injective
    hv.finsuppLinearCombination_injective (Finsupp.linearCombination K a)
  refine ⟨f, fun i => ?_⟩
  have h := LinearMap.congr_fun hf (Finsupp.single i (1 : K))
  simpa only [LinearMap.dualMap_apply, Finsupp.linearCombination_single, one_smul] using h

theorem prescribed_conormal_values (T : Submodule K E) {v : I → E}
    (hv : LinearIndependent K (fun i => T.mkQ (v i))) (a : I → K) :
    ∃ f : E →ₗ[K] K, (∀ t ∈ T, f t = 0) ∧ ∀ i, f (v i) = a i := by
  obtain ⟨g, hg⟩ := prescribed_values_of_independent hv a
  refine ⟨g.comp T.mkQ, ?_, hg⟩
  intro t ht
  change g (T.mkQ t) = 0
  have hqt : T.mkQ t = 0 := (Submodule.Quotient.mk_eq_zero T).mpr ht
  rw [hqt, map_zero]

theorem normal_dual_evaluation_surjective (T : Submodule K E)
    {v : I → E} (hv : LinearIndependent K (fun i => T.mkQ (v i))) :
    Function.Surjective (fun f : (E ⧸ T) →ₗ[K] K => fun i => f (T.mkQ (v i))) := by
  intro a
  obtain ⟨f, hf⟩ := prescribed_values_of_independent hv a
  exact ⟨f, funext hf⟩

theorem independent_forms_evaluation_surjective [FiniteDimensional K E]
    {f : I → E →ₗ[K] K} (hf : LinearIndependent K f) :
    Function.Surjective (fun x : E => fun i => f i x) := by
  intro a
  obtain ⟨g, hg⟩ := prescribed_values_of_independent hf a
  refine ⟨(Module.evalEquiv K E).symm g, ?_⟩
  funext i
  change f i ((Module.evalEquiv K E).symm g) = a i
  rw [Module.apply_evalEquiv_symm_apply]
  exact hg i

end WeightedTorusJets.ConormalPairing

end

end SiegelZeros

end OAI
