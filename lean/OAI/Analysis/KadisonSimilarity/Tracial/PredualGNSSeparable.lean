import OAI.Analysis.KadisonSimilarity.Tracial.PredualGNSNormality
import OAI.Analysis.KadisonSimilarity.Representation.SeparableConcretePredual
import OAI.Analysis.FactorGeneration.FunctionalLimits

namespace OAI

/-! A normal positive functional on an algebra with separable predual has
a separable GNS space. Countably many dual evaluations give a total family
of GNS vectors. -/

noncomputable section
namespace KadisonSimilarity

open HochschildNormalPart
open scoped ComplexOrder

universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [TopologicalSpace.SeparableSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A) (τ : A →ₚ[ℂ] ℂ)

theorem exists_countable_total_gns_vectors (hτ : BoundedHochschild.TraceInPredual e τ) :
    ∃ a : ℕ → A, (∀ n, ‖a n‖ ≤ 1) ∧
      ∀ ξ : τ.GNS, (∀ n, inner ℂ ξ (gnsTracialVector τ (a n)) = 0) → ξ = 0 := by
  obtain ⟨g, hg, htotal⟩ := Generator.exists_countable_total_dual X
  refine ⟨fun n => e (g n), fun n => (e.norm_map (g n)).le.trans (hg n), ?_⟩
  intro ξ hξ
  obtain ⟨z, hz⟩ := (mem_normalDual e _).mp (gnsCyclic_coefficient_normal e τ hτ ξ)
  have hz0 : z = 0 := htotal z (fun n => by
    have h := hz (e (g n))
    simpa only [coefficient_apply, gnsTracialVector_left, mul_one,
      e.symm_apply_apply, hξ n, star_eq_zero] using h.symm)
  apply (gnsTracialVector_dense τ).eq_zero_of_inner_left ℂ
  intro a
  have h := hz a
  simpa only [coefficient_apply, gnsTracialVector_left, mul_one, hz0,
    map_zero, star_zero] using h

theorem gns_separable_of_predual (hτ : BoundedHochschild.TraceInPredual e τ) :
    TopologicalSpace.SeparableSpace τ.GNS := by
  obtain ⟨a, _, ha⟩ := exists_countable_total_gns_vectors e τ hτ
  let v : ℕ → τ.GNS := fun n => gnsTracialVector τ (a n)
  let V := (Submodule.span ℂ (Set.range v)).topologicalClosure
  have htop : V = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro ξ hξ
    change ξ = 0
    apply ha ξ
    intro n
    exact (Submodule.mem_orthogonal' V ξ).mp hξ (v n)
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩))
  have hs : TopologicalSpace.IsSeparable (V : Set τ.GNS) :=
    (Set.countable_range v).isSeparable.span.closure
  rw [htop, Submodule.top_coe] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

end KadisonSimilarity

end

end OAI
