import OAI.Analysis.BoundedHochschild.FiniteModuleAverages

namespace OAI

/-! Compactness and restriction of joint averaging orbits. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I J : Type*}

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakFamilyAverageOrbit_component (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) (i : I) {F : I → M → WeakDual ℂ X}
    (hF : F ∈ weakFamilyAverageOrbit e T) : F i ∈ weakRightAverageOrbit e (T i) := by
  have hc : IsClosed {G : I → M → WeakDual ℂ X | G i ∈ weakRightAverageOrbit e (T i)} :=
    isClosed_closure.preimage (continuous_apply i)
  apply closure_minimal _ hc hF
  rintro G ⟨k, m, hm, rfl⟩
  exact subset_closure ⟨_, finiteRightAverage_mem_orbit m hm _, rfl⟩

omit [PartialOrder M] [StarOrderedRing M] [CompleteSpace X] in
lemma weakFamilyAverageOrbit_nonempty (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) : (weakFamilyAverageOrbit e T).Nonempty := by
  refine ⟨_, subset_closure ⟨1, (fun _ : Fin 1 => (1 : M)), by simp, rfl⟩⟩

theorem weakFamilyAverageOrbit_isCompact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : I → M →L[ℂ] M) (C : I → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    IsCompact (weakFamilyAverageOrbit e T) :=
  (isCompact_pi_infinite (fun i => weakRightAverageOrbit_isCompact e hno (T i) (hT i))).of_isClosed_subset
    isClosed_closure (fun _ hF i => weakFamilyAverageOrbit_component e T i hF)

theorem weakFamilyAverageOrbit_restriction_lift (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (T : I → M →L[ℂ] M) (C : I → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) (f : J → I)
    {F : J → M → WeakDual ℂ X} (hF : F ∈ weakFamilyAverageOrbit e (T ∘ f)) :
    ∃ G ∈ weakFamilyAverageOrbit e T, G ∘ f = F := by
  let r (G : I → M → WeakDual ℂ X) : J → M → WeakDual ℂ X := G ∘ f
  have hc : Continuous r := continuous_pi (fun j => continuous_apply (f j))
  have hclosed : IsClosed (r '' weakFamilyAverageOrbit e T) :=
    ((weakFamilyAverageOrbit_isCompact e hno T C hT).image hc).isClosed
  have hsub : finiteFamilyAverageOrbit e (T ∘ f) ⊆ r '' weakFamilyAverageOrbit e T := by
    rintro G ⟨k, m, hm, rfl⟩
    refine ⟨fun i => weakOperatorImage e (finiteRightAverage m (T i)),
      subset_closure ⟨k, m, hm, rfl⟩, rfl⟩
  exact closure_minimal hsub hclosed hF

end BoundedHochschild.KadisonRingrose

end

end OAI
