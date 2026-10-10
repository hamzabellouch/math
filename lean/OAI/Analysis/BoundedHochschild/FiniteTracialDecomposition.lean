import OAI.Analysis.BoundedHochschild.NormalTraceFaithfulness
import OAI.Analysis.BoundedHochschild.CenterAveragingReduction

namespace OAI

/-!
# Unconditional scalar traces on finite central pieces

Trace-free normal states, orbit compactness, and the isometric fixed-point
argument discharge the local tracial-cut input to central decomposition.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A center-faithful normal state on a finite von Neumann algebra gives an
actual faithful normal tracial state. -/
theorem faithful_normal_trace_of_center_state (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hψ1 : ψ 1 = 1)
    (hfaith : ∀ p : M, IsStarProjection p → (∀ a : M, p * a = a * p) → ψ p = 0 → p = 0) :
    ∃ τ : M →ₚ[ℂ] ℂ, TraceInPredual e τ ∧ τ 1 = 1 ∧
      (∀ a b : M, τ (a * b) = τ (b * a)) ∧
      ∀ a : M, τ (star a * a) = 0 → a = 0 := by
  obtain ⟨τ, hτ, hτ1, htr, hc⟩ := exists_normal_tracial_average e hfinite ψ hψ
  refine ⟨τ, hτ, hτ1.trans hψ1, htr, ?_⟩
  apply normal_trace_faithful_of_center e τ hτ htr
  intro p hp hpc hτp
  apply hfaith p hp hpc
  rwa [hc p hpc] at hτp

/-- The local scalar-trace input is now a theorem, with no averaging input. -/
theorem localTracialCutInput (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    LocalTracialCutInput M := by
  intro z hz hzc hzfinite hzII hz0
  obtain ⟨p, hp, hpc, hpz, hp0, hstate⟩ :=
    exists_central_normal_state_subprojection e hz hzc hz0
  have hpfinite : FiniteAlgebra (Corner p hp) :=
    (finiteCorner_iff p hp).mp
      (finiteCorner_mono hp hz hpz ((finiteCorner_iff z hz).mpr hzfinite))
  have hpII : PopaTypeII.NoTypeICentralPart (Corner p hp) :=
    noTypeICentralPart_smaller_centralCorner hp hz hpz hpc hzII
  obtain ⟨ψ, hψ, hψ1, hfaith⟩ := central_faithful_state_on_corner e hp hpc hstate
  let eP := cornerPredualEquiv p hp e
  obtain ⟨τ, hτ, hτ1, htr, hfaithτ⟩ :=
    faithful_normal_trace_of_center_state eP hpfinite ψ hψ hψ1 hfaith
  exact ⟨p, hp, hpc, hpz, hp0, CornerPredual p hp e,
    inferInstance, inferInstance, inferInstance, eP, τ, hτ, htr, hfaithτ, hτ1, hpII⟩

/-- The central decomposition needed by the main theorem is unconditional. -/
theorem centralDecompositionInput (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    CentralDecompositionInput M :=
  centralDecompositionInput_of_local_tracial_cuts e (localTracialCutInput e)

/-- Only the classical non-type-II₁ vanishing input remains here. -/
theorem primitive_of_classical_vanishing (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hclassical : ClassicalVanishingInput.{u})
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x :=
  primitive_of_published_inputs e (centralDecompositionInput e) hclassical f hf

end KadisonRingrose
end BoundedHochschild

end

end OAI
