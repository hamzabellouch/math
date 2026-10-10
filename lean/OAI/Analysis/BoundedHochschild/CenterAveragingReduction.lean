import OAI.Analysis.BoundedHochschild.TracialCoverReduction
import OAI.Analysis.BoundedHochschild.FiniteNormalState
import OAI.Analysis.BoundedHochschild.CentralTypeIIInheritance

namespace OAI

/-!
# The precise remaining center-valued trace input

The construction of faithful normal scalar traces is reduced to the
center-valued trace theorem for finite von Neumann algebras (Blackadar,
III.2.5.7--8). Normal states and their central supports are constructed
without this input. Only the positive normal central averaging map remains
an explicit hypothesis; the global central partition is derived.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

universe u

/-- The part of a center-valued trace used by the scalar trace construction. -/
structure NormalCentralAverage {N Y : Type u} [CStarAlgebra N]
    [PartialOrder N] [StarOrderedRing N] [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [CompleteSpace Y] (e : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N) where
  map : N →L[ℂ] N
  normal : HasPreadjoint e map
  positive : ∀ a : N, 0 ≤ a → 0 ≤ map a
  unital : map 1 = 1
  central : ∀ a b : N, map a * b = b * map a
  tracial : ∀ a b : N, map (a * b) = map (b * a)
  faithful : ∀ a : N, map (star a * a) = 0 → a = 0

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Center-valued trace existence, restricted to the finite type-II central
corners needed for this application. -/
def FiniteCentralAveragingInput (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : Prop :=
  ∀ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) →
    FiniteAlgebra (Corner p hp) → PopaTypeII.NoTypeICentralPart (Corner p hp) →
    Nonempty (NormalCentralAverage (cornerPredualEquiv p hp e))

/-- A center-valued trace yields the exact local scalar-trace consequence
needed by the already proved global decomposition. -/
theorem localTracialCutInput_of_center_averaging (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (haverage : FiniteCentralAveragingInput e) : LocalTracialCutInput M := by
  intro z hz hzc hzfinite hzII hz0
  obtain ⟨p, hp, hpc, hpz, hp0, hstate⟩ :=
    exists_central_normal_state_subprojection e hz hzc hz0
  have hpfinite : FiniteAlgebra (Corner p hp) :=
    (finiteCorner_iff p hp).mp
      (finiteCorner_mono hp hz hpz ((finiteCorner_iff z hz).mpr hzfinite))
  have hpII : PopaTypeII.NoTypeICentralPart (Corner p hp) :=
    noTypeICentralPart_smaller_centralCorner hp hz hpz hpc hzII
  obtain ⟨E⟩ := haverage p hp hpc hpfinite hpII
  obtain ⟨ψ, hψ, hψ1, hfaith⟩ := central_faithful_state_on_corner e hp hpc hstate
  let eP := cornerPredualEquiv p hp e
  obtain ⟨τ, hτ, hτ1, htr, hfaithτ⟩ := tracial_state_of_normal_center_average eP
    ψ hψ hψ1 hfaith E.map E.normal E.positive E.unital E.central E.tracial E.faithful
  exact ⟨p, hp, hpc, hpz, hp0, CornerPredual p hp e,
    inferInstance, inferInstance, inferInstance, eP, τ, hτ, htr, hfaithτ, hτ1, hpII⟩

/-- All central partition and scalar-trace work is discharged; only the
center-valued averaging existence input remains in the structural reduction. -/
theorem centralDecompositionInput_of_center_averaging (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (haverage : FiniteCentralAveragingInput e) : CentralDecompositionInput M :=
  centralDecompositionInput_of_local_tracial_cuts e
    (localTracialCutInput_of_center_averaging e haverage)

theorem primitive_of_center_averaging (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (haverage : FiniteCentralAveragingInput e) (hclassical : ClassicalVanishingInput.{u})
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x :=
  primitive_of_published_inputs e (centralDecompositionInput_of_center_averaging e haverage)
    hclassical f hf

end KadisonRingrose
end BoundedHochschild

end

end OAI
