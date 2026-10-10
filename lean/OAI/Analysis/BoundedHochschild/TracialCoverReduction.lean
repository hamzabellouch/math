import OAI.Analysis.BoundedHochschild.CentralProjectionPartitions
import OAI.Analysis.BoundedHochschild.CornerEquivalences
import OAI.Analysis.BoundedHochschild.FiniteCentralDecomposition

namespace OAI

/-!
# Reduction of the structural input to local tracial corners

The global central decomposition follows from a local consequence of the
finite von Neumann algebra trace theorem: every nonzero finite central
type-II corner contains a nonzero faithfully normally tracial central corner.
The maximal-family argument, the exceptional summand, and all corner
identifications are proved here. Only the local trace existence statement
remains an input (Blackadar, III.2.5.7--8).
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

universe u

/-- The remaining local consequence of the finite-algebra trace theorem. -/
def LocalTracialCutInput (M : Type u) [CStarAlgebra M]
    [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ (z : M) (hz : IsStarProjection z), (∀ a : M, z * a = a * z) →
    FiniteAlgebra (Corner z hz) → PopaTypeII.NoTypeICentralPart (Corner z hz) → z ≠ 0 →
    ∃ (p : M) (hp : IsStarProjection p), (∀ a : M, p * a = a * p) ∧
      p ≤ z ∧ p ≠ 0 ∧ TracialTypeII (Corner p hp)

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The global structural input is reduced to local tracial existence, with
the maximal central partition constructed from the given predual. -/
theorem centralDecompositionInput_of_local_tracial_cuts
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hlocal : LocalTracialCutInput M) :
    CentralDecompositionInput M := by
  classical
  let P : M → Prop := fun p => ∃ hp : IsStarProjection p, TracialTypeII (Corner p hp)
  obtain ⟨D⟩ := exists_maximal_central_partition e P
  have hexceptional : NoTypeII1Summand (Corner D.complement D.complement_isProjection) := by
    intro z hz hzc hfinite hII
    by_contra hz0
    let hzM : IsStarProjection (z : M) :=
      corner_projection_coe D.complement D.complement_isProjection hz
    have hzcM : ∀ a : M, (z : M) * a = a * (z : M) :=
      centralCorner_central D.complement_isProjection D.complement_central z hzc
    have hfiniteM : FiniteAlgebra (Corner (z : M) hzM) := by
      apply (finiteCorner_iff (z : M) hzM).mp
      exact finiteCorner_trans D.complement_isProjection z ((finiteCorner_iff z hz).mpr hfinite)
    have hIIM : PopaTypeII.NoTypeICentralPart (Corner (z : M) hzM) :=
      noTypeICentralPart_map_equiv (nestedCornerEquiv D.complement_isProjection z hz) hII
    have hzM0 : (z : M) ≠ 0 := fun h => hz0 (Subtype.ext h)
    obtain ⟨p, hp, hpc, hpz, hp0, hptr⟩ := hlocal (z : M) hzM hzcM hfiniteM hIIM hzM0
    have hzle : (z : M) ≤ D.complement :=
      (hzM.le_iff_mul_eq_right D.complement_isProjection).mpr z.property.1
    exact hp0 (D.maximal p hp hpc (hpz.trans hzle) ⟨hp, hptr⟩)
  let p : Option D.Index → M := fun i => match i with
    | none => D.complement
    | some j => D.projection j
  let hp : ∀ i, IsStarProjection (p i) := fun i => by
    cases i with
    | none => exact D.complement_isProjection
    | some j => exact D.isProjection j
  refine ⟨{
    Index := D.Index
    projection := p
    isProjection := hp
    central := ?_
    orthogonal := ?_
    total := ?_
    exceptional := hexceptional
    tracial := ?_ }⟩
  · intro i a
    cases i with
    | none => exact D.complement_central a
    | some j => exact D.central j a
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        exact (D.complement_central (D.projection j)).trans (D.complement_orthogonal j)
    | some i =>
      cases j with
      | none => exact D.complement_orthogonal i
      | some j => exact D.orthogonal i j (fun h => hij (congrArg some h))
  · intro a ha
    exact D.total a (ha none) (fun i => ha (some i))
  · intro i
    obtain ⟨hi, htr⟩ := D.property i
    exact htr

/-- The global theorem now requires only the local trace construction and the
classical non-II₁ vanishing theorem. -/
theorem primitive_of_local_tracial_cuts (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hlocal : LocalTracialCutInput M) (hclassical : ClassicalVanishingInput.{u})
    {n : ℕ} (f : Cochain M (n + 2)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x :=
  primitive_of_published_inputs e (centralDecompositionInput_of_local_tracial_cuts e hlocal)
    hclassical f hf

end KadisonRingrose
end BoundedHochschild

end

end OAI
