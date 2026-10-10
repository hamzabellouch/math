import OAI.Analysis.KadisonSimilarity.Representation.ConcretePredualDuality
import OAI.Analysis.KadisonSimilarity.Representation.ProperlyInfiniteEstimate
import OAI.Analysis.BoundedHochschild.TypeIICharacterization
import OAI.Analysis.BoundedHochschild.TypeICentralDecomposition

namespace OAI

/-! Absence of nonzero abelian projections supplies the exact diffuse
projection condition used by the increasing matrix-subfactor construction. -/

noncomputable section
namespace KadisonSimilarity

open BoundedHochschild.KadisonRingrose
open scoped ComplexOrder

universe u
variable {A X : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem diffuse_projections_of_no_abelian_projection
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] A)
    (hno : ∀ p : A, FinitePathMain.AbelianProjection p → p = 0) :
    ∀ p : A, IsStarProjection p → p ≠ 0 →
      ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  have hII : PopaTypeII.NoTypeICentralPart A := by
    intro z hz _ hz0 hI
    obtain ⟨q, hq, _, hq0, hab⟩ := hI z hz le_rfl hz0
    exact hq0 (hno q (finitePath_abelian_of_popa hq hab))
  intro p hp hp0
  obtain ⟨v, horth, hsum⟩ := typeII_projection_halving e hII hp
  have hvi0 : v.initial ≠ 0 := by
    intro hzero
    have hv : (v : A) = 0 := by simpa only [hzero, mul_zero] using v.mul_initial.symm
    apply hp0
    simpa only [HochschildComparison.PartialIso.initial,
      HochschildComparison.PartialIso.final, hv, star_zero, zero_mul, add_zero] using hsum.symm
  have hvinp : v.initial ≠ p := by
    intro heq
    have hfinal : v.final = 0 := by
      have h := hsum
      rw [heq] at h
      exact add_eq_left.mp h
    have hv : (v : A) = 0 := by simpa only [hfinal, zero_mul] using v.final_mul.symm
    apply hvi0
    simp only [HochschildComparison.PartialIso.initial, hv, star_zero, zero_mul]
  have horth' : v.final * v.initial = 0 := by
    simpa only [star_mul, v.initial_proj.isSelfAdjoint.star_eq,
      v.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star horth
  refine ⟨v.initial, v.initial_proj, hvi0, hvinp, ?_, ?_⟩
  · rw [← hsum, add_mul, v.initial_proj.isIdempotentElem.eq, horth', add_zero]
  · rw [← hsum, mul_add, v.initial_proj.isIdempotentElem.eq, horth, add_zero]

end KadisonSimilarity

end

end OAI
