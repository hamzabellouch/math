import OAI.Analysis.FactorGeneration.Supports
import OAI.Analysis.KadisonKastler.Algebra

namespace OAI

/-! # The polar support test for self-adjoint vectors

The positive spectral support gives a self-adjoint unitary whose pairing
with a self-adjoint operator is the sum of its positive and negative parts.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance polarTestOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance polarTestPreorder : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance polarTestLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance polarTestStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem selfAdjoint_polar_test (x : Algebra M) (hx : IsSelfAdjoint x) :
    ∃ u : Algebra M, IsSelfAdjoint u ∧ ‖u‖ ≤ 1 ∧
      u * x = x⁺ + x⁻ ∧ x * u = x⁺ + x⁻ := by
  let p := positiveSupport x
  let u := p.val - (1 - p.val)
  have hu : IsSelfAdjoint u := p.property.isSelfAdjoint.sub
    ((show IsSelfAdjoint (1 : Algebra M) from star_one _).sub p.property.isSelfAdjoint)
  have hs : u * u = 1 := by
    dsimp [u]
    simp only [sub_mul, mul_sub, mul_one, one_mul, p.property.isIdempotentElem.eq]
    abel
  let U : unitary (Algebra M) := ⟨u, by rw [hu.star_eq]; exact hs, by rw [hu.star_eq]; exact hs⟩
  have hn : ‖u‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial (Algebra M) with h | h
    · let := h
      rw [Subsingleton.elim u 0, norm_zero]
      exact zero_le_one
    · let := h
      exact (CStarRing.norm_coe_unitary U).le
  have hl : u * x = x⁺ + x⁻ := by
    rw [sub_mul, positiveSupport_mul x hx, positiveSupport_complement_mul x hx, sub_neg_eq_add]
  have hr : x * u = x⁺ + x⁻ := by
    have h := congrArg star hl
    simpa only [star_mul, hu.star_eq, hx.star_eq, star_add,
      (CFC.posPart_nonneg x).isSelfAdjoint.star_eq,
      (CFC.negPart_nonneg x).isSelfAdjoint.star_eq] using h
  exact ⟨u, hu, hn, hl, hr⟩

end

end KadisonKastler

end OAI
