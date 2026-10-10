import OAI.Analysis.KadisonKastler.FiniteInnerTransport

namespace OAI

/-! # Composition and scalar invariance of finite inner averages -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace FiniteInnerAverage

/-- Applying one finite average after another is again a finite average. -/
def comp (B A : FiniteInnerAverage M) : FiniteInnerAverage M where
  Index := A.Index × B.Index
  fintype := inferInstance
  nonempty := inferInstance
  unitary p := B.unitary p.2 * A.unitary p.1

theorem comp_apply (B A : FiniteInnerAverage M) (x : H →L[ℂ] H) :
    (B.comp A).apply x = B.apply (A.apply x) := by
  change (Fintype.card (A.Index × B.Index) : ℂ)⁻¹ •
      (∑ p : A.Index × B.Index,
        unitaryConj (ambientAlgebraUnitary (B.unitary p.2 * A.unitary p.1)) x) =
    B.linear ((Fintype.card A.Index : ℂ)⁻¹ •
      ∑ i, unitaryConj (ambientAlgebraUnitary (A.unitary i)) x)
  rw [B.linear.map_smul, map_sum]
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev, Fintype.sum_prod_type]
  have hu (i : A.Index) (j : B.Index) :
      unitaryConj (ambientAlgebraUnitary (B.unitary j * A.unitary i)) x =
        unitaryConj (ambientAlgebraUnitary (B.unitary j))
          (unitaryConj (ambientAlgebraUnitary (A.unitary i)) x) := by
    have he : ambientAlgebraUnitary (B.unitary j * A.unitary i) =
        ambientAlgebraUnitary (B.unitary j) * ambientAlgebraUnitary (A.unitary i) := by
      apply Subtype.ext
      rfl
    rw [he, unitaryConj_mul]
  simp only [hu]
  change ((Fintype.card B.Index : ℂ)⁻¹ * (Fintype.card A.Index : ℂ)⁻¹) •
      (∑ i, ∑ j, unitaryConj (ambientAlgebraUnitary (B.unitary j))
        (unitaryConj (ambientAlgebraUnitary (A.unitary i)) x)) =
    (Fintype.card A.Index : ℂ)⁻¹ • ∑ i,
      (Fintype.card B.Index : ℂ)⁻¹ • ∑ j,
        unitaryConj (ambientAlgebraUnitary (B.unitary j))
          (unitaryConj (ambientAlgebraUnitary (A.unitary i)) x)
  rw [← Finset.smul_sum, smul_smul, mul_comm]

theorem apply_scalar (A : FiniteInnerAverage M) (z : ℂ) :
    A.apply (z • (1 : H →L[ℂ] H)) = z • (1 : H →L[ℂ] H) := by
  have h (i : A.Index) : unitaryConj (ambientAlgebraUnitary (A.unitary i))
      (z • (1 : H →L[ℂ] H)) = z • (1 : H →L[ℂ] H) := by
    simp only [unitaryConj, mul_smul_comm, mul_one, smul_mul_assoc,
      Unitary.mul_star_self_of_mem (ambientAlgebraUnitary (A.unitary i)).property]
  change finiteAverage (fun i => unitaryConj (ambientAlgebraUnitary (A.unitary i))
    (z • (1 : H →L[ℂ] H))) = _
  simp only [h]
  exact finiteAverage_const _

theorem algebraApply_selfAdjoint (A : FiniteInnerAverage M)
    (x : Algebra M) (hx : IsSelfAdjoint x) : IsSelfAdjoint (A.algebraApply x) := by
  have hs : IsSelfAdjoint (∑ i, (A.unitary i : Algebra M) * x *
      star (A.unitary i : Algebra M)) := isSelfAdjoint_sum _ (fun i _ => hx.conjugate _)
  change star ((Fintype.card A.Index : ℂ)⁻¹ •
      (∑ i, (A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M))) =
    (Fintype.card A.Index : ℂ)⁻¹ •
      (∑ i, (A.unitary i : Algebra M) * x * star (A.unitary i : Algebra M))
  rw [star_smul, hs.star_eq]
  simp only [star_inv₀, star_natCast]

end FiniteInnerAverage

end

end KadisonKastler

end OAI
