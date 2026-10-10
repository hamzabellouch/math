import OAI.Analysis.KadisonSimilarity.Representation.CStarCorner
import OAI.Analysis.KadisonSimilarity.Representation.DyadicPhases

namespace OAI

/-! The finite dyadic spectral sums form contractive unital star
homomorphisms into the original corner. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge
open scoped BigOperators CStarAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}
  (τ : TracialRepresentation M)
  (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q)

local instance dyadicAlgebra_closed : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  Generator.Tracial.base_norm_closed M

theorem dyadicProjection_le_root (p : AlgebraProjection M) (n : ℕ)
    (i : DyadicIndex n) : dyadicProjection τ hdiff p n i ≤ p := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact (dyadicProjection_le_parent τ hdiff p n i).trans (ih i.1)

theorem dyadicEval_supported (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    p.val * dyadicEval τ hdiff p n c = dyadicEval τ hdiff p n c ∧
      dyadicEval τ hdiff p n c * p.val = dyadicEval τ hdiff p n c := by
  constructor
  · simp only [dyadicEval, projectionSum, Finset.mul_sum, mul_smul_comm]
    exact Finset.sum_congr rfl (fun i _ => congrArg (c i • ·)
      (dyadicProjection_le_root τ hdiff p n i))
  · simp only [dyadicEval, projectionSum, Finset.sum_mul, smul_mul_assoc]
    exact Finset.sum_congr rfl (fun i _ => congrArg (c i • ·)
      (projection_mul_of_le (dyadicProjection_le_root τ hdiff p n i)))

def dyadicCornerHom (p : AlgebraProjection M) (n : ℕ) :
    (DyadicIndex n → ℂ) →⋆ₐ[ℂ] CStarCorner p.val p.property where
  toFun c := ⟨dyadicEval τ hdiff p n c, dyadicEval_supported τ hdiff p n c⟩
  map_zero' := Subtype.ext (by simp [dyadicEval, projectionSum])
  map_one' := by
    apply Subtype.ext
    change dyadicEval τ hdiff p n 1 =
      ((1 : CStarCorner p.val p.property) : M.toStarSubalgebra)
    rw [CStarCorner.coe_one]
    simpa only [dyadicEval, projectionSum, Pi.one_apply, one_smul] using
      dyadicProjection_sum τ hdiff p n
  map_add' c d := Subtype.ext (by simp [dyadicEval, projectionSum, add_smul,
    Finset.sum_add_distrib])
  map_mul' c d := Subtype.ext (projectionSum_mul _
    (dyadicProjection_orthogonal τ hdiff p n) c d).symm
  commutes' c := Subtype.ext (by
    change dyadicEval τ hdiff p n (fun _ => c) =
      ((algebraMap ℂ (CStarCorner p.val p.property) c :
        CStarCorner p.val p.property) : M.toStarSubalgebra)
    rw [Algebra.algebraMap_eq_smul_one]
    change dyadicEval τ hdiff p n (fun _ => c) =
      c • ((1 : CStarCorner p.val p.property) : M.toStarSubalgebra)
    rw [CStarCorner.coe_one]
    have h := congrArg (c • ·) (dyadicEval_one τ hdiff p n)
    simpa only [dyadicEval, projectionSum, Finset.smul_sum, smul_smul, mul_one] using h)
  map_star' c := Subtype.ext (projectionSum_star _ c).symm

@[simp] theorem dyadicCornerHom_coe (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    (dyadicCornerHom τ hdiff p n c : M.toStarSubalgebra) =
      dyadicEval τ hdiff p n c := rfl

theorem norm_dyadicCornerHom_le (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    ‖dyadicCornerHom τ hdiff p n c‖ ≤ C :=
  (NonUnitalStarAlgHom.norm_apply_le (dyadicCornerHom τ hdiff p n) c).trans
    ((pi_norm_le_iff_of_nonneg hC).mpr hc)

theorem dyadicCornerHom_refine (p : AlgebraProjection M) (n : ℕ)
    (c : DyadicIndex n → ℂ) :
    dyadicCornerHom τ hdiff p (n + 1) (fun i => c i.1) =
      dyadicCornerHom τ hdiff p n c :=
  Subtype.ext (dyadicEval_refine τ hdiff p n c)

end KadisonSimilarity

end

end OAI
