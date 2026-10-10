import OAI.Probability.InvariantIsing.Spectral.PositiveRankOneInverse

namespace OAI

/-! The exact quadratic and trace increments of a positive rank-one resolvent update. -/
noncomputable section
open Matrix
namespace InvariantIsing

lemma positive_rankOne_quadratic {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef)
    (x : Fin N → ℝ) :
    x ⬝ᵥ ((A+vecMulVec x x)⁻¹ *ᵥ x) = (x ⬝ᵥ (A⁻¹ *ᵥ x))/(1+x ⬝ᵥ (A⁻¹ *ᵥ x)) := by
  let u := A⁻¹ *ᵥ x
  let q := x ⬝ᵥ u
  have hq : 0 < 1+q := by
    have hh := hA.inv.posSemidef.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hh
    change 0 ≤ q at hh
    linarith
  have hh : vecMulVec u u *ᵥ x = q • u := by
    ext i
    simp only [Matrix.mulVec,Matrix.vecMulVec_apply,dotProduct,Pi.smul_apply,smul_eq_mul]
    dsimp only [q]
    simp only [dotProduct]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [positive_rankOne_inverse A hA x,Matrix.sub_mulVec,Matrix.smul_mulVec]
  change x ⬝ᵥ (u-(1+q)⁻¹ • (vecMulVec u u *ᵥ x)) = q/(1+q)
  rw [hh,dotProduct_sub,dotProduct_smul,dotProduct_smul]
  change q-(1+q)⁻¹*(q*q) = q/(1+q)
  field_simp [hq.ne']
  ring

lemma positive_rankOne_trace_difference {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef)
    (x : Fin N → ℝ) :
    A⁻¹.trace-(A+vecMulVec x x)⁻¹.trace =
      ((A⁻¹ *ᵥ x) ⬝ᵥ (A⁻¹ *ᵥ x))/(1+x ⬝ᵥ (A⁻¹ *ᵥ x)) := by
  rw [positive_rankOne_inverse A hA x,Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_vecMulVec]
  simp only [smul_eq_mul]
  ring

end InvariantIsing

end

end OAI
