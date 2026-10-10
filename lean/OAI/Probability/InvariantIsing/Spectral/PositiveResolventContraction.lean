import OAI.Probability.InvariantIsing.Spectral.PositiveResolventSpectrum

namespace OAI

/-! A dimension-free quadratic contraction for positive resolvents. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

lemma positiveResolvent_quadratic_contraction {N : ℕ} {t : ℝ} (ht : 0 < t)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.PosSemidef) (x : Fin N → ℝ) :
    t*((positiveResolvent t B *ᵥ x) ⬝ᵥ (positiveResolvent t B *ᵥ x)) ≤
      x ⬝ᵥ (positiveResolvent t B *ᵥ x) := by
  let y := positiveResolvent t B *ᵥ x
  have hinv : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B)*positiveResolvent t B = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (((Matrix.PosDef.one.smul ht).add_posSemidef hB).det_pos.ne'))
  have hy : (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) *ᵥ y = x := by
    change (t • (1 : Matrix (Fin N) (Fin N) ℝ)+B) *ᵥ (positiveResolvent t B *ᵥ x) = x
    rw [Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec]
  have hp : 0 ≤ y ⬝ᵥ (B *ᵥ y) := by
    simpa only [star_trivial] using hB.dotProduct_mulVec_nonneg y
  have hh := congrArg (fun z => y ⬝ᵥ z) hy
  rw [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul] at hh
  simp only [smul_eq_mul] at hh
  rw [dotProduct_comm x y]
  change t*(y ⬝ᵥ y) ≤ y ⬝ᵥ x
  linarith

end InvariantIsing

end

end OAI
