import OAI.Combinatorics.ThinTrees.ShortcutDuality

namespace OAI

universe uι

section
open Matrix
namespace StrongThinTree
section Resistance
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma quadratic_cauchy_schwarz {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (x y : ι → ℝ) :
    (x ⬝ᵥ (X *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (X *ᵥ x)) * (y ⬝ᵥ (X *ᵥ y)) := by
  let := X.toSeminormedAddCommGroup hX
  let := X.toInnerProductSpace hX
  have h := real_inner_mul_inner_self_le x y
  change ((X *ᵥ y) ⬝ᵥ star x) * ((X *ᵥ y) ⬝ᵥ star x) ≤
    ((X *ᵥ x) ⬝ᵥ star x) * ((X *ᵥ y) ⬝ᵥ star y) at h
  simpa only [star_trivial, dotProduct_comm, pow_two] using h

omit [DecidableEq ι] in
lemma rankOne_quadratic (b x : ι → ℝ) :
    x ⬝ᵥ (vecMulVec b b *ᵥ x) = (b ⬝ᵥ x) ^ 2 := by
  rw [vecMulVec_mulVec]
  simp [dotProduct, Finset.mul_sum, pow_two, mul_comm, mul_left_comm]

lemma posDef_solve {X : Matrix ι ι ℝ} (hX : X.PosDef) (b : ι → ℝ) :
    X *ᵥ (X⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv X ((isUnit_iff_isUnit_det X).mp hX.isUnit),
    one_mulVec]

theorem resistance_order {X : Matrix ι ι ℝ} (hX : X.PosDef)
    (b : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    b ⬝ᵥ (X⁻¹ *ᵥ b) ≤ t ↔ (t • X - vecMulVec b b).PosSemidef := by
  let y := X⁻¹ *ᵥ b
  have hsolve : X *ᵥ y = b := posDef_solve hX b
  have hq (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (X *ᵥ x) := by
    simpa only [star_trivial] using hX.posSemidef.dotProduct_mulVec_nonneg x
  have hr : 0 ≤ b ⬝ᵥ y := by
    simpa only [hsolve, dotProduct_comm] using hq y
  constructor
  · intro h
    have hb : (vecMulVec b b).IsHermitian := by
      simpa only [star_trivial] using (posSemidef_vecMulVec_self_star b).isHermitian
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      ((hX.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial t))).sub hb) ?_
    intro x
    have hcs := quadratic_cauchy_schwarz hX.posSemidef x y
    rw [hsolve] at hcs
    have hm : (x ⬝ᵥ (X *ᵥ x)) * (b ⬝ᵥ y) ≤ (x ⬝ᵥ (X *ᵥ x)) * t :=
      mul_le_mul_of_nonneg_left h (hq x)
    rw [dotProduct_comm y b, dotProduct_comm x b] at hcs
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, rankOne_quadratic]
    nlinarith
  · intro h
    have htest := h.dotProduct_mulVec_nonneg y
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, rankOne_quadratic, hsolve, dotProduct_comm y b] at htest
    change b ⬝ᵥ y ≤ t
    nlinarith

theorem resistance_antitone {X Y : Matrix ι ι ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) (hXY : (X - Y).PosSemidef) (b : ι → ℝ) :
    b ⬝ᵥ (X⁻¹ *ᵥ b) ≤ b ⬝ᵥ (Y⁻¹ *ᵥ b) := by
  let x := X⁻¹ *ᵥ b
  let y := Y⁻¹ *ᵥ b
  have hx : X *ᵥ x = b := posDef_solve hX b
  have hy : Y *ᵥ y = b := posDef_solve hY b
  have hrX : 0 ≤ b ⬝ᵥ x := by
    simpa only [star_trivial, hx, dotProduct_comm] using
      hX.posSemidef.dotProduct_mulVec_nonneg x
  have hrY : 0 ≤ b ⬝ᵥ y := by
    simpa only [star_trivial, hy, dotProduct_comm] using
      hY.posSemidef.dotProduct_mulVec_nonneg y
  have hcomp : x ⬝ᵥ (Y *ᵥ x) ≤ b ⬝ᵥ x := by
    have h := hXY.dotProduct_mulVec_nonneg x
    simp only [star_trivial, sub_mulVec, dotProduct_sub, hx, dotProduct_comm x b] at h
    linarith
  have hcs := quadratic_cauchy_schwarz hY.posSemidef x y
  rw [hy, dotProduct_comm x b, dotProduct_comm y b] at hcs
  have hm := mul_le_mul_of_nonneg_right hcomp hrY
  change b ⬝ᵥ x ≤ b ⬝ᵥ y
  nlinarith

end Resistance
end StrongThinTree

end

end OAI
