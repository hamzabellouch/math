import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ChargePenalty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-!
# The concrete inverse of a charge-sector penalty

The high block of the Hubbard penalty is diagonal in the occupation basis.
That block and its inverse are continuous linear maps satisfying the
positivity, symmetry and inverse-norm hypotheses of the second-order
perturbation theorem.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace ContinuumCoulomb

variable {Basis : Type*} [Fintype Basis]

def diagonalPenaltyLinear (weight : Basis → ℝ) :
    EuclideanSpace ℂ Basis →ₗ[ℝ] EuclideanSpace ℂ Basis where
  toFun x := WithLp.toLp 2 (fun s => weight s • x s)
  map_add' x y := by ext s; simp [smul_add]
  map_smul' c x := by
    ext s
    change (weight s : ℂ) * ((c : ℂ) * x s) = (c : ℂ) * ((weight s : ℂ) * x s)
    ring

def diagonalPenalty (weight : Basis → ℝ) :
    EuclideanSpace ℂ Basis →L[ℝ] EuclideanSpace ℂ Basis :=
  (diagonalPenaltyLinear weight).toContinuousLinearMap

@[simp] theorem diagonalPenalty_apply (weight : Basis → ℝ)
    (x : EuclideanSpace ℂ Basis) (s : Basis) :
    diagonalPenalty weight x s = weight s • x s := rfl

theorem diagonalPenalty_form (weight : Basis → ℝ) (x : EuclideanSpace ℂ Basis) :
    ⟪x, diagonalPenalty weight x⟫_ℝ = ∑ s, weight s * ‖x s‖ ^ 2 := by
  simp only [PiLp.inner_apply, diagonalPenalty_apply,
    real_inner_smul_right, real_inner_self_eq_norm_sq]

theorem diagonalPenalty_symmetric (weight : Basis → ℝ)
    (x y : EuclideanSpace ℂ Basis) :
    ⟪x, diagonalPenalty weight y⟫_ℝ = ⟪diagonalPenalty weight x, y⟫_ℝ := by
  simp only [PiLp.inner_apply, diagonalPenalty_apply,
    real_inner_smul_right, real_inner_smul_left]

theorem diagonalPenalty_gap (weight : Basis → ℝ) (g : ℝ)
    (hgap : ∀ s, g ≤ weight s) (x : EuclideanSpace ℂ Basis) :
    g * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty weight x⟫_ℝ := by
  rw [diagonalPenalty_form, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hgap s) (sq_nonneg _)

theorem diagonalPenalty_norm_le (weight : Basis → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hweight : ∀ s, |weight s| ≤ C) :
    ‖diagonalPenalty weight‖ ≤ C := by
  apply (diagonalPenalty weight).opNorm_le_bound hC
  intro x
  have hsq : ‖diagonalPenalty weight x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    have hw : weight s ^ 2 ≤ C ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 (hweight s)
    simpa only [diagonalPenalty_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using
      mul_le_mul_of_nonneg_right hw (sq_nonneg ‖x s‖)
  have hn := norm_nonneg (diagonalPenalty weight x)
  have hcx : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  nlinarith

theorem diagonalPenalty_inverse_right (weight : Basis → ℝ)
    (hweight : ∀ s, weight s ≠ 0) (x : EuclideanSpace ℂ Basis) :
    diagonalPenalty weight (diagonalPenalty (fun s => (weight s)⁻¹) x) = x := by
  ext s
  simp [hweight s]

theorem diagonalPenalty_inverse_norm {g : ℝ} (hg : 0 < g) (weight : Basis → ℝ)
    (hgap : ∀ s, g ≤ weight s) :
    ‖diagonalPenalty (fun s => (weight s)⁻¹)‖ ≤ 1 / g := by
  apply diagonalPenalty_norm_le _ (by positivity)
  intro s
  have hw : 0 < weight s := hg.trans_le (hgap s)
  rw [abs_of_pos (inv_pos.mpr hw)]
  simpa only [one_div] using one_div_le_one_div_of_le hg (hgap s)

/-- High occupations exclude the singly occupied spin subspace. -/
abbrev ChargeHighBasis {m : ℕ} (occupation : Basis → Fin m → Fin 3) :=
  {s : Basis // ¬ ∀ i, occupation s i = 1}

/-- The charge-transfer gap gives a concrete bounded inverse on the high
occupation space. -/
theorem chargePenalty_inverse_data {m : ℕ} (U R : ℝ)
    (V : Fin m → Fin m → ℝ) (occupation : Basis → Fin m → Fin 3)
    (hsymm : ∀ i j, V i j = V j i) (hrow : ∀ i, ∑ j, |V i j| ≤ R)
    (hUR : R < U) (hfill : ∀ s, ∑ i, (occupation s i : ℕ) = m) :
    let weight : ChargeHighBasis occupation → ℝ :=
      fun s => chargePenalty U V (occupation s.val)
    (∀ x, diagonalPenalty weight (diagonalPenalty (fun s => (weight s)⁻¹) x) = x) ∧
      ‖diagonalPenalty (fun s => (weight s)⁻¹)‖ ≤ 1 / (U - R) ∧
      (∀ x, (U - R) * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty weight x⟫_ℝ) := by
  classical
  intro weight
  have hg : 0 < U - R := sub_pos.mpr hUR
  have hgap (s : ChargeHighBasis occupation) : U - R ≤ weight s :=
    chargePenalty_gap U R V (occupation s.val) hsymm hrow hUR.le (hfill s.val) s.property
  exact ⟨diagonalPenalty_inverse_right weight (fun s => ne_of_gt (hg.trans_le (hgap s))),
    diagonalPenalty_inverse_norm hg weight hgap, diagonalPenalty_gap weight (U - R) hgap⟩

end ContinuumCoulomb

end

end OAI
