import OAI.GroupTheory.PolycyclicRecognition.Geometry.WordChartHeight
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledBasisScaleChange
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles

namespace OAI

/-! # Exact coordinate and height identities between two chart scales -/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Finite J]

/-- Coordinates of the same Lie-algebra point in the second scaled basis. -/
def basisScaleTransition (b : Basis J ℝ L) (cost : J → ℝ) (r t : ℝ) :
    (J → ℝ) ≃ₗ[ℝ] (J → ℝ) :=
  (exponentialRescaleBasis b cost r).equivFun.symm.trans
    (exponentialRescaleBasis b cost t).equivFun

theorem basisScaleTransition_point (b : Basis J ℝ L) (cost : J → ℝ)
    (r t : ℝ) (z : J → ℝ) :
    (exponentialRescaleBasis b cost t).equivFun.symm (basisScaleTransition b cost r t z) =
      (exponentialRescaleBasis b cost r).equivFun.symm z :=
  (exponentialRescaleBasis b cost t).equivFun.symm_apply_apply _

/-- Enlarging a scale contracts all coordinates with nonnegative weight. -/
theorem norm_basisScaleTransition_le [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) (hcost : ∀ j, 0 ≤ cost j)
    {r t : ℝ} (hrt : r ≤ t) (z : J → ℝ) :
    ‖basisScaleTransition b cost r t z‖ ≤ ‖z‖ := by
  have hh := norm_scale_exponentialRescaleBasis_le b cost t r 0
    (fun j => mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrt) (hcost j))
    ((exponentialRescaleBasis b cost r).equivFun.symm z)
  simpa only [basisScaleTransition, LinearEquiv.trans_apply, Real.exp_zero, one_mul,
    LinearEquiv.apply_symm_apply] using hh

/-- A bracket-killing height scales by the physical scale ratio, exactly. -/
theorem wordChartScaleTransition_height
    {I W : Type*} [Fintype I] [DecidableEq I] [AddCommGroup W] [Module ℝ W]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (height : L →ₗ[ℝ] W) (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (z : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)
    height (b.equivFun.symm (basisScaleTransition b cost (Real.log r) (Real.log t) z)) =
      (r / t) • height (b.equivFun.symm z) := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => (bracketWordLength (β.val j : FreeMagma I) : ℝ)
  have h₁ := word_length_chart_height X S β height hkill hr z
  have h₂ := word_length_chart_height X S β height hkill ht
    (basisScaleTransition b cost (Real.log r) (Real.log t) z)
  rw [basisScaleTransition_point] at h₂
  have hh := congrArg (fun w : W => t⁻¹ • w) (h₂.symm.trans h₁)
  simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, div_eq_mul_inv, mul_comm] using hh

/-- If the two charts represent the same point, their actual profiles
agree after multiplication by the physical scale. -/
theorem scaled_profile_eq_of_chart_eq
    {G W Z : Type*} [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (map : G → W) (x k : G) {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (φ ψ : Z → G) (z z' : Z) (hpoint : φ z = ψ z') :
    r • rescaledMapProfile map x k (Real.log r) φ z =
      t • rescaledMapProfile map x k (Real.log t) ψ z' := by
  simp only [rescaledMapProfile, Real.exp_log hr, Real.exp_log ht, smul_smul,
    mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ ht.ne', one_smul, hpoint]

end PolycyclicRecognition

end

end OAI
