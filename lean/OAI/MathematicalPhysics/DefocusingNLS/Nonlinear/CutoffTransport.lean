import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffLaplacian
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFreeStep
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # The moving cutoff has zero transport derivative

This identifies the displayed residual with the actual similarity-equation
defect of the cutoff profile, including its time derivative.
-/

open scoped Laplacian ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def movingProfileCutoff (χ : E → ℝ) (L s : ℝ) (y : E) : ℝ :=
  χ ((L⁻¹ * Real.exp (-s / 2)) • y)

theorem movingProfileCutoff_eq (χ : E → ℝ) (L s : ℝ) (y : E) :
    movingProfileCutoff χ L s y = χ ((expandingRadius L s)⁻¹ • y) := by
  unfold movingProfileCutoff expandingRadius
  rw [mul_inv_rev, ← Real.exp_neg]
  congr 2
  ring_nf

theorem hasDerivAt_movingProfileCutoff (χ : E → ℝ) (hχ : Differentiable ℝ χ)
    (L s : ℝ) (y : E) :
    HasDerivAt (fun t => movingProfileCutoff χ L t y)
      (-(1 / 2 : ℝ) * fderiv ℝ χ ((L⁻¹ * Real.exp (-s / 2)) • y)
        ((L⁻¹ * Real.exp (-s / 2)) • y)) s := by
  let c := L⁻¹ * Real.exp (-s / 2)
  have hc : HasDerivAt (fun t : ℝ => L⁻¹ * Real.exp (-t / 2)) (-(1 / 2 : ℝ) * c) s := by
    apply (((hasDerivAt_id s).neg.div_const 2).exp.const_mul L⁻¹).congr_deriv
    dsimp [c]
    ring_nf
  have h := (hχ (c • y)).hasFDerivAt.comp_hasDerivAt s (hc.smul_const y)
  apply h.congr_deriv
  simp only [map_smul, smul_eq_mul]
  dsimp only [c]
  ring_nf

theorem movingProfileCutoff_transport (χ : E → ℝ) (hχ : Differentiable ℝ χ)
    (L s : ℝ) (y : E) :
    deriv (fun t => movingProfileCutoff χ L t y) s +
      fderiv ℝ (movingProfileCutoff χ L s) y ((1 / 2 : ℝ) • y) = 0 := by
  rw [(hasDerivAt_movingProfileCutoff χ hχ L s y).deriv]
  unfold movingProfileCutoff
  rw [fderiv_comp_smul]
  simp only [smul_apply, map_smul, smul_eq_mul]
  ring_nf

noncomputable def stationarySimilarityDefect (a b : ℝ) (m : ℕ) (Q : E → ℂ) (y : E) : ℂ :=
  Δ Q y + Complex.I * (fderiv ℝ Q y ((1 / 2 : ℝ) • y) + (a : ℂ) * Q y) +
    (b : ℂ) * Q y - oddPowerNonlinearity m (Q y)

theorem movingCutoff_similarity_defect (a b L s : ℝ) (m : ℕ)
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (y : E) :
    let U : ℝ → E → ℂ := fun t z => (movingProfileCutoff χ L t z : ℂ) * Q z
    Complex.I * deriv (fun t => U t y) s +
      Δ (U s) y + Complex.I * (fderiv ℝ (U s) y ((1 / 2 : ℝ) • y) + (a : ℂ) * U s y) +
      (b : ℂ) * U s y - oddPowerNonlinearity m (U s y) =
    (movingProfileCutoff χ L s y : ℂ) * stationarySimilarityDefect a b m Q y +
      cutoffResidual m (expandingRadius L s) χ Q y := by
  intro U
  let c : E → ℝ := movingProfileCutoff χ L s
  have hc : ContDiff ℝ ∞ c := hχ.comp (contDiff_id.const_smul _)
  have hcC : ContDiff ℝ ∞ (fun z => (c z : ℂ)) := Complex.ofRealCLM.contDiff.comp hc
  have ht : deriv (fun t => U t y) s =
      ((deriv (fun t => movingProfileCutoff χ L t y) s : ℝ) : ℂ) * Q y := by
    have hr := hasDerivAt_movingProfileCutoff χ (hχ.differentiable (by simp)) L s y
    have h := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hr).mul_const (Q y)).deriv
    rw [hr.deriv]
    exact h
  have hd : fderiv ℝ (U s) y ((1 / 2 : ℝ) • y) =
      (c y : ℂ) * fderiv ℝ Q y ((1 / 2 : ℝ) • y) +
      (fderiv ℝ c y ((1 / 2 : ℝ) • y) : ℂ) * Q y := by
    have hcast := Complex.ofRealCLM.hasFDerivAt.comp y (hc.differentiable (by simp) y).hasFDerivAt
    have hcast' : fderiv ℝ (fun z => (c z : ℂ)) y =
        Complex.ofRealCLM.comp (fderiv ℝ c y) := hcast.fderiv
    change fderiv ℝ (fun z => (c z : ℂ) * Q z) y _ = _
    rw [fderiv_fun_mul (hcC.differentiable (by simp) y) (hQ.differentiable (by simp) y), hcast']
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
    ring_nf
  have hz := movingProfileCutoff_transport χ (hχ.differentiable (by simp)) L s y
  have hzC : ((deriv (fun t => movingProfileCutoff χ L t y) s : ℝ) : ℂ) +
      (fderiv ℝ c y ((1 / 2 : ℝ) • y) : ℂ) = 0 := by exact_mod_cast hz
  have hs := cutoffResidual_spatial_identity m (expandingRadius L s) χ Q hχ hQ y
  have heq : U s = fun z => (χ ((expandingRadius L s)⁻¹ • z) : ℂ) * Q z := by
    funext z
    rw [show U s z = (movingProfileCutoff χ L s z : ℂ) * Q z from rfl,
      movingProfileCutoff_eq]
  have hspatial : Δ (U s) y - oddPowerNonlinearity m (U s y) =
      (c y : ℂ) * (Δ Q y - oddPowerNonlinearity m (Q y)) +
        cutoffResidual m (expandingRadius L s) χ Q y := by
    rw [heq]
    simpa only [c, movingProfileCutoff_eq] using hs
  rw [ht, hd]
  unfold stationarySimilarityDefect
  change _ = (c y : ℂ) * _ + _
  linear_combination hspatial + Complex.I * Q y * hzC

end DefocusingNLS

end OAI
