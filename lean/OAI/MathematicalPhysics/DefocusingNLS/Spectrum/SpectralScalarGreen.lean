import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalSourceCombination
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! The scalar Dirichlet/outgoing Green formula used on the high-frequency shell.
The sign of its diagonal jump is recorded explicitly. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralScalarWronskian (D U : ℂ × ℂ) : ℂ :=
  D.1 * U.2 - D.2 * U.1

noncomputable def spectralScalarField (V : ℂ) (u : ℂ × ℂ) : ℂ × ℂ :=
  (u.2, -V * u.1)

noncomputable def spectralScalarGreenState (D U : ℝ → ℂ × ℂ)
    (W : ℂ) (r t : ℝ) : ℂ × ℂ :=
  if r ≤ t then ((U t).1 / W) • D r else ((D t).1 / W) • U r

theorem spectralScalarWronskian_hasDerivAt
    (D U : ℝ → ℂ × ℂ) (V : ℂ) (r : ℝ)
    (hD : HasDerivAt D (spectralScalarField V (D r)) r)
    (hU : HasDerivAt U (spectralScalarField V (U r)) r) :
    HasDerivAt (fun t => spectralScalarWronskian (D t) (U t)) 0 r := by
  have hD₁ : HasDerivAt (fun t => (D t).1) (D r).2 r :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hD
  have hD₂ : HasDerivAt (fun t => (D t).2) (-V*(D r).1) r :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hD
  have hU₁ : HasDerivAt (fun t => (U t).1) (U r).2 r :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hU
  have hU₂ : HasDerivAt (fun t => (U t).2) (-V*(U r).1) r :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt r hU
  have h := (hD₁.mul hU₂).sub (hD₂.mul hU₁)
  apply h.congr_deriv
  ring

theorem spectralScalarGreenState_jump (D U : ℂ × ℂ)
    (hW : spectralScalarWronskian D U ≠ 0) :
    (D.1 / spectralScalarWronskian D U) • U -
      (U.1 / spectralScalarWronskian D U) • D = (0,1) := by
  apply Prod.ext <;> dsimp only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,
    Prod.smul_snd,smul_eq_mul,spectralScalarWronskian] at *
  · ring
  · field_simp

theorem spectralScalarGreenState_left (D U : ℝ → ℂ × ℂ)
    (W : ℂ) (R t : ℝ) (hRt : R ≤ t) (hD : (D R).1=0) :
    (spectralScalarGreenState D U W R t).1=0 := by
  simp only [spectralScalarGreenState,ite_eq_left hRt,Prod.smul_fst,smul_eq_mul,hD,mul_zero]

theorem spectralScalarGreenState_right (D U : ℝ → ℂ × ℂ)
    (W beta : ℂ) (E t : ℝ) (htE : t < E) (hU : (U E).2=beta*(U E).1) :
    (spectralScalarGreenState D U W E t).2=
      beta*(spectralScalarGreenState D U W E t).1 := by
  simp only [spectralScalarGreenState,ite_eq_right (not_le.mpr htE),Prod.smul_fst,
    Prod.smul_snd,smul_eq_mul,hU]
  ring

/-- Variation of constants with the Dirichlet and outgoing scalar solutions.
The two derivatives of the scalar primitives cancel in the value component. -/
theorem spectralScalarGreen_variation
    (D U : ℝ → ℂ × ℂ) (A B : ℝ → ℂ) (V W f : ℂ) (r : ℝ)
    (hW : W ≠ 0) (hdet : spectralScalarWronskian (D r) (U r)=W)
    (hD : HasDerivAt D (spectralScalarField V (D r)) r)
    (hU : HasDerivAt U (spectralScalarField V (U r)) r)
    (hA : HasDerivAt A ((D r).1*f/W) r)
    (hB : HasDerivAt B (-((U r).1*f/W)) r) :
    HasDerivAt (fun t => A t • U t + B t • D t)
      (spectralScalarField V (A r • U r + B r • D r) + (0,f)) r := by
  apply ((hA.smul hU).add (hB.smul hD)).congr_deriv
  have he : (D r).1*(U r).2-(D r).2*(U r).1=W := hdet
  apply Prod.ext <;> dsimp only [spectralScalarField,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  · ring
  · field_simp
    linear_combination f*he

end DefocusingNLS

end OAI
