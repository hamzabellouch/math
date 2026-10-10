import OAI.NumberTheory.JointDickman.Analysis.MellinApplicationScales

namespace OAI

/-! # Constant and linear frequency costs in the canonical estimate -/
namespace JointDickman
open Filter TwoPointCorrelations
open scoped Topology

noncomputable def canonicalAffineBase (C H : ℝ) : ℝ :=
  5632*Real.exp 1*(8/mellinFirstPrime H+4/mellinResolution H)+
    2048*Real.exp 2/mellinResolution H+4/mellinFirstPrime H+
    96*Real.exp 1*C*Real.log (mellinFirstPrime H)/Real.log (mellinLastPrime H)

noncomputable def canonicalAffineSlope (C H : ℝ) : ℝ :=
  5632*Real.exp 1*(8/mellinFirstPrime H+4/mellinResolution H)+
    2048*Real.exp 2*mellinLastPrime H/mellinResolution H+4/mellinFirstPrime H+
    48*Real.exp 1*C*Real.log (mellinFirstPrime H)/Real.log (mellinLastPrime H)

theorem canonical_affine_budget (C : ℝ) :
    Tendsto (fun H => canonicalAffineBase C H+canonicalAffineSlope C H/H) atTop (𝓝 0) := by
  have h1 := mellinWindowCost_tendsto_zero.const_mul 2
  have h2 := ((tendsto_inv_atTop_zero.add_const 2).mul mellin_typical_cost_tendsto_zero).const_mul
    (48*Real.exp 1*C)
  have hh := h1.add h2
  simp only [mul_zero,add_zero] at hh
  convert hh using 1
  funext H
  dsimp only [canonicalAffineBase,canonicalAffineSlope,mellinWindowCost]
  ring

theorem canonical_affine_nonneg {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ H : ℝ in atTop, 0 ≤ canonicalAffineBase C H ∧ 0 ≤ canonicalAffineSlope C H := by
  filter_upwards [eventually_mellin_application_scales] with H hH
  have hP : 0 ≤ mellinFirstPrime H := by linarith [hH.1,Real.exp_pos 1]
  have hQ : 0 ≤ mellinLastPrime H := hP.trans hH.2.1
  have hR : 0 ≤ mellinResolution H := by linarith [hH.2.2.2.2.2]
  have hlogP : 0 ≤ Real.log (mellinFirstPrime H) := by linarith [hH.2.2.1]
  have hlogQ : 0 ≤ Real.log (mellinLastPrime H) := by linarith [hH.2.2.2.1]
  constructor <;> dsimp [canonicalAffineBase,canonicalAffineSlope] <;> positivity

end JointDickman

end OAI
