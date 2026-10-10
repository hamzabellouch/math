import OAI.NumberTheory.CubicMoment.Estimates.ShrinkingVariance
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-! An actual nonnegative cutoff supported in a cell of width 1/J,
with a plateau on the central half of that cell. -/
noncomputable section
open Set Metric
open scoped ContDiff SchwartzMap
namespace CubicFirstMoment

def thinBaseBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1/4, rOut := 1/2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }

def thinBaseSchwartz : 𝓢(ℝ,ℂ) :=
  (thinBaseBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp thinBaseBump.contDiff)

@[simp] lemma thinBaseSchwartz_apply (x : ℝ) :
    thinBaseSchwartz x = (thinBaseBump x : ℂ) := rfl

lemma thinBaseSchwartz_compact : HasCompactSupport (thinBaseSchwartz : ℝ → ℂ) :=
  thinBaseBump.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

def thinCellCutoff (J x : ℝ) : ℝ :=
  thinBaseBump (J*(x-(1+1/(2*J))))

lemma thinCellCutoff_nonneg (J x : ℝ) : 0 ≤ thinCellCutoff J x := thinBaseBump.nonneg

lemma thinCellCutoff_le_one (J x : ℝ) : thinCellCutoff J x ≤ 1 := thinBaseBump.le_one

lemma thinCellCutoff_eq_affine (J : ℝ) (hJ : J ≠ 0) :
    (fun x => (thinCellCutoff J x : ℂ)) =
      affineSchwartzProfile thinBaseSchwartz J (1+1/(2*J)) hJ := rfl

lemma thinCellCutoff_compact (J : ℝ) (hJ : J ≠ 0) :
    HasCompactSupport (fun x => (thinCellCutoff J x : ℂ)) := by
  rw [thinCellCutoff_eq_affine J hJ]
  exact affineSchwartzProfile_compact thinBaseSchwartz thinBaseSchwartz_compact J _ hJ

lemma thinCellCutoff_smooth (J : ℝ) (hJ : J ≠ 0) :
    ContDiff ℝ ∞ (fun x => (thinCellCutoff J x : ℂ)) := by
  rw [thinCellCutoff_eq_affine J hJ]
  exact (affineSchwartzProfile thinBaseSchwartz J _ hJ).smooth ⊤

lemma thinCellCutoff_norm (J x : ℝ) : ‖(thinCellCutoff J x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_of_nonneg (thinCellCutoff_nonneg J x)]
  exact thinCellCutoff_le_one J x

lemma thinCellCutoff_support {J : ℝ} (hJ : 0 < J) (x : ℝ)
    (hx : (thinCellCutoff J x : ℂ) ≠ 0) : 1 ≤ x ∧ x ≤ 1+1/J := by
  have hm : J*(x-(1+1/(2*J))) ∈ Function.support thinBaseBump := by
    change thinBaseBump _ ≠ 0
    exact fun h => hx (by change (thinBaseBump _ : ℂ) = 0; rw [h]; rfl)
  rw [thinBaseBump.support_eq] at hm
  have ha : |J*(x-(1+1/(2*J)))| < 1/2 := by
    simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,thinBaseBump] using hm
  have hh := abs_lt.mp ha
  have hc : J*(1+1/(2*J)) = J+1/2 := by field_simp
  have hd : J*(1+1/J) = J+1 := by field_simp
  constructor
  · nlinarith
  · nlinarith

lemma thinCellCutoff_one {J x : ℝ} (hJ : 0 < J)
    (hx : 1+1/(4*J) ≤ x ∧ x ≤ 1+3/(4*J)) : thinCellCutoff J x = 1 := by
  apply thinBaseBump.one_of_mem_closedBall
  change dist (J*(x-(1+1/(2*J)))) 0 ≤ 1/4
  rw [dist_zero_right,Real.norm_eq_abs]
  have hc : J*(1+1/(2*J)) = J+1/2 := by field_simp
  have hl : J*(1+1/(4*J)) = J+1/4 := by field_simp
  have hu : J*(1+3/(4*J)) = J+3/4 := by field_simp
  have hxl := mul_le_mul_of_nonneg_left hx.1 hJ.le
  have hxu := mul_le_mul_of_nonneg_left hx.2 hJ.le
  apply abs_le.mpr
  constructor <;> nlinarith

end CubicFirstMoment

end

end OAI
