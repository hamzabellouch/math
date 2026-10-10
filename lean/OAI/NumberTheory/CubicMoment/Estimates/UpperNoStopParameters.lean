import OAI.NumberTheory.CubicMoment.Estimates.RestrictedNoStopWindow
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! The literal no-stop thresholds in the two height ranges. The upper
range uses the smaller stopping level required by the Type-I exponent. -/
noncomputable section
open Filter
namespace CubicFirstMoment

def heightNoStopThreshold (κ X T : ℝ) : ℝ :=
  if T ≤ X^(1/100:ℝ) then X^(38/100:ℝ) else X^(1/3-κ)

def heightNoStopOuterBound (κ X T : ℝ) : ℝ :=
  if T ≤ X^(1/100:ℝ) then X^(39/100:ℝ) else X^(1/3-κ/2)/2

lemma eventually_ordinary_noStop_window_scales {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) :
    ∀ᶠ X : ℝ in atTop,
      1 ≤ X^(39/100:ℝ) ∧
      (Real.exp hW.radius*X)^((1/100:ℝ)/4)*X^(38/100:ℝ) ≤ X^(39/100:ℝ) ∧
      2*X^(39/100:ℝ) ≤ X^(2/5:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (by norm_num : (1/400:ℝ)+38/100 < 39/100)
      ((Real.exp hW.radius)^(1/400:ℝ)),
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 2/5) 2]
    with X hX hd hs
  refine ⟨Real.one_le_rpow hX (by norm_num),?_,hs⟩
  have hXp : 0 < X := zero_lt_one.trans_le hX
  norm_num only [show (1/100:ℝ)/4 = 1/400 by norm_num]
  rw [Real.mul_rpow (Real.exp_pos _).le hXp.le,mul_assoc,←Real.rpow_add hXp]
  convert hd using 1
  norm_num

lemma eventually_upper_noStop_window_scales {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/3) :
    ∀ᶠ X : ℝ in atTop,
      1 ≤ X^(1/3-κ/2)/2 ∧
      (Real.exp hW.radius*X)^(κ/4)*X^(1/3-κ) ≤ X^(1/3-κ/2)/2 := by
  have ha : 0 < 1/3-κ/2 := by linarith
  have ht := (tendsto_rpow_atTop ha).eventually_ge_atTop 2
  have hd := eventually_rpow_le_const_mul
    (show κ/4+(1/3-κ) < 1/3-κ/2 by linarith)
    (C := ((Real.exp hW.radius)^(κ/4))⁻¹/2) (by positivity)
  filter_upwards [eventually_gt_atTop (0:ℝ),ht,hd] with X hX hY hd
  refine ⟨by linarith,?_⟩
  rw [Real.mul_rpow (Real.exp_pos _).le hX.le,mul_assoc,←Real.rpow_add hX]
  have hp : 0 < (Real.exp hW.radius)^(κ/4) := by positivity
  have hh := mul_le_mul_of_nonneg_left hd hp.le
  apply hh.trans_eq
  field_simp

lemma eventually_height_noStop_window_scales {γ : Type*} {W : γ → ℝ → ℂ}
    (hW : UniformLogWeights W) {κ η : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/3) :
    ∀ᶠ X : ℝ in atTop, ∀ T : ℝ, T ≤ X^(1/6+η) →
      1 ≤ heightNoStopOuterBound κ X T ∧
      (Real.exp hW.radius*X)^((if T ≤ X^(1/100:ℝ) then 1/100 else κ)/4)*
        heightNoStopThreshold κ X T ≤ heightNoStopOuterBound κ X T ∧
      ((2*heightNoStopOuterBound κ X T ≤ X^(2/5:ℝ) ∧ T ≤ X^(1/100:ℝ)) ∨
        (2*heightNoStopOuterBound κ X T ≤ X^(1/3-κ/2) ∧ T ≤ X^(1/6+η))) := by
  filter_upwards [eventually_ordinary_noStop_window_scales hW,
    eventually_upper_noStop_window_scales hW hκ hκsmall] with X ho hu
  intro T hT
  by_cases hl : T ≤ X^(1/100:ℝ)
  · simp only [heightNoStopOuterBound,heightNoStopThreshold,hl,ite_true]
    exact ⟨ho.1,ho.2.1,Or.inl ⟨ho.2.2,True.intro⟩⟩
  · simp only [heightNoStopOuterBound,heightNoStopThreshold,hl,ite_false]
    exact ⟨hu.1,hu.2,Or.inr ⟨by linarith,hT⟩⟩

end CubicFirstMoment

end

end OAI
