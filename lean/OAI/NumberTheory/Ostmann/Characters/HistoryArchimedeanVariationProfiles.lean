import Mathlib.Analysis.Calculus.MeanValue
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightFourier

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Set Ostmann.Arithmetic
open scoped SchwartzMap ComplexConjugate

def historyLeafProfile (ρ : 𝓢(ℝ,ℂ)) (conjugated : Bool) (v z : ℝ) : ℂ :=
  if conjugated then conj (leafLogProfile ρ v z) else leafLogProfile ρ v z

def historyRatioProfile (z : ℝ) : ℂ := (Real.exp z : ℂ)

theorem leafLogProfile_norm_le (ρ : 𝓢(ℝ,ℂ)) (v z : ℝ) :
    ‖leafLogProfile ρ v z‖ ≤ Real.exp (z/2)*leafProfileBound ρ := by
  have hρ := SchwartzMap.norm_le_seminorm ℝ ρ (-v*Real.exp z)
  have h1 := apply_nonneg (SchwartzMap.seminorm ℝ 1 1) ρ
  unfold leafLogProfile
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  unfold leafProfileBound
  linarith

theorem historyLeafProfile_norm_le (ρ : 𝓢(ℝ,ℂ)) (b : Bool) (v : ℝ)
    {z B : ℝ} (hz : z ≤ B) :
    ‖historyLeafProfile ρ b v z‖ ≤ Real.exp (B/2)*leafProfileBound ρ := by
  have hh : ‖leafLogProfile ρ v z‖ ≤ Real.exp (B/2)*leafProfileBound ρ :=
    (leafLogProfile_norm_le ρ v z).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (leafProfileBound_pos ρ).le)
  cases b <;> simpa only [historyLeafProfile,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,
    Complex.norm_conj] using hh

theorem leafLogProfile_lipschitz (ρ : 𝓢(ℝ,ℂ)) (v : ℝ)
    {A B x y : ℝ} (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) :
    ‖leafLogProfile ρ v y-leafLogProfile ρ v x‖ ≤
      (Real.exp (B/2)*leafProfileBound ρ)*|y-x| := by
  have hd (z : ℝ) (hz : z ∈ Icc A B) :
      ‖deriv (leafLogProfile ρ v) z‖ ≤ Real.exp (B/2)*leafProfileBound ρ :=
    (leafLogProfile_deriv_bound ρ v z).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hz.2]))
        (leafProfileBound_pos ρ).le)
  simpa only [Real.norm_eq_abs] using (convex_Icc A B).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (leafLogProfile_hasDerivAt ρ v z).differentiableAt) hd hx hy

theorem historyLeafProfile_lipschitz (ρ : 𝓢(ℝ,ℂ)) (b : Bool) (v : ℝ)
    {A B x y : ℝ} (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) :
    ‖historyLeafProfile ρ b v y-historyLeafProfile ρ b v x‖ ≤
      (Real.exp (B/2)*leafProfileBound ρ)*|y-x| := by
  have hh := leafLogProfile_lipschitz ρ v hx hy
  cases b <;> simpa only [historyLeafProfile,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,
    ← map_sub,Complex.norm_conj] using hh

theorem historyRatioProfile_norm_le {z B : ℝ} (hz : z ≤ B) :
    ‖historyRatioProfile z‖ ≤ Real.exp B := by
  simpa only [historyRatioProfile,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hz

theorem historyRatioProfile_lipschitz {A B x y : ℝ}
    (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) :
    ‖historyRatioProfile y-historyRatioProfile x‖ ≤ Real.exp B*|y-x| := by
  have hh := (convex_Icc A B).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => Real.differentiable_exp.differentiableAt)
    (fun z (hz : z ∈ Icc A B) => show ‖deriv Real.exp z‖ ≤ Real.exp B by
      rw [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr hz.2)
    hx hy
  simpa only [historyRatioProfile,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hh

theorem historyRatioProfile_eq_ratio (T H : ℝ) (hH : 0 < H) :
    historyRatioProfile (Real.log (Real.exp T/H)) = (Real.exp T/H : ℂ) := by
  unfold historyRatioProfile
  rw [Real.exp_log (div_pos (Real.exp_pos _) hH)]
  push_cast
  rfl

end Ostmann.Characters

end

end OAI
