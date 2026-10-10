import OAI.NumberTheory.JointDickman.Analysis.ZetaLogarithmicBound
import OAI.NumberTheory.JointDickman.Analysis.ZetaLogFrequency

namespace OAI

/-! # Uniform sublogarithmic zeta bounds away from zero frequency -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem zeta_uniform_sublog {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ 2*X →
      ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤ η*Real.log X := by
  let B : ℝ := 2+4/η
  have hB : 2 ≤ B := by dsimp [B]; linarith [div_pos (show (0:ℝ) < 4 by norm_num) hη]
  have hB0 : 0 < B := by linarith
  have hBcoef : 1/B ≤ η/4 := by
    apply (div_le_iff₀ hB0).mpr
    have he : (η/4)*B = η/2+1 := by dsimp [B]; field_simp; ring
    rw [he]
    linarith
  obtain ⟨C,hC,hlarge⟩ := zeta_logarithmic_bound hB
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hlarge
  obtain ⟨K,hK,hsmall⟩ := zeta_log_frequency_norm (show (0:ℝ) ≤ 1 by norm_num)
  have hlog := Real.tendsto_log_atTop
  have hpower := (tendsto_rpow_atTop (show (0:ℝ) < 3/4 by norm_num)).comp hlog
  filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (2 : ℝ),hlog.eventually_ge_atTop T₀,
    hlog.eventually_ge_atTop (2*C/η),hpower.eventually_ge_atTop (K/η)]
    with X hX hX2 hXT hXC hXK
  intro t htlo ht
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlog0 : 0 < Real.log X := by linarith
  have hσ1 : 1 < 1+1/Real.log X := by linarith [one_div_pos.mpr hlog0]
  have hσ2 : 1+1/Real.log X ≤ 2 := by
    have hh := (div_le_one hlog0).mpr hlog1
    linarith
  by_cases htlog : |t| ≤ Real.log X
  · have hb := hsmall X hX t htlo (by simpa using htlog)
    have hKbound : K ≤ η*(Real.log X)^(3/4:ℝ) := by
      simpa only [Function.comp_def, mul_comm] using (div_le_iff₀ hη).mp hXK
    have he : (Real.log X)^(3/4:ℝ)*(Real.log X)^(1/4:ℝ) = Real.log X := by
      rw [←Real.rpow_add hlog0]
      norm_num
    exact hb.trans (by
      calc
        _ ≤ (η*(Real.log X)^(3/4:ℝ))*(Real.log X)^(1/4:ℝ) :=
          mul_le_mul_of_nonneg_right hKbound (by positivity)
        _ = _ := by rw [mul_assoc,he])
  · have ht0 : 0 < |t| := hlog0.trans (lt_of_not_ge htlog)
    have hb := hT₀ |t| (hXT.trans (lt_of_not_ge htlog).le) t (1+1/Real.log X) rfl hσ1 hσ2
    have hCbound : C ≤ (η/2)*Real.log X := by
      have hh := (div_le_iff₀ hη).mp hXC
      nlinarith
    have hlt₀ := Real.log_le_log ht0 ht
    have hlt : Real.log |t| ≤ 2*Real.log X := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : X ≠ 0)] at hlt₀
      have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hX2
      linarith
    calc
      _ ≤ (1/B)*Real.log |t|+C := hb
      _ ≤ (1/B)*(2*Real.log X)+C := add_le_add (mul_le_mul_of_nonneg_left hlt (by positivity : 0 ≤ 1/B)) le_rfl
      _ ≤ (η/4)*(2*Real.log X)+(η/2)*Real.log X :=
        add_le_add (mul_le_mul_of_nonneg_right hBcoef (by positivity)) hCbound
      _ = _ := by ring

end JointDickman

end OAI
