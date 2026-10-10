import OAI.NumberTheory.JointDickman.Analysis.CanonicalMellinEnergy
import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates

namespace OAI

/-! # Qualitative application scales for the multiscale energy bound

The large fixed logarithmic exponent pays the explicit factorial budget.
The application needs only a vanishing error as the short length grows.
-/
namespace JointDickman
open Filter TwoPointCorrelations
open scoped Topology

noncomputable def mellinFirstPrime (H : ℝ) : ℝ := (Real.log H)^(300000 : ℝ)
noncomputable def mellinLastPrime (H : ℝ) : ℝ := H^(1/2 : ℝ)
noncomputable def mellinResolution (H : ℝ) : ℝ :=
  mrtBaseResolution (mellinFirstPrime H) (mellinLastPrime H) (1/12)

lemma mellinFirstPrime_tendsto : Tendsto mellinFirstPrime atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 300000)).comp Real.tendsto_log_atTop

lemma mellinLastPrime_tendsto : Tendsto mellinLastPrime atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)

lemma mellinFirstPrime_div_last_tendsto :
    Tendsto (fun H => mellinFirstPrime H / mellinLastPrime H) atTop (𝓝 0) :=
  log_power_div_power_tendsto_zero 300000 (by norm_num)

lemma mellinLastPrime_div_length_tendsto :
    Tendsto (fun H => mellinLastPrime H / H) atTop (𝓝 0) := by
  have hh := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  dsimp [mellinLastPrime]
  have he : H^(1/2 : ℝ)/H = H^(-1/2 : ℝ) := by
    calc
      _ = H^(1/2 : ℝ)/H^(1 : ℝ) := by rw [Real.rpow_one]
      _ = H^((1/2 : ℝ)-1) := (Real.rpow_sub hH _ _).symm
      _ = _ := by norm_num
  simpa only [neg_div] using he.symm

lemma mellinResolution_eventually :
    ∀ᶠ H : ℝ in atTop, mellinResolution H =
      Real.exp ((74999/3 : ℝ)*Real.log (Real.log H) - (1/3 : ℝ)*Real.log (1/2 : ℝ)) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with H hH hH0
  unfold mellinResolution mrtBaseResolution mellinFirstPrime mellinLastPrime
  rw [Real.log_rpow hH, Real.log_rpow hH0,
    Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0) hH.ne']
  congr 1
  ring

lemma mellinResolution_tendsto : Tendsto mellinResolution atTop atTop := by
  have hm := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_mul_atTop
    (by norm_num : (0 : ℝ) < 74999/3)
  have hl : Tendsto (fun H : ℝ => (74999/3 : ℝ)*Real.log (Real.log H) -
      (1/3 : ℝ)*Real.log (1/2 : ℝ)) atTop atTop := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      tendsto_atTop_add_const_right atTop (-((1/3 : ℝ)*Real.log (1/2 : ℝ))) hm
  have hh := Real.tendsto_exp_atTop.comp hl
  exact hh.congr' (mellinResolution_eventually.mono fun _ h => h.symm)

/-- All fixed-scale numerical hypotheses of the canonical partition hold
for every sufficiently large short length. -/
theorem eventually_mellin_application_scales :
    ∀ᶠ H : ℝ in atTop,
      2*Real.exp 1 ≤ mellinFirstPrime H ∧
      mellinFirstPrime H ≤ mellinLastPrime H ∧
      2 ≤ Real.log (mellinFirstPrime H) ∧ 1 ≤ Real.log (mellinLastPrime H) ∧
      8192*(Real.log (Real.log (mellinLastPrime H))+1) ≤
        (1/12 : ℝ)*Real.log (mellinFirstPrime H) ∧
      2 ≤ mellinResolution H := by
  have hPlog := Real.tendsto_log_atTop.comp mellinFirstPrime_tendsto
  have hQlog := Real.tendsto_log_atTop.comp mellinLastPrime_tendsto
  filter_upwards [mellinFirstPrime_tendsto.eventually (eventually_ge_atTop (2*Real.exp 1)),
    mellinFirstPrime_div_last_tendsto.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hPlog.eventually (eventually_ge_atTop 2), hQlog.eventually (eventually_ge_atTop 1),
    mellinResolution_tendsto.eventually (eventually_ge_atTop 2),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (1 : ℝ)] with H hP hPQ hLP hLQ hR hLL hH
  have hH0 : 0 < H := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos hH
  refine ⟨hP, (div_le_one (Real.rpow_pos_of_pos hH0 _)).mp hPQ, hLP, hLQ, ?_, hR⟩
  rw [mellinFirstPrime, mellinLastPrime, Real.log_rpow hlogH, Real.log_rpow hH0,
    Real.log_mul (by norm_num : (1/2 : ℝ) ≠ 0) hlogH.ne']
  simp only [Function.comp_apply] at hLL
  have hhalf : Real.log (1/2 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
  nlinarith

theorem mellin_typical_cost_tendsto_zero :
    Tendsto (fun H => Real.log (mellinFirstPrime H) / Real.log (mellinLastPrime H))
      atTop (𝓝 0) := by
  have hh := (log_power_div_power_tendsto_zero 1 (by norm_num : (0 : ℝ) < 1)).comp
    Real.tendsto_log_atTop
  simp only [Real.rpow_one] at hh
  have hs := hh.const_mul 600000
  simp only [mul_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with H hH
  have hH0 : 0 < H := by linarith
  have hlog : 0 < Real.log H := Real.log_pos hH
  rw [mellinFirstPrime, mellinLastPrime, Real.log_rpow hlog, Real.log_rpow hH0]
  dsimp only [Function.comp_apply]
  ring

noncomputable def mellinWindowCost (H : ℝ) : ℝ :=
  2816*Real.exp 1*(H⁻¹+1)*(8/(mellinFirstPrime H)+4/(mellinResolution H)) +
  1024*Real.exp 2*(mellinLastPrime H/H+1)/(mellinResolution H) +
  2*(H⁻¹+1)/(mellinFirstPrime H)

theorem mellinWindowCost_tendsto_zero : Tendsto mellinWindowCost atTop (𝓝 0) := by
  have hH : Tendsto (fun H : ℝ => H⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hP := tendsto_inv_atTop_zero.comp mellinFirstPrime_tendsto
  have hR := tendsto_inv_atTop_zero.comp mellinResolution_tendsto
  have hQ := mellinLastPrime_div_length_tendsto
  have h1 := ((hH.add_const 1).const_mul (2816*Real.exp 1)).mul
    ((hP.const_mul 8).add (hR.const_mul 4))
  have h2 := ((hQ.add_const 1).const_mul (1024*Real.exp 2)).mul hR
  have h3 := ((hH.add_const 1).const_mul 2).mul hP
  unfold mellinWindowCost
  simpa only [Function.comp_apply, mul_zero, add_zero, div_eq_mul_inv, mul_assoc]
    using (h1.add h2).add h3

end JointDickman

end OAI
