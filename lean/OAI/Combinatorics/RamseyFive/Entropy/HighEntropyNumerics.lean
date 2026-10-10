import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_high_entropy_contradiction {η : ℝ} (hη : 0<η)
    (c C : ℝ) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ (q n h E : ℝ),q=Real.exp σ→
      c*q*σ^(1+η)≤n→0≤h→h≤2*q*σ^beta η→
      4*σ*n+η*n*Real.log σ+n*(Real.log c-1)-Real.log (2*C)≤E→
      E≤3*h*(8*σ+Real.log 4)+n*(4*σ+Real.log 2)→False := by
  have hb : 0<η-beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>6*(8+Real.log 4)*σ^(-(η-beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hb).const_mul (6*(8+Real.log 4))
  have hexp : Tendsto (fun σ : ℝ=>c*Real.exp σ) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  have hlog : Tendsto (fun σ : ℝ=>η*Real.log σ) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hη
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hc,
    hexp.eventually_ge_atTop (Real.log (2*C)),
    hlog.eventually_gt_atTop (Real.log 2+3-Real.log c)] with σ hσ ht he hg
  intro q n h E hq hn hh0 hh hlo hhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hq0 : 0<q := hq ▸Real.exp_pos σ
  have hp : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
  have hn0 : 0<n := (by positivity : 0<c*q*σ^(1+η)).trans_le hn
  have he' : Real.log (2*C)≤n := by
    calc
      _ ≤ c*q := by simpa only [hq] using he
      _ ≤ c*q*σ^(1+η) := le_mul_of_one_le_right (by positivity) hp
      _ ≤ n := hn
  have hm : 3*h*(8*σ+Real.log 4)≤n := by
    have hl4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤3*(2*q*σ^beta η)*((8+Real.log 4)*σ) := by gcongr; nlinarith
      _ =(6*(8+Real.log 4)*σ^(-(η-beta η)))*(q*σ^(1+η)) := by
        rw [show 3*(2*q*σ^beta η)*((8+Real.log 4)*σ)=
          6*(8+Real.log 4)*q*(σ^beta η*σ^(1:ℝ)) by rw [Real.rpow_one];ring]
        rw [show (6*(8+Real.log 4)*σ^(-(η-beta η)))*(q*σ^(1+η))=
          6*(8+Real.log 4)*q*(σ^(-(η-beta η))*σ^(1+η)) by ring]
        rw [←Real.rpow_add hs,←Real.rpow_add hs]
        congr 2
        ring
      _ ≤c*(q*σ^(1+η)) := mul_le_mul_of_nonneg_right ht.le (by positivity)
      _ ≤n := by simpa only [mul_assoc] using hn
  have hg' := mul_lt_mul_of_pos_right hg hn0
  nlinarith
end
end SharpRamseyFive.ParameterHierarchy

end OAI
