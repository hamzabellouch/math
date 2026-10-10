import OAI.NumberTheory.TwoPoint.Halasz.HalaszHurwitzGrowth
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakHurwitzGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Weak Hurwitz growth from the
Vinogradov-system moment proof and first-order Hurwitz cutoff. -/
namespace TwoPointCorrelations

open Filter Complex HurwitzZeta

theorem mrt_weak_hurwitz_growth : MRTWeakHurwitzGrowthInput := by
  obtain ⟨A,hA,hgrowth⟩ := halasz_hurwitz_growth
  have hrsmall : ∀ᶠ x : ℝ in atTop, x^(-(2/3:ℝ))≤ 1/5 := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2/3)).eventually
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1/5))
    exact hh.mono (fun _ hx => hx.le)
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.1 hrsmall
  let B := max M₀ (max 100 (128*A))
  have hB100 : 100≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBA : 128*A≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hBM : M₀≤ B := le_max_left _ _
  refine ⟨8,Real.exp B+3,by norm_num,by positivity,?_⟩
  intro t ht a ha s hσ hσhi hsim
  let M := mrtVKLog t
  have hM : B≤ M := by
    have hh : Real.exp B≤|t|+3 := by linarith
    have hl := Real.log_le_log (Real.exp_pos B) hh
    simpa only [Real.log_exp,M,mrtVKLog] using hl
  have hM100 : 100≤ M := hB100.trans hM
  have hM0 : 0 < M := by linarith
  have hR : mrtVKRadius t≤ 1/5 := by
    change M^(-(2/3:ℝ))≤ 1/5
    exact hM₀ M (hBM.trans hM)
  have hR0 : 0 < mrtVKRadius t := by
    change 0 < M^(-(2/3:ℝ))
    exact Real.rpow_pos_of_pos hM0 _
  have hupper : |s.im|≤|t|+3 := by
    have hh : |s.im|≤|t|+|s.im-t| := by
      calc
        _ = |t+(s.im-t)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    linarith
  have hlower : Real.exp B≤|s.im| := by
    have hh : |t|≤|s.im|+|s.im-t| := by
      calc
        _ = |s.im+(t-s.im)| := by congr 1; ring
        _ ≤ |s.im|+|t-s.im| := abs_add_le _ _
        _ = _ := by rw [abs_sub_comm]
    linarith
  have him0 : 0 < |s.im| := (Real.exp_pos B).trans_le hlower
  let L := Real.log |s.im|
  have hL : B≤ L := by
    have hh := Real.log_le_log (Real.exp_pos B) hlower
    simpa only [Real.log_exp,L] using hh
  have hL100 : 100≤ L := hB100.trans hL
  have hL0 : 0 < L := by linarith
  have hLM : L≤ M := Real.log_le_log him0 hupper
  have hδ : max (1-s.re) 0≤4*L^(-(2/3:ℝ)) := by
    have hδR : max (1-s.re) 0≤ mrtVKRadius t := max_le_iff.mpr ⟨by linarith,hR0.le⟩
    have hRL : mrtVKRadius t≤ L^(-(2/3:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hL0 hLM (by norm_num)
    have hn : 0≤ L^(-(2/3:ℝ)) := Real.rpow_nonneg hL0.le _
    linarith
  have hg := hgrowth L hL100 a ha s (by linarith) (by linarith)
    (Real.exp_log him0).symm hδ
  apply hg.trans
  have hsize : L+1≤2*M := by linarith
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith : 0≤ L+1) hsize 7) (by linarith : 0≤ A)
  have hcoef : 128*A≤ M := hBA.trans hM
  have hm7 : 0≤ M^7 := pow_nonneg hM0.le _
  have hh := mul_le_mul_of_nonneg_right hcoef hm7
  change A*(L+1)^7≤ M^(8:ℝ)
  rw [Real.rpow_ofNat,show M^8=M^7*M from pow_succ M 7]
  norm_num only [mul_pow] at hp
  nlinarith

end TwoPointCorrelations

end OAI
