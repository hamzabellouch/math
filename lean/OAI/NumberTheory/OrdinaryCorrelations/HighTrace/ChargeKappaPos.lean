import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Epsilon

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical Filter

lemma charge_kappa_pos : 0 < kappa := by norm_num [kappa,eta,epsilon]
lemma betaC_correction_lt_one : betaC * (Real.exp kappa - 1) < 1 := by
  have he := Real.exp_le_exp.mpr (show kappa ≤ 2*kappa by linarith only [charge_kappa_pos])
  have hp : 0 < 1 + A := by unfold A; positivity
  rw [betaC,inv_mul_eq_div]
  apply (div_lt_one hp).mpr
  unfold A
  linarith

lemma coreMass_tendsto : Tendsto SourcePrimeBands.coreMass atTop atTop := by
  have h := SourcePrimeBands.source_prime_bands.1.pos_mul_atTop
    (by norm_num [SourcePrimeBands.eta,SourcePrimeBands.epsilon]) Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hB))

lemma sqrt_coreMass_div_log :
    Tendsto (fun B : ℝ => Real.sqrt (SourcePrimeBands.coreMass B) / Real.log B)
      atTop (nhds 0) := by
  have h := SourcePrimeBands.source_prime_bands.1.mul
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp coreMass_tendsto))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [coreMass_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with B hv hB
  have hl : Real.log B ≠ 0 := ne_of_gt (Real.log_pos hB)
  have hs : Real.sqrt (SourcePrimeBands.coreMass B) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hs2 := Real.sq_sqrt hv.le
  dsimp only [Function.comp_def]
  field_simp [hl,hs]
  nlinarith only [hs2]

theorem source_charge_lower (T : ℝ) :
    ∀ᶠ B : ℝ in atTop,
      100 * Real.log B < kappa * (SourcePrimeBands.coreMass B -
        T * Real.sqrt (SourcePrimeBands.coreMass B)) ∧
      100 * Real.log B < kappa * (SourcePrimeBands.coreMass B -
        T * Real.sqrt (SourcePrimeBands.coreMass B)) -
          SourcePrimeBands.coreMass B * betaC * (Real.exp kappa - 1) := by
  let v := SourcePrimeBands.coreMass
  let c := betaC * (Real.exp kappa - 1)
  have hη : 0 < SourcePrimeBands.eta := by norm_num [SourcePrimeBands.eta,SourcePrimeBands.epsilon]
  have hc := betaC_correction_lt_one
  have hlim := (SourcePrimeBands.source_prime_bands.1.sub
    (sqrt_coreMass_div_log.const_mul T)).const_mul kappa
  have hlim2 := hlim.sub (SourcePrimeBands.source_prime_bands.1.mul_const c)
  have hconst : 100 < kappa * (SourcePrimeBands.eta - T*0) - SourcePrimeBands.eta*c := by
    have hκη : kappa * SourcePrimeBands.eta = 400 := by
      norm_num [kappa,eta,epsilon,SourcePrimeBands.eta,SourcePrimeBands.epsilon]
    have hη1 : SourcePrimeBands.eta < 1 := by norm_num [SourcePrimeBands.eta,SourcePrimeBands.epsilon]
    have hx := mul_lt_mul_of_pos_left hc hη
    dsimp [c] at *
    nlinarith
  have hconst1 : 100 < kappa * (SourcePrimeBands.eta - T*0) := by
    norm_num [kappa,eta,epsilon,SourcePrimeBands.eta,SourcePrimeBands.epsilon]
  have he1 := hlim.eventually (eventually_gt_nhds hconst1)
  have he2 := hlim2.eventually (eventually_gt_nhds hconst)
  filter_upwards [he1,he2,eventually_gt_atTop (1 : ℝ)] with B hb1 hb2 hB
  have hl : 0 < Real.log B := Real.log_pos hB
  constructor
  · have hm := (lt_div_iff₀ hl).mp (show 100 <
      (kappa * (v B - T * Real.sqrt (v B))) / Real.log B by
        calc
          100 < kappa * (v B / Real.log B - T * (Real.sqrt (v B) / Real.log B)) := hb1
          _ = _ := by ring)
    exact hm
  · have hm := (lt_div_iff₀ hl).mp (show 100 <
      (kappa * (v B - T * Real.sqrt (v B)) - v B * c) / Real.log B by
        calc
          100 < kappa * (v B / Real.log B - T * (Real.sqrt (v B) / Real.log B)) -
            v B / Real.log B * c := hb2
          _ = _ := by ring)
    simpa only [v,c,mul_assoc] using hm

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
