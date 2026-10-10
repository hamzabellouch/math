import OAI.Analysis.LipschitzHilbert.Trees.SourceNormalizedDecay
import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseParameters

namespace OAI

/-! Numerical parameters for the source prediction comparison.
All thresholds are uniform in the top family, phase dimension and mass. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

theorem eventually_source_mass_error_small (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ Kw : ℝ, 1 ≤ Kw →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      Real.exp δ*δ ≤ 1/8 := by
  have hm := eventually_source_mass_rescaling_error D hD
  have hs := (Real.tendsto_sqrt_atTop.comp source_step_tendsto_atTop).eventually_ge_atTop
    (80*D*Real.exp 1)
  filter_upwards [hm,hs] with L hm hs
  intro Kw hKw
  dsimp only
  have hb := hm 1 0 Kw (by norm_num) (by norm_num) (by norm_num) hKw
  norm_num at hb
  apply hb.trans
  have hroot : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  apply (div_le_iff₀ hroot).mpr
  change 80*D*Real.exp 1 ≤ Real.sqrt (SourceParameters.step L) at hs
  nlinarith

/-- Both relative errors used by the actual path comparison are smaller
than the chosen prediction error, uniformly in the block length. -/
theorem eventually_source_path_errors_small (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw Z : ℝ) (steps : ℕ),
      1 ≤ Kw → 0 ≤ Z → Z ≤ 2*L^2 → (steps:ℝ) ≤ L^2 →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let E := (steps:ℝ)*Z*(2*δ)
      let ε := SourceParameters.step L^(-(1/8:ℝ))
      (Real.exp δ*δ ≤ 1/8 ∧ Real.exp δ*δ ≤ ε) ∧
        Real.exp E*E ≤ ε := by
  have hm := eventually_source_mass_rescaling_error D hD
  have ht := eventually_source_transition_error D hD
  have hpm := eventually_source_polynomial_motion (10*D*Real.exp 1) 0
  have hpt := eventually_source_polynomial_motion (20*D*Real.exp 1) 4
  filter_upwards [hm,ht,hpm,hpt,eventually_source_mass_error_small D hD]
    with L hm ht hpm hpt hsmall
  intro Kw Z steps hKw hZ0 hZ hsteps
  dsimp only
  have hb := hm 1 0 Kw (by norm_num) (by norm_num) (by norm_num) hKw
  norm_num at hb hpm
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hpow : SourceParameters.step L^(-(1/4:ℝ)) ≤
      SourceParameters.step L^(-(1/8:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hG (by norm_num)
  refine ⟨⟨hsmall Kw hKw,hb.trans (hpm.trans hpow)⟩,?_⟩
  have hphase := ht steps Z Kw hsteps hZ0 hZ hKw
  rw [Real.rpow_ofNat] at hpt
  exact hphase.trans (hpt.trans hpow)

/-- A single small positive power controls the path comparison,
the convex blend and the mesh/mixture error. -/
theorem prediction_budget_of_subpower {G V F : ℝ}
    (hG : 1 ≤ G) (hV0 : 0 ≤ V) (hV : V ≤ G^(1/128:ℝ)) (hF : 0 ≤ F)
    (hsmall : 96 ≤ G^(7/128:ℝ)) (hcost : 27650+F ≤ G^(3/128:ℝ)) :
    Real.exp (48*V*G^(-(1/8:ℝ))) ≤ 2 ∧
      96*V*G^(-(1/8:ℝ)) ≤ G^(-(1/16:ℝ)) ∧
      27648*V^2*G^(-(1/8:ℝ))+(2+F)*V*G^(-(1/16:ℝ)) ≤ G^(-(1/32:ℝ)) := by
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  have hvε : V*G^(-(1/8:ℝ)) ≤ G^(-(15/128:ℝ)) := by
    calc
      _ ≤ G^(1/128:ℝ)*G^(-(1/8:ℝ)) :=
        mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hG0.le _)
      _ = _ := by rw [← Real.rpow_add hG0]; norm_num
  have habsorb : 96*V*G^(-(1/8:ℝ)) ≤ G^(-(1/16:ℝ)) := by
    calc
      _ = 96*(V*G^(-(1/8:ℝ))) := by ring
      _ ≤ 96*G^(-(15/128:ℝ)) := mul_le_mul_of_nonneg_left hvε (by norm_num)
      _ ≤ G^(7/128:ℝ)*G^(-(15/128:ℝ)) :=
        mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hG0.le _)
      _ = _ := by rw [← Real.rpow_add hG0]; norm_num
  have htheta : G^(-(1/16:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  have hlog : (1/2:ℝ) ≤ Real.log 2 := by
    have hb := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hb
    exact hb
  have hexp : Real.exp (48*V*G^(-(1/8:ℝ))) ≤ 2 := by
    have hx : 48*V*G^(-(1/8:ℝ)) ≤ Real.log 2 := by
      have hh := habsorb.trans htheta
      linarith
    exact (Real.exp_le_exp.mpr hx).trans_eq (Real.exp_log (by norm_num))
  have hsq : V^2 ≤ G^(1/128:ℝ)*G^(1/128:ℝ) := by
    have hh := mul_le_mul hV hV hV0 (Real.rpow_nonneg hG0.le (1/128:ℝ))
    simpa only [pow_two] using hh
  have hfirst : V^2*G^(-(1/8:ℝ)) ≤ G^(-(7/128:ℝ)) := by
    calc
      _ ≤ (G^(1/128:ℝ)*G^(1/128:ℝ))*G^(-(1/8:ℝ)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hG0.le _)
      _ = G^(-(14/128:ℝ)) := by rw [← Real.rpow_add hG0,← Real.rpow_add hG0]; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hG (by norm_num)
  have hsecond : V*G^(-(1/16:ℝ)) ≤ G^(-(7/128:ℝ)) := by
    calc
      _ ≤ G^(1/128:ℝ)*G^(-(1/16:ℝ)) :=
        mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hG0.le _)
      _ = _ := by rw [← Real.rpow_add hG0]; norm_num
  refine ⟨hexp,habsorb,?_⟩
  calc
    _ = 27648*(V^2*G^(-(1/8:ℝ)))+(2+F)*(V*G^(-(1/16:ℝ))) := by ring
    _ ≤ 27648*G^(-(7/128:ℝ))+(2+F)*G^(-(7/128:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
        (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ = (27650+F)*G^(-(7/128:ℝ)) := by ring
    _ ≤ G^(3/128:ℝ)*G^(-(7/128:ℝ)) :=
      mul_le_mul_of_nonneg_right hcost (Real.rpow_nonneg hG0.le _)
    _ = _ := by rw [← Real.rpow_add hG0]; norm_num

/-- The source values `p=sqrt L`, `epsilon=G^(-1/8)` and
`theta=G^(-1/16)` meet the complete dominant-comparison budget. -/
theorem eventually_source_prediction_parameters (C F : ℝ) (_hC : 0 ≤ C) (hF : 0 ≤ F) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ,
      1 ≤ D → 0 < N → Real.log N ≤ 2*L →
      let p := Real.sqrt L
      let K := L^C*(1+N^phaseMu D p)
      let G := SourceParameters.step L
      let ε := G^(-(1/8:ℝ))
      let θ := G^(-(1/16:ℝ))
      Real.exp (24*p*ε*(2*K)) ≤ 2 ∧
      2*24*p*ε*(2*K) ≤ θ ∧
      (12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))+F*G^(-(1/16:ℝ))*p*K ≤
        G^(-(1/32:ℝ)) := by
  have hsub := eventually_source_subpower_amplitude (C+1/2) (1/128) (by norm_num)
  have hsmall := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<7/128)).comp
    source_step_tendsto_atTop).eventually_ge_atTop 96
  have hcost := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/128)).comp
    source_step_tendsto_atTop).eventually_ge_atTop (27650+F)
  filter_upwards [hsub,hsmall,hcost,eventually_ge_atTop (1:ℝ)] with L hsub hsmall hcost hL
  intro D N hD hN hlogN
  dsimp only
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let K := L^C*(1+N^phaseMu D (Real.sqrt L))
  let V := Real.sqrt L*K
  have hV0 : 0 ≤ V := by dsimp [V,K]; positivity
  have hV : V ≤ SourceParameters.step L^(1/128:ℝ) := by
    calc
      _ = L^(C+1/2)*(1+N^phaseMu D (Real.sqrt L)) := by
        dsimp [V,K]
        rw [Real.rpow_add hL0,← Real.sqrt_eq_rpow]
        ring
      _ ≤ _ := hsub D N hD hN hlogN
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  obtain ⟨hexp,habsorb,hbudget⟩ := prediction_budget_of_subpower hG hV0 hV hF hsmall hcost
  refine ⟨?_,?_,?_⟩
  · convert hexp using 1
    congr 1
    dsimp [V,K]
    ring
  · convert habsorb using 1
    dsimp [V,K]
    ring
  · convert hbudget using 1
    dsimp [V,K]
    ring

/-- The balanced branch fits inside the same error budget as the
dominant branch, so the final marked-cell exponent is common to both. -/
theorem balanced_prediction_cost_le_dominant {p K ε θ : ℝ}
    (hp : 1 ≤ p) (hK : 1 ≤ K) (hε : 0 ≤ ε) :
    6*p*ε*K+2*θ*(p*K) ≤
      12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)) := by
  have hx : 1 ≤ p*K := one_le_mul_of_one_le_of_one_le hp hK
  have hbase : 6*(p*K) ≤ 27648*(p*K)^2 := by nlinarith
  calc
    _ = 6*(p*K)*ε+θ*(p*(2*K)) := by ring
    _ ≤ 27648*(p*K)^2*ε+θ*(p*(2*K)) :=
      add_le_add (mul_le_mul_of_nonneg_right hbase hε) le_rfl
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
