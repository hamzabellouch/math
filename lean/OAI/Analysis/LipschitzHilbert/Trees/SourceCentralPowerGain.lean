import OAI.Analysis.LipschitzHilbert.Trees.SourceParameters
import OAI.Analysis.LipschitzHilbert.Phase.ImprovedFourthMoment

namespace OAI

/-! The numerical gain in manuscript §11, with the actual rounded number
of shifts. A polynomial separated-count bound gives the required phase
lower bound, and the central exponent absorbs every fixed power of L. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert
open PhaseCombinatorics

 theorem eventually_phaseParameter_lower (d : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℝ, 1 ≤ D → D ≤ L^d →
      (phaseConstant/(d+1))/Real.log L ≤ phaseParameter D := by
  filter_upwards [eventually_ge_atTop (2:ℝ)] with L hL
  intro D hD hDupper
  have hL0 : 0 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogD : 0 < Real.log (2*D) := Real.log_pos (by linarith)
  have hden : Real.log (2*D) ≤ (d+1)*Real.log L := by
    calc
      _ = Real.log 2+Real.log D := Real.log_mul (by norm_num) (by linarith)
      _ ≤ Real.log L+Real.log (L^d) := add_le_add
        (Real.log_le_log (by norm_num) hL)
        (Real.log_le_log (by linarith) hDupper)
      _ = (d+1)*Real.log L := by rw [Real.log_rpow hL0]; ring
  have h := div_le_div_of_nonneg_left phaseConstant_pos.le hlogD hden
  change _ ≤ phaseConstant/Real.log (2*D)
  calc
    _ = phaseConstant/((d+1)*Real.log L) := by rw [div_div]
    _ ≤ _ := h

 theorem central_exponent_gap {L c alpha K : ℝ}
    (hL : 1 < L) (hc : 0 < c) (hlog : 4/c ≤ Real.log L)
    (halpha : c/Real.log L ≤ alpha-2) (halpha3 : alpha ≤ 3)
    (hK : Real.log L^2 ≤ K) :
    c/(2*Real.sqrt L*Real.log L) ≤
      (alpha-2-(alpha-1)/K)/Real.sqrt L := by
  have ht : 0 < Real.log L := Real.log_pos hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hK0 : 0 < K := (sq_pos_of_pos ht).trans_le hK
  have hsmall : 2/K ≤ c/(2*Real.log L) := by
    calc
      _ ≤ 2/(Real.log L^2) :=
        div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ht) hK
      _ ≤ c/(2*Real.log L) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos ht) (by positivity)).mpr
        have hcLog : 4 ≤ c*Real.log L := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hlog
        nlinarith [mul_le_mul_of_nonneg_right hcLog ht.le]
  have hterm : (alpha-1)/K ≤ 2/K :=
    div_le_div_of_nonneg_right (by linarith) hK0.le
  have hgap : c/(2*Real.log L) ≤ alpha-2-(alpha-1)/K := by
    have heq : c/Real.log L = 2*(c/(2*Real.log L)) := by ring
    linarith
  calc
    _ = (c/(2*Real.log L))/Real.sqrt L := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hgap hs.le

 theorem eventually_source_central_power_gain (c C Q : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ alpha K N : ℝ,
      c/Real.log L ≤ alpha-2 → alpha ≤ 3 →
      Real.log L^2 ≤ K → 0 < N → L/2 ≤ Real.log N →
      L^C*N^(1+(2-alpha)/Real.sqrt L+((alpha-1)/Real.sqrt L)/K) ≤ L^(-Q)*N := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (by norm_num : (0:ℝ) < 1/2)).bound
      (show 0 < c/(4*(C+Q+1)) by positivity)
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4/c),hsmall]
    with L hL hlog hsmallL
  intro alpha K N halpha halpha3 hK hN hmass
  have hL0 : 0 < L := by linarith
  have ht : 0 < Real.log L := Real.log_pos hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hK0 : 0 < K := (sq_pos_of_pos ht).trans_le hK
  rw [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL0.le _),
    ← Real.sqrt_eq_rpow] at hsmallL
  let delta := (alpha-2-(alpha-1)/K)/Real.sqrt L
  have hdelta : c/(2*Real.sqrt L*Real.log L) ≤ delta :=
    central_exponent_gap hL hc hlog halpha halpha3 hK
  have hdelta0 : 0 ≤ delta := (by positivity : 0 ≤ c/(2*Real.sqrt L*Real.log L)).trans hdelta
  have hproduct : c*Real.sqrt L/(4*Real.log L) ≤ delta*Real.log N := by
    calc
      _ = (c/(2*Real.sqrt L*Real.log L))*(L/2) := by
        field_simp
        nlinarith [Real.sq_sqrt hL0.le]
      _ ≤ delta*Real.log N := mul_le_mul hdelta hmass (by positivity) hdelta0
  have hcost : (C+Q)*Real.log L ≤ c*Real.sqrt L/(4*Real.log L) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*Real.log L)).mpr
    have hb := (le_div_iff₀ (show 0 < 4*(C+Q+1) by positivity)).mp
      (show (Real.log L)^2 ≤ (c*Real.sqrt L)/(4*(C+Q+1)) by
        simpa only [div_mul_eq_mul_div] using hsmallL)
    nlinarith [sq_nonneg (Real.log L)]
  have hexponent : 1+(2-alpha)/Real.sqrt L+((alpha-1)/Real.sqrt L)/K = 1-delta := by
    dsimp only [delta]
    field_simp
    ring
  rw [hexponent,Real.rpow_def_of_pos hL0,Real.rpow_def_of_pos hN,
    ← Real.exp_add,Real.rpow_def_of_pos hL0,← Real.exp_log hN,← Real.exp_add]
  rw [Real.log_exp]
  apply Real.exp_le_exp.mpr
  nlinarith [hcost.trans hproduct]

/-- The manuscript's rounded shift count satisfies the numerical hypothesis
without replacing it by an unrounded real parameter. -/
theorem eventually_source_central_power_gain_actual (d C Q : ℝ)
    (hd : 0 ≤ d) (hC : 0 ≤ C) (hQ : 0 ≤ Q) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ,
      1 ≤ D → D ≤ L^d → 0 < N → L/2 ≤ Real.log N →
      L^C*N^(1-phaseParameter D/Real.sqrt L+
        ((1+phaseParameter D)/Real.sqrt L)/(SourceParameters.blockCount L:ℝ)) ≤
        L^(-Q)*N := by
  have hc : 0 < phaseConstant/(d+1) := div_pos phaseConstant_pos (by linarith)
  filter_upwards [eventually_phaseParameter_lower d,
    eventually_source_central_power_gain (phaseConstant/(d+1)) C Q hc hC hQ]
    with L hphase hgain
  intro D N hD hDbound hN hmass
  have hrange := phaseParameter_range hD
  have h := hgain (2+phaseParameter D) (SourceParameters.blockCount L:ℝ) N
    (by simpa only [add_sub_cancel_left] using hphase D hD hDbound)
    (by change 2+phaseConstant/Real.log (2*D) ≤ 3; linarith)
    (Nat.le_ceil _) hN hmass
  convert h using 2
  congr 1
  ring

end LipschitzHilbert

end

end OAI
