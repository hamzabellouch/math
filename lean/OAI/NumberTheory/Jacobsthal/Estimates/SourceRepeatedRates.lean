import OAI.NumberTheory.Jacobsthal.Probability.RepeatedPairProbability

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedBudgetRate
open _root_.Filter RepeatedStepRowBound ExponentialMesh
open scoped Topology

theorem search_repeat_budget_small {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop,∀ S xi : ℝ,0 ≤ S → S ≤ (Real.log w)^3 → 0 ≤ xi → xi ≤ 1 →
      ∀ N : ℕ,(N:ℝ) ≤ A*(Real.log w)^3 →
      (N:ℝ)*repeatBudget S (w^((1/4:ℝ))) xi w (mesh κ w) ≤ eps := by
  have hC := repeatDensityConstant_pos
  have ht : Tendsto (fun w : ℝ => (Real.log w)^12/w^((1/4:ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (12:ℝ) (s := (1/4:ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hsum : Tendsto (fun w : ℝ => 9*A*repeatDensityConstant*((Real.log w)^12/w^((1/4:ℝ)))+
      18*A*repeatDensityConstant*(Real.log w)^9*Real.exp (-κ*Real.sqrt (Real.log w))) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using
      (ht.const_mul (9*A*repeatDensityConstant)).add (log_power_exp_tendsto (18*A*repeatDensityConstant) 9 hκ)
  filter_upwards [hsum.eventually (eventually_le_nhds heps),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with w hbound hlog hw
  intro S xi hS0 hS hxi0 hxi1 N hN
  have hm : 0 ≤ mesh κ w := (mesh_pos κ w).le
  have hX : 0 < w^((1/4:ℝ)) := Real.rpow_pos_of_pos (zero_lt_one.trans hw) _
  have hL3 : 1 ≤ (Real.log w)^3 := one_le_pow₀ hlog
  have hSplus : S+2 ≤ 3*(Real.log w)^3 := by linarith
  have hsrc : xi/Real.log w ≤ 1 := (div_le_self hxi0 hlog).trans hxi1
  have hsrc0 : 0 ≤ xi/Real.log w := div_nonneg hxi0 (Real.log_pos hw).le
  have hcoef : (N:ℝ)*repeatDensityConstant*(S+2)^2 ≤ 9*A*repeatDensityConstant*(Real.log w)^9 := by
    calc
      _ ≤ (A*(Real.log w)^3)*repeatDensityConstant*(3*(Real.log w)^3)^2 := by gcongr
      _ = _ := by ring
  have hnum : S*(xi/Real.log w) ≤ (Real.log w)^3 := by nlinarith [mul_le_mul_of_nonneg_left hsrc hS0]
  have hwidth : S*(xi/Real.log w)/w^((1/4:ℝ))+2*mesh κ w ≤
      (Real.log w)^3/w^((1/4:ℝ))+2*Real.exp (-κ*Real.sqrt (Real.log w)) :=
    add_le_add (div_le_div_of_nonneg_right hnum hX.le) (mul_le_mul_of_nonneg_left (mesh_upper κ w) (by norm_num))
  calc
    _ = ((N:ℝ)*repeatDensityConstant*(S+2)^2)*(S*(xi/Real.log w)/w^((1/4:ℝ))+2*mesh κ w) := by
      unfold repeatBudget
      ring
    _ ≤ (9*A*repeatDensityConstant*(Real.log w)^9)*
        ((Real.log w)^3/w^((1/4:ℝ))+2*Real.exp (-κ*Real.sqrt (Real.log w))) :=
      mul_le_mul hcoef hwidth (show 0 ≤ S*(xi/Real.log w)/w^((1/4:ℝ))+2*mesh κ w by positivity)
        (show 0 ≤ 9*A*repeatDensityConstant*(Real.log w)^9 by positivity)
    _ = 9*A*repeatDensityConstant*((Real.log w)^12/w^((1/4:ℝ)))+
        18*A*repeatDensityConstant*(Real.log w)^9*Real.exp (-κ*Real.sqrt (Real.log w)) := by ring
    _ ≤ _ := hbound

theorem compact_repeat_budget_small {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 < κ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop,∀ xi : ℝ,0 ≤ xi → xi ≤ 1 →
      repeatBudget L 1 xi w (mesh κ w)*(L+1) ≤ eps := by
  have hC := repeatDensityConstant_pos
  have ht : Tendsto (fun w : ℝ => 1/Real.log w) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsum : Tendsto (fun w : ℝ => repeatDensityConstant*(L+2)^2*(L+1)*
      (L*(1/Real.log w)+2*Real.exp (-κ*Real.sqrt (Real.log w)))) atTop (𝓝 0) := by
    have hh := ((ht.const_mul L).add (log_power_exp_tendsto 2 0 hκ)).const_mul (repeatDensityConstant*(L+2)^2*(L+1))
    simpa only [pow_zero,mul_one,mul_zero,add_zero] using hh
  filter_upwards [hsum.eventually (eventually_le_nhds heps),eventually_gt_atTop (1:ℝ)] with w hw hw1
  intro xi hxi0 hxi1
  have hlog := Real.log_pos hw1
  have hxi : xi/Real.log w ≤ 1/Real.log w := div_le_div_of_nonneg_right hxi1 hlog.le
  have hwidth := add_le_add (mul_le_mul_of_nonneg_left hxi hL) (mul_le_mul_of_nonneg_left (mesh_upper κ w) (by norm_num : (0:ℝ)≤2))
  calc
    _ = (repeatDensityConstant*(L+2)^2*(L+1))*(L*(xi/Real.log w)+2*mesh κ w) := by unfold repeatBudget; ring
    _ ≤ (repeatDensityConstant*(L+2)^2*(L+1))*(L*(1/Real.log w)+2*Real.exp (-κ*Real.sqrt (Real.log w))) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ ≤ _ := hw
end NumberTheoryLean.RepeatedBudgetRate



namespace NumberTheoryLean.SourceRepeatedRates
open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualCoupledHistories FlaggedSourceStart SourceSelectedCompactOccupation SourceCouplingRate
open RepeatedStepRowBound RepeatedPairEvents RepeatedPairProbability RepeatedBudgetRate
open FinitePairOccurrence ExponentialMesh LowStateHorizon PersistentFailureFlag
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

theorem source_repeated_pair_probabilities : ∃ κ₀ : ℝ,0 < κ₀ ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ D L eps : ℝ,0 < D → 0 ≤ L → 0 < eps →
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∃ hw : 1 < w,
      ∀ top : ℝ,∀ htop : w < top,∀ ell B : ℝ,
      ∀ start : Node,∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ D*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B → w^start.cutoff=top →
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      (fullSourceLaw w ell S start hs (mesh κ w) N
        (pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) (w^((1/4:ℝ))) S Set.univ) N) ≤ ENNReal.ofReal eps) ∧
      (fullSourceLaw w ell S start hs (mesh κ w) N
        (pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) 1 L (compactParentGate L)) N) ≤ ENNReal.ofReal eps) := by
  obtain ⟨κ₀,hκ₀,hCouple⟩ := source_coupling_rate
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle D L eps hD hL heps
  obtain ⟨WC,hWC,hC⟩ := hCouple κ hκ hκle D hD
  have hA : 0 ≤ 5*D^3 := by positivity
  have hEvents := (search_repeat_budget_small hA hκ (show 0 < eps/2 by positivity)).and
    ((compact_repeat_budget_small hL hκ (show 0 < eps/2 by positivity)).and
      (((log_power_exp_tendsto 1 0 (show 0 < κ/2 by positivity)).eventually
        (eventually_le_nhds (show 0 < eps/2 by positivity))).and
        (Real.tendsto_log_atTop.eventually_ge_atTop (D^2))))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hEvents
  refine ⟨max WC (max normalizationThreshold W),hWC.trans_le (le_max_left _ _),?_⟩
  intro w hw₀
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw₀
  have hw : 1 < w := normalizationThreshold_gt_one.trans_le hnorm
  refine ⟨hw,?_⟩
  intro top htop ell B start hs hell hB hlogB hcomp hr hs23 hc hsize hcap xi hxi hxi1
  dsimp only
  have hwC : WC ≤ w := (le_max_left _ _).trans hw₀
  have hwe := hW w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw₀)
  have hscale := UniformBudgetRate.source_scale_bound hwe.2.2.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hsS : start.ratio ≤ (Real.log B)^2 := by nlinarith
  let N := sourceHorizon ((Real.log B)^2) B
  have hf := (hC w hwC ell B start hs hell hB hlogB hcomp hr hs23 hc hsize).1 N le_rfl |>.1
  have hfail : Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤ eps/2 := by
    simpa only [pow_zero,mul_one,one_mul] using hwe.2.2.1
  have hf' : FlaggedSourceStart.sourceLaw hnorm hell hS0 hscale.1 hr hs hsS (mesh κ w) N failed ≤ ENNReal.ofReal (eps/2) :=
    hf.trans (ENNReal.ofReal_le_ofReal hfail)
  have hm := mesh_pos κ w
  have hmesh := mesh_le_one hκ.le w
  have hSearch := hwe.1 ((Real.log B)^2) xi hS0 hscale.1 hxi.le hxi1 N hscale.2
  have hCompact := hwe.2.1 xi hxi.le hxi1
  have hsum : ENNReal.ofReal (eps/2)+ENNReal.ofReal (eps/2)=ENNReal.ofReal eps := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ eps/2) (by positivity : 0 ≤ eps/2)]
    congr 1
    ring
  constructor
  · have hraw := raw_repeat_probability_le_good hnorm hell hS0 hscale.1 hr hs hsS
      (label (zero_lt_one.trans hw) htop hxi) (w^((1/4:ℝ))) ((Real.log B)^2) Set.univ hm N
    have hgood := good_repeat_probability_uniform hnorm hell hS0 hscale.1 hr hs hsS hw htop hxi hS0
      (Real.rpow_pos_of_pos (zero_lt_one.trans hw) (1/4:ℝ)) hm hmesh hcap N Set.univ
    exact hraw.trans ((add_le_add hf' (hgood.trans (ENNReal.ofReal_le_ofReal hSearch))).trans_eq hsum)
  · have hraw := raw_repeat_probability_compact hnorm hell hS0 hscale.1 hr hs hsS hw htop hxi hL hm hmesh hcap N
    exact hraw.trans ((add_le_add hf' (ENNReal.ofReal_le_ofReal hCompact)).trans_eq hsum)
end NumberTheoryLean.SourceRepeatedRates


end Erdos970

end OAI
