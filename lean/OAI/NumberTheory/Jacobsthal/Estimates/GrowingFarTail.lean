import OAI.NumberTheory.Jacobsthal.Paths.ActualFlaggedCompact

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.InverseWeightGrowth
open _root_.Filter
open scoped Topology

theorem quartic_log_scale_absorption {C kappa : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) :
    ∀ᶠ w : ℝ in atTop,
      Real.exp (C*(1+(Real.log w)^((1 : ℝ)/10))^4) *
        Real.exp (-kappa*Real.sqrt (Real.log w)) ≤
          Real.exp (-(kappa/2)*Real.sqrt (Real.log w)) := by
  have hk : Tendsto (fun w : ℝ => (Real.log w)^((1 : ℝ)/10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hk.eventually (eventually_ge_atTop (max 1 (32*C/kappa)))] with w hlog hcut
  let k : ℝ := (Real.log w)^((1 : ℝ)/10)
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hcut
  have hk0 : 0 ≤ k := by linarith
  have hcoef : 16*C ≤ (kappa/2)*k := by
    have h := (div_le_iff₀ hkappa).mp ((le_max_right _ _).trans hcut)
    nlinarith
  have hsqrt : Real.sqrt (Real.log w) = k^5 := by
    rw [Real.sqrt_eq_rpow]
    dsimp [k]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ Real.log w)]
    norm_num
  have hmajor : C*(1+k)^4 ≤ (kappa/2)*Real.sqrt (Real.log w) := by
    calc
      _ ≤ C*(2*k)^4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by linarith : 1+k ≤ 2*k) 4) hC
      _ = (16*C)*k^4 := by ring
      _ ≤ ((kappa/2)*k)*k^4 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hk0 _)
      _ = _ := by rw [hsqrt]; ring
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change C*(1+k)^4 + -kappa*Real.sqrt (Real.log w) ≤ _
  nlinarith

end NumberTheoryLean.InverseWeightGrowth

end

section

namespace NumberTheoryLean.ModerateFailedReward

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeCompactVisits PrimeCompactWeights ActualProcessCoupling
open FlaggedOccupationBound ActualFlaggedCompact PersistentFailureFlag
open DerivativeWeights ExponentialMeshTail InverseWeightGrowth

variable {w ell S : ℝ} {start : Node}

noncomputable def moderateReward (c K : ℝ) : ChainState w ell S start → ℝ≥0∞
  | none => 0
  | some h => ENNReal.ofReal (h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio)*
      ENNReal.ofReal (visit K (some h))

theorem exponential_quartic_absorbs_linear {C K : ℝ} (hK : 0 ≤ K) :
    Real.exp (C*(1+K)^4)*(K+1) ≤ Real.exp ((C+1)*(1+K)^4) := by
  have hp : K ≤ (1+K)^4 := by nlinarith [pow_nonneg hK 3,pow_nonneg hK 4]
  have hlin : K+1 ≤ Real.exp ((1+K)^4) := (Real.add_one_le_exp K).trans (Real.exp_le_exp.mpr hp)
  calc
    _ ≤ Real.exp (C*(1+K)^4)*Real.exp ((1+K)^4) := mul_le_mul_of_nonneg_left hlin (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem moderate_reward_envelope : ∃ A C : ℝ,0 < A ∧ 0 < C ∧
    ∀ w ell S : ℝ,∀ start : Node,1 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      Consistent start → ell ≤ start.cutoff → ∀ c : ℝ,0 < c → ∀ K : ℝ,
      ∀ z : ChainState w ell S start,
        moderateReward c K z ≤ ENNReal.ofReal ((8*A/c^2)*Real.exp (C*(1+K)^4))*ENNReal.ofReal (visit K z) := by
  obtain ⟨A,C,hA,hC,hbound⟩ := inverse_weight_below_cutoff
  refine ⟨A,C,hA,hC,?_⟩
  intro w ell S start hell hr hs hcons hcut c hc K z
  cases z with
  | none => simp [moderateReward,visit]
  | some h =>
    by_cases hh : h.node.gap ≤ K
    · have hg : 0 < h.node.gap := terminal_gap_positive (by linarith) hr hs h.admissible
      have hv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
      have htK := (history_ratio_le_gap hell hr hs hcons hcut h).trans hh
      have hinv := hbound K h.node.side h.node.ratio hv htK
      have hraw : h.node.gap^2*Real.exp (-c*h.node.gap) ≤ 8/c^2 := by
        refine (quadratic_exp_majorant hc hg.le).trans ?_
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by nlinarith : -c*h.node.gap/2 ≤ 0)) (show 0 ≤ 8/c^2 by positivity)
      have hφ := weight_pos hv
      have hreal : h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio ≤
          (8*A/c^2)*Real.exp (C*(1+K)^4) := by
        calc
          _ = (h.node.gap^2*Real.exp (-c*h.node.gap))*(1/weight h.node.side h.node.ratio) := by ring
          _ ≤ (8/c^2)*(A*Real.exp (C*(1+K)^4)) := mul_le_mul hraw hinv (by positivity) (by positivity)
          _ = _ := by ring
      simp only [moderateReward,visit,ite_eq_left hh,ENNReal.ofReal_one,mul_one]
      exact ENNReal.ofReal_le_ofReal hreal
    · simp [moderateReward,visit,hh]

theorem actual_moderate_failed_sum : ∃ A C : ℝ,0 < A ∧ 0 < C ∧
    ∀ w ell S : ℝ,∀ start : Node,∀ _hw : normalizationThreshold ≤ w,
      ∀ _hell : 1 ≤ ell,∀ _hS0 : 0 ≤ S,∀ _hS : S ≤ (Real.log w)^3,
      ∀ _hr : 0 < start.gap,∀ hs : Valid start.side start.ratio,∀ _hsS : start.ratio ≤ S,
      Consistent start → ell ≤ start.cutoff → ∀ c : ℝ,0 < c → ∀ K : ℝ,0 ≤ K →
      ∀ mesh : ℝ,∀ N : ℕ,
        (∑ n ∈ range N,∫⁻ z,selected (fun q : JointState w ell S start => moderateReward c K q.1) z
          ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
          ENNReal.ofReal ((8*A/c^2)*Real.exp (C*(1+K)^4))*
            CouplingData.sourceLaw w ell S start hs mesh N failed := by
  obtain ⟨A,C,hA,hC,hbound⟩ := moderate_reward_envelope
  refine ⟨A,C+1,hA,by linarith,?_⟩
  intro w ell S start hw hell hS0 hS hr hs hsS hcons hcut c hc K hK mesh N
  let D := (8*A/c^2)*Real.exp (C*(1+K)^4)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint : ∀ z : FlagState (JointState w ell S start),
      selected (fun q => moderateReward c K q.1) z ≤ ENNReal.ofReal D*selected (compactVisit K) z := by
    rintro ⟨q,b⟩
    cases b with
    | false => simp only [selected_false,mul_zero,le_refl]
    | true =>
      simpa only [selected_true,compactVisit] using hbound w ell S start hell hr hs hcons hcut c hc K q.1
  have hsum : (∑ n ∈ range N,∫⁻ z,selected (fun q : JointState w ell S start => moderateReward c K q.1) z
      ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
      ENNReal.ofReal D*(∑ n ∈ range N,∫⁻ z,selected (compactVisit K) z ∂CouplingData.sourceLaw w ell S start hs mesh n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _hn
    calc
      _ ≤ ∫⁻ z,ENNReal.ofReal D*selected (compactVisit K) z ∂CouplingData.sourceLaw w ell S start hs mesh n := lintegral_mono hpoint
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hlinear := exponential_quartic_absorbs_linear (C:=C) hK
  refine hsum.trans ?_
  calc
    _ ≤ ENNReal.ofReal D*(ENNReal.ofReal (K+1)*CouplingData.sourceLaw w ell S start hs mesh N failed) :=
      mul_le_mul_of_nonneg_left (actual_flagged_compact_visits hw hell hS0 hS hr hs hsS hK mesh N) zero_le
    _ ≤ _ := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hD]
      apply mul_le_mul_of_nonneg_right _ zero_le
      apply ENNReal.ofReal_le_ofReal
      dsimp [D]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlinear (show 0 ≤ 8*A/c^2 by positivity)

end NumberTheoryLean.ModerateFailedReward

end

section

namespace NumberTheoryLean.SourceFarGapTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeGridGeometry PrimeGridKernel PrimeInverseBins PrimeExponentialTail
open SourceAllInverseBins ExponentialMesh LowStateHorizon

theorem source_far_gap_tail : ∃ κ₀ C : ℝ,0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,
        1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ c : ℝ,0 < c → ∀ K : ℝ,
        (∀ n,1 ≤ n → n ≤ N → (∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
          ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4))) ∧
        ((∑ n ∈ range N,∫⁻ z,tailReward c K z ∂pathLaw w ell S start (n+1)) ≤
          (N:ℝ≥0∞)*ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4))) := by
  obtain ⟨κ₀,C,hκ₀,hC,hsource⟩ := source_all_inverse_bins
  refine ⟨κ₀,C,hκ₀,hC,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨w₀,hw₀,hsource⟩ := hsource κ hκ hκle d hd
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell B start hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut
  dsimp only
  intro c hc K
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
  have hm : 1 ≤ m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hh : width m ≤ 1 := mesh_le_one hκ.le w
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hb := hsource w hw ell B start hell hB hlogB hcomp hr hi h199 h23
  have hper : ∀ n,1 ≤ n → n ≤ N → (∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4)) := by
    intro n hn hnN
    exact actual_tail_from_inverse_bins hc hC.le hm hh hell hr hs hcons (by rwa [hcut]) hsS n (hb n hn hnN)
  refine ⟨hper,?_⟩
  change (∑ n ∈ range N,∫⁻ z,tailReward c K z ∂pathLaw w ell S start (n+1)) ≤
    (N:ℝ≥0∞)*ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4))
  calc
    _ ≤ ∑ _n ∈ range N,ENNReal.ofReal (C*(8/c^2)*(1+4/c)*Real.exp (-c*K/4)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hper (n+1) (by omega) (by have hh := Finset.mem_range.mp hn; omega)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

end NumberTheoryLean.SourceFarGapTail

end

section

namespace NumberTheoryLean.SourceModerateFailure

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualProcessCoupling PersistentFailureFlag FlaggedOccupationBound
open ModerateFailedReward SourceCouplingRate InverseWeightGrowth UniformBudgetRate
open ExponentialMesh LowStateHorizon

noncomputable def growingCutoff (w : ℝ) : ℝ := (Real.log w)^((1:ℝ)/10)

theorem source_moderate_failure : ∃ κ₀ A : ℝ,0 < κ₀ ∧ 0 < A ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ hs : Valid start.side start.ratio,
        1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ c : ℝ,0 < c →
          (∑ n ∈ range N,∫⁻ z,selected (fun q : JointState w ell S start => moderateReward c (growingCutoff w) q.1) z
            ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) n) ≤
              ENNReal.ofReal ((A/c^2)*Real.exp (-(κ/4)*Real.sqrt (Real.log w))) := by
  obtain ⟨κ₀,hκ₀,hrate⟩ := source_coupling_rate
  obtain ⟨A,C,hA,hC,hmod⟩ := actual_moderate_failed_sum
  refine ⟨κ₀,8*A,hκ₀,by positivity,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨wF,hwF,hrate⟩ := hrate κ hκ hκle d hd
  have hevent := (quartic_log_scale_absorption hC.le (show 0 < κ/2 by linarith)).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp hevent
  refine ⟨max wF (max normalizationThreshold wAux),hwF.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hr h23 hcons hcut
  dsimp only
  intro c hc
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwe := hwAux w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hscale := source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hwe.2
  have hcut0 : 0 ≤ growingCutoff w := Real.rpow_nonneg hlog _
  have hsize : start.gap ≤ (23/10:ℝ)*B := by
    have he : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at he
    have hh := (eq_div_iff (valid_pos hs).ne').mp he
    nlinarith
  have hfailed := ((hrate w ((le_max_left _ _).trans hw) ell B start hs hell hB hlogB hcomp hr h23 hcons hsize).1 N le_rfl).1
  have hm := hmod w ell S start hnorm hell hS0 hscale.1 hr hs hsS hcons (by rwa [hcut])
    c hc (growingCutoff w) hcut0 (mesh κ w) N
  have hcoef : 0 ≤ 8*A/c^2 := by positivity
  refine hm.trans ?_
  calc
    _ ≤ ENNReal.ofReal ((8*A/c^2)*Real.exp (C*(1+growingCutoff w)^4))*
        ENNReal.ofReal (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) :=
      mul_le_mul_of_nonneg_left hfailed zero_le
    _ = ENNReal.ofReal ((8*A/c^2)*(Real.exp (C*(1+growingCutoff w)^4)*
        Real.exp (-(κ/2)*Real.sqrt (Real.log w)))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have habsorb : Real.exp (C*(1+growingCutoff w)^4)*Real.exp (-(κ/2)*Real.sqrt (Real.log w)) ≤
          Real.exp (-(κ/4)*Real.sqrt (Real.log w)) := by
        simpa only [growingCutoff,div_div,show (2:ℝ)*2 = 4 by norm_num] using hwe.1
      exact mul_le_mul_of_nonneg_left habsorb hcoef

end NumberTheoryLean.SourceModerateFailure

end

section

namespace NumberTheoryLean.GrowingFarTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeExponentialTail SourceFarGapTail SourceModerateFailure LowStateHorizon

theorem growingCutoff_tendsto : Tendsto growingCutoff atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).comp Real.tendsto_log_atTop

theorem log_cube_growing_exp_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun w : ℝ => (Real.log w)^3*Real.exp (-c*growingCutoff w)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => x^30*Real.exp (-c*x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (30:ℝ) c hc
  apply Tendsto.congr' _ (h.comp growingCutoff_tendsto)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hw
  have hp : growingCutoff w^30 = (Real.log w)^3 := by
    unfold growingCutoff
    rw [← Real.rpow_mul_natCast hw]
    norm_num
  simp only [Function.comp_apply,hp]

noncomputable def farBudget (C c d w : ℝ) : ℝ :=
  (5*d^3*(C*(8/c^2)*(1+4/c)))*(Real.log w)^3*Real.exp (-(c/4)*growingCutoff w)

theorem farBudget_tendsto_zero (C d : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (farBudget C c d) atTop (𝓝 0) := by
  have h := (log_cube_growing_exp_tendsto (show 0 < c/4 by linarith)).const_mul (5*d^3*(C*(8/c^2)*(1+4/c)))
  simp only [mul_zero] at h
  convert h using 1
  funext w
  unfold farBudget
  ring

theorem source_horizon_comparison {B d w : ℝ} (hlogB : 2 ≤ Real.log B)
    (hcomp : Real.log B ≤ d*Real.log w) :
    (sourceHorizon ((Real.log B)^2) B:ℝ) ≤ 5*d^3*(Real.log w)^3 := by
  have hN := source_horizon_log_cube hlogB
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log B) hcomp 3
  nlinarith

theorem source_growing_far_tail : ∃ κ₀ C : ℝ,0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d : ℝ,0 < d → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,
        1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ c : ℝ,0 < c →
          (∑ n ∈ range N,∫⁻ z,tailReward c (growingCutoff w) z ∂pathLaw w ell S start (n+1)) ≤
            ENNReal.ofReal (farBudget C c d w) := by
  obtain ⟨κ₀,C,hκ₀,hC,hsource⟩ := source_far_gap_tail
  refine ⟨κ₀,C,hκ₀,hC,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨w₀,hw₀,hsource⟩ := hsource κ hκ hκle d hd
  refine ⟨w₀,hw₀,?_⟩
  intro w hw ell B start hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut
  dsimp only
  intro c hc
  have hb := (hsource w hw ell B start hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut c hc (growingCutoff w)).2
  have hN := source_horizon_comparison hlogB hcomp
  refine hb.trans ?_
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hcst : 0 ≤ C*(8/c^2)*(1+4/c)*Real.exp (-c*growingCutoff w/4) := by positivity
  have h := mul_le_mul_of_nonneg_right hN hcst
  unfold farBudget
  rw [show -(c/4)*growingCutoff w = -c*growingCutoff w/4 by ring]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

end NumberTheoryLean.GrowingFarTail

end

end Erdos970

end OAI
