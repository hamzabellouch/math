import OAI.NumberTheory.Jacobsthal.Analysis.CompactTestMeasurable

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualFiniteCoupling

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag FailureFlagBounds
open FlaggedSourceStart UniformFailureBudget PrimeBinMembership LowStateHorizon PrimeChainHorizon

theorem actual_finite_failure : ∃ c₁ c₂ C₁ C₂ C₃ D w₀ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < D ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node, ∀ mesh : ℝ, ∀ N : ℕ,
      ∀ (hnorm : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS3 : 3 ≤ S) (hS : S ≤ (Real.log w)^3)
        (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S),
      Consistent start → 0 < mesh → 2*mesh ≤ 1 → upperDisplacement S mesh N+mesh ≤ 1 →
      ∀ n ≤ N,
        sourceLaw hnorm hell (show 0 ≤ S from by linarith) hS hr hs hsS mesh n failed ≤
          (n:ℝ≥0∞)*ENNReal.ofReal (stepBudget c₁ c₂ C₁ C₂ C₃ D w S mesh N) := by
  obtain ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,hrow⟩ := uniform_actual_bad_row
  refine ⟨c₁,c₂,C₁,C₂,C₃,D,w₀,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hw₀,?_⟩
  intro w hw ell S start mesh N hnorm hell hS3 hS hr hs hsS hcons hm hmesh hupper n hn
  exact failure_probability_le
    (jointKernel hnorm hell (by linarith) hS hr hs hsS (Real.log start.gap) mesh)
    (mismatch_measurable mesh) (GoodAt (Real.log start.gap) mesh)
    (GoodAt_measurable (Real.log start.gap) mesh)
    (actual_good_step hnorm hell (by linarith) hS hr hs hsS (Real.log start.gap) hm)
    (sourceJoint w ell S start hs) (source_good hs hsS hm.le)
    (ENNReal.ofReal (stepBudget c₁ c₂ C₁ C₂ C₃ D w S mesh N)) N
    (fun m hm' q hq => hrow w hw ell S start (Real.log start.gap) mesh N hnorm hell hS3 hS hr hs hsS
      hcons hm hmesh hupper m hm'.le q hq) n hn

variable {w ell S B : ℝ} {start : Node}

theorem source_success_exits (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B) {mesh : ℝ} (hm : 0 < mesh)
    (n : ℕ) (hn : sourceHorizon S B ≤ n) :
    ∀ᵐ q ∂sourceLaw hw hell hS0 hS hr hs hsS mesh n,
      q.2 = false → q.1 = (none,CemeteryKernel.dead) := by
  have hP : ∀ᵐ p ∂(sourceLaw hw hell hS0 hS hr hs hsS mesh n).map (fun q => q.1.1), p = none := by
    rw [sourceLaw_prime,pathLaw_eq_cemetery hw hell hS0 hS hr hs hsS hB hsize n hn]
    exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
  have hp := (ae_map_iff (measurable_fst.comp measurable_fst).aemeasurable (measurableSet_singleton _)).mp hP
  filter_upwards [hp,sourceLaw_good hw hell hS0 hS hr hs hsS hm n] with q hq hgood
  intro hflag
  have hg := hgood hflag
  rcases q with ⟨⟨p,z⟩,b⟩
  change p = none at hq
  subst p
  cases z with
  | inl z => exact False.elim hg
  | inr u => cases u; rfl

end NumberTheoryLean.ActualFiniteCoupling

end

section

namespace NumberTheoryLean.CouplingData

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant KernelCouplingLift PersistentFailureFlag

noncomputable def joint (w ell S : ℝ) (start : Node) (v mesh : ℝ) :
    Kernel (JointState w ell S start) (JointState w ell S start) :=
  coupled (primeParent w ell S start) (continuousParent w ell S start v)
    (primeLabel_measurable w ell S mesh start) (continuousLabel_measurable S mesh)
    none CemeteryKernel.dead

noncomputable def sourceLaw (w ell S : ℝ) (start : Node) (hs : Valid start.side start.ratio)
    (mesh : ℝ) (n : ℕ) : Measure (FlagState (JointState w ell S start)) :=
  law (joint w ell S start (Real.log start.gap) mesh) (mismatch_measurable mesh)
    (FlaggedSourceStart.sourceJoint w ell S start hs) n

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
variable (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem joint_eq (v mesh : ℝ) :
    jointKernel hw hell hS0 hS hr hs hsS v mesh = joint w ell S start v mesh := rfl

theorem sourceLaw_eq (mesh : ℝ) (n : ℕ) :
    FlaggedSourceStart.sourceLaw hw hell hS0 hS hr hs hsS mesh n = sourceLaw w ell S start hs mesh n := rfl

include hw hell hS0 hS hr hsS in

theorem source_probability (mesh : ℝ) (n : ℕ) : IsProbabilityMeasure (sourceLaw w ell S start hs mesh n) := by
  rw [← sourceLaw_eq hw hell hS0 hS hr hs hsS]
  infer_instance

include hw hell hS0 hS hr hsS in

theorem source_prime (mesh : ℝ) (n : ℕ) :
    (sourceLaw w ell S start hs mesh n).map (fun q => q.1.1) = pathLaw w ell S start n := by
  rw [← sourceLaw_eq hw hell hS0 hS hr hs hsS]
  exact FlaggedSourceStart.sourceLaw_prime hw hell hS0 hS hr hs hsS mesh n

end NumberTheoryLean.CouplingData

end

section

namespace NumberTheoryLean.SourceCouplingRate

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open ActualFiniteCoupling UniformFailureBudget UniformBudgetRate ActualFlagInvariant
open PersistentFailureFlag LowStateHorizon ExponentialMesh

theorem source_coupling_rate : ∃ κ₀ : ℝ, 0 < κ₀ ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ d : ℝ, 0 < d → ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ, ∀ start : Node, ∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      (∀ n ≤ N,
        CouplingData.sourceLaw w ell S start hs (mesh κ w) n failed ≤
          ENNReal.ofReal (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) ∧
        ∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) n,
          q.2 = false → GoodAt (Real.log start.gap) (mesh κ w) n q.1) ∧
      (∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) N,
        q.2 = false → q.1 = (none,CemeteryKernel.dead)) := by
  obtain ⟨c₁,c₂,C₁,C₂,C₃,D,wF,hc₁,hc₂,hC₁,hC₂,hC₃,hD,hwF,hfinite⟩ := actual_finite_failure
  let κ₀ := min (c₁/4) (min (c₂/2) normalizationRate)
  have hκ₀ : 0 < κ₀ := lt_min (by positivity) (lt_min (by positivity) normalizationRate_pos)
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle d hd
  have hκ₁ : 4*κ ≤ c₁ := by
    have h : κ ≤ c₁/4 := hκle.trans (min_le_left _ _)
    linarith
  have hκ₂ : 2*κ ≤ c₂ := by
    have h : κ ≤ c₂/2 := (hκle.trans (min_le_right _ _)).trans (min_le_left _ _)
    linarith
  have hκr : κ ≤ normalizationRate := (hκle.trans (min_le_right _ _)).trans (min_le_right _ _)
  let A := 5*d^3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hevent := (uniform_budget_rate hC₁.le hC₂.le hC₃.le hD.le hA hκ hκ₁ hκ₂ hκr).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hevent
  let w₀ := max wF (max normalizationThreshold W)
  refine ⟨w₀,hwF.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hB hlogB hcomp hr hs23 hcons hsize
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hwF' : wF ≤ w := (le_max_left _ _).trans hw
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwW : W ≤ w := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hw
  have hwe := hW w hwW
  have hscale := source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hS : S ≤ (Real.log w)^3 := hscale.1
  have hsS : start.ratio ≤ S := by linarith
  have hN : (N:ℝ) ≤ A*(Real.log w)^3 := hscale.2
  have hrate := hwe.1 S hS0 hS N hN
  have hm : 0 < mesh κ w := mesh_pos κ w
  constructor
  · intro n hn
    constructor
    · have hf := hfinite w hwF' ell S start (mesh κ w) N hnorm hell hS3 hS hr hs hsS hcons
        hm hrate.1 hrate.2.1 n hn
      calc
        _ ≤ (n:ℝ≥0∞)*ENNReal.ofReal (stepBudget c₁ c₂ C₁ C₂ C₃ D w S (mesh κ w) N) := hf
        _ ≤ (N:ℝ≥0∞)*ENNReal.ofReal (stepBudget c₁ c₂ C₁ C₂ C₃ D w S (mesh κ w) N) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hn) zero_le
        _ = ENNReal.ofReal ((N:ℝ)*stepBudget c₁ c₂ C₁ C₂ C₃ D w S (mesh κ w) N) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg N),ENNReal.ofReal_natCast]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hrate.2.2
    · exact FlaggedSourceStart.sourceLaw_good hnorm hell hS0 hS hr hs hsS hm n
  · exact source_success_exits hnorm hell hS0 hS hr hs hsS hB hsize hm N le_rfl

end NumberTheoryLean.SourceCouplingRate

end

section

namespace NumberTheoryLean.MarkedSourceSmallness

open _root_.Filter
open scoped Topology
open ExponentialMesh

theorem mark_mesh_smallness {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop, mesh κ w ≤ 1/100 ∧ ∀ N : ℕ,
      (N:ℝ) ≤ A*(Real.log w)^3 → 4*(N:ℝ)*mesh κ w ≤ Real.log (11/10) := by
  have hlog : 0 < Real.log (11/10:ℝ) := Real.log_pos (by norm_num)
  filter_upwards [
    (log_power_exp_tendsto 1 0 hκ).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/100)),
    (log_power_exp_tendsto (4*A) 3 hκ).eventually (eventually_le_nhds hlog),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0:ℝ))] with w hm hN hL
  refine ⟨(mesh_upper κ w).trans (by simpa using hm),?_⟩
  intro N hbound
  calc
    _ ≤ (4*(A*(Real.log w)^3))*Real.exp (-κ*Real.sqrt (Real.log w)) :=
      mul_le_mul (by nlinarith) (mesh_upper κ w) (mesh_pos κ w).le (by positivity)
    _ = (4*A)*(Real.log w)^3*Real.exp (-κ*Real.sqrt (Real.log w)) := by ring
    _ ≤ _ := hN

theorem moving_compact_gap_small (R : ℝ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop, R < 6*(K*(Real.log w)^2) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max (1:ℝ) (1+R/(6*K))))] with w hw
  have hL : 1 ≤ Real.log w := (le_max_left _ _).trans hw
  have hR : 1+R/(6*K) ≤ Real.log w := (le_max_right _ _).trans hw
  have hm := mul_le_mul_of_nonneg_left hR (show 0 ≤ 6*K by positivity)
  have he : 6*K*(1+R/(6*K)) = 6*K+R := by field_simp [hK.ne']
  rw [he] at hm
  have hSq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hSq (show 0 ≤ 6*K by positivity)
  nlinarith

end NumberTheoryLean.MarkedSourceSmallness

end

section

namespace NumberTheoryLean.CompactCouplingError

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open CompactTestGeometry CompactTestMeasurable PrimeCompactVisits

variable {w ell S : ℝ} {start : Node}

noncomputable def difference (v : ℝ) (F : Side → ℝ×ℝ → ℝ)
    (q : FlagState (JointState w ell S start)) : ℝ≥0∞ :=
  ENNReal.ofReal |primeTest F q.1.1-continuousTest v F q.1.2|

theorem difference_measurable (v : ℝ) (F : Side → ℝ×ℝ → ℝ) (hF : ∀ i,Measurable (F i)) :
    Measurable (difference (w:=w) (ell:=ell) (S:=S) (start:=start) v F) :=
  ENNReal.measurable_ofReal.comp (((primeTest_measurable F).comp (measurable_fst.comp measurable_fst)).sub
    ((continuousTest_measurable v F hF).comp (measurable_snd.comp measurable_fst))).abs

theorem actual_finite_compact_error (F : Side → ℝ×ℝ → ℝ)
    (hF : ∀ i,UniformContinuous (F i)) {K η A : ℝ} (hK : 0 ≤ K) (hη : 0 < η) (hA : 0 ≤ A)
    (hbound : ∀ i x,|F i x| ≤ A) (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → F i (r,s)=0) :
    ∃ δ : ℝ,0 < δ ∧ ∀ w ell S : ℝ,∀ start : Node,
      ∀ _hw : normalizationThreshold ≤ w,∀ _hell : 1 ≤ ell,∀ _hS0 : 0 ≤ S,∀ _hS : S ≤ (Real.log w)^3,
      ∀ _hr : 0 < start.gap,∀ hs : Valid start.side start.ratio,∀ _hsS : start.ratio ≤ S,
      ∀ mesh : ℝ,0 < mesh → mesh ≤ δ → ∀ N : ℕ,
        4*(N:ℝ)*mesh ≤ 1 → 3*K*(Real.exp (4*(N:ℝ)*mesh)-1) ≤ δ →
        (∑ n ∈ range N,∫⁻ q,difference (Real.log start.gap) F q ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
          ENNReal.ofReal (η*(3*K+1))+ENNReal.ofReal (2*A)*(∑ n ∈ range N,CouplingData.sourceLaw w ell S start hs mesh n failed) := by
  obtain ⟨δ,hδ,hcompare⟩ := actual_compact_test_comparison F hF hK hη hsupport
  refine ⟨δ,hδ,?_⟩
  intro w ell S start hw hell hS0 hS hr hs hsS mesh hm hmδ N hclock hgap
  have hpoint : ∀ n < N,∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs mesh n,
      difference (Real.log start.gap) F q ≤ ENNReal.ofReal η*ENNReal.ofReal (visit (3*K) q.1.1)+
        ENNReal.ofReal (2*A)*failed.indicator (fun _ => (1:ℝ≥0∞)) q := by
    intro n hn
    have hgood := FlaggedSourceStart.sourceLaw_good hw hell hS0 hS hr hs hsS hm n
    rw [CouplingData.sourceLaw_eq hw hell hS0 hS hr hs hsS] at hgood
    filter_upwards [hgood] with q hq
    by_cases hb : q.2 = false
    · have hnum : 4*(n:ℝ)*mesh ≤ 4*(N:ℝ)*mesh := by
        have hnR : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hn.le
        nlinarith
      have hgapn : 3*K*(Real.exp (4*(n:ℝ)*mesh)-1) ≤ δ := by
        exact (mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_le_exp.mpr hnum) 1) (by positivity)).trans hgap
      have hc := hcompare w ell S start (by linarith : 0 ≤ ell) hr hs (Real.log start.gap) mesh n hmδ
        (hnum.trans hclock) hgapn q.1 (hq hb)
      rw [indicator_of_notMem (show q ∉ (failed:Set (FlagState (JointState w ell S start))) by change ¬q.2=true; simp [hb]),mul_zero,add_zero]
      rw [← ENNReal.ofReal_mul hη.le]
      exact ENNReal.ofReal_le_ofReal hc
    · have hbtrue : q.2 = true := by cases he : q.2 <;> simp_all
      rw [indicator_of_mem (show q ∈ (failed:Set (FlagState (JointState w ell S start))) from hbtrue),mul_one]
      exact (ENNReal.ofReal_le_ofReal (test_difference_bound hA hbound (Real.log start.gap) q.1.1 q.1.2)).trans
        (le_add_of_nonneg_left zero_le)
  have hone : ∀ n < N,(∫⁻ q,difference (Real.log start.gap) F q ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
      ENNReal.ofReal η*(∫⁻ z,ENNReal.ofReal (visit (3*K) z) ∂pathLaw w ell S start n)+
        ENNReal.ofReal (2*A)*CouplingData.sourceLaw w ell S start hs mesh n failed := by
    intro n hn
    have he := CouplingData.source_prime hw hell hS0 hS hr hs hsS mesh n
    calc
      _ ≤ ∫⁻ q,ENNReal.ofReal η*ENNReal.ofReal (visit (3*K) q.1.1)+
          ENNReal.ofReal (2*A)*failed.indicator (fun _ => (1:ℝ≥0∞)) q ∂CouplingData.sourceLaw w ell S start hs mesh n :=
        lintegral_mono_ae (hpoint n hn)
      _ = _ := by
        rw [lintegral_add_left (f:=fun q : FlagState (JointState w ell S start) => ENNReal.ofReal η*ENNReal.ofReal (visit (3*K) q.1.1))
          (measurable_const.mul ((measurable_of_countable (fun z : ChainState w ell S start => ENNReal.ofReal (visit (3*K) z))).comp (measurable_fst.comp measurable_fst))),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator failed_measurable,setLIntegral_const,one_mul,← he,
          lintegral_map (g:=fun q : FlagState (JointState w ell S start) => q.1.1)
            (measurable_of_countable (fun z : ChainState w ell S start => ENNReal.ofReal (visit (3*K) z)))
            (measurable_fst.comp measurable_fst)]
  have hsum := Finset.sum_le_sum (s:=range N) (fun n hn => hone n (Finset.mem_range.mp hn))
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at hsum
  refine hsum.trans (add_le_add_left ?_ _)
  have hvisit := finite_compact_visits hw hell hS0 hS hr hs hsS (K:=3*K) (by positivity) N
  have h := mul_le_mul_of_nonneg_left hvisit (show 0 ≤ ENNReal.ofReal η from zero_le)
  rw [← ENNReal.ofReal_mul hη.le] at h
  exact h

end NumberTheoryLean.CompactCouplingError

end

section

namespace NumberTheoryLean.SourceCompactCoupling

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open CompactTestGeometry CompactCouplingError ExponentialMesh SourceMarginalRate
open SourceCouplingRate HorizonMeshSmallness UniformBudgetRate LowStateHorizon PersistentFailureFlag

theorem source_compact_coupling (F : Side → ℝ×ℝ → ℝ) (hF : ∀ i,UniformContinuous (F i))
    {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hbound : ∀ i x,|F i x| ≤ A)
    (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → F i (r,s)=0) :
    ∃ κ₀ : ℝ,0 < κ₀ ∧ ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d ε : ℝ,0 < d → 0 < ε →
      ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ hs : Valid start.side start.ratio,
        1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        (∑ n ∈ range N,∫⁻ q,difference (Real.log start.gap) F q
          ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) n) ≤ ENNReal.ofReal ε := by
  obtain ⟨κ₀,hκ₀,hrate⟩ := source_coupling_rate
  refine ⟨κ₀,hκ₀,?_⟩
  intro κ hκ hκle d ε hd hε
  let η := ε/(2*(3*K+1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hfinite⟩ := actual_finite_compact_error F hF hK hη hA hbound hsupport
  obtain ⟨wP,hwP,hrate⟩ := hrate κ hκ hκle d hd
  let H := 5*d^3
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hevent := (horizon_mesh_smallness (D:=0) hH (by norm_num) hκ).and
    ((mesh_eventually_small hκ hδ).and
      (((log_power_exp_tendsto (2*A*H) 3 (show 0 < κ/2 by linarith)).eventually
        (eventually_le_nhds (show 0 < ε/2 by linarith))).and
        (((log_power_exp_tendsto (36*K*H) 3 hκ).eventually (eventually_le_nhds hδ)).and
          (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2))))))
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp hevent
  refine ⟨max wP (max normalizationThreshold wAux),hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hB hlogB hcomp hr h23 hcons hsize
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwe := hwAux w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hscale := source_scale_bound hwe.2.2.2.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hN : (N:ℝ) ≤ H*(Real.log w)^3 := hscale.2
  have hnum := hwe.1 S hS0 hscale.1 N hN
  have hm := mesh_pos κ w
  have hgap : 3*K*(Real.exp (4*(N:ℝ)*mesh κ w)-1) ≤ δ := by
    have he := exp_increment (show 0 ≤ 4*(N:ℝ)*mesh κ w by positivity) hnum.2.1
    have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hwe.2.2.2.2
    have hmul : (N:ℝ)*mesh κ w ≤ (H*(Real.log w)^3)*Real.exp (-κ*Real.sqrt (Real.log w)) :=
      mul_le_mul hN (mesh_upper κ w) hm.le (by positivity)
    calc
      _ ≤ 36*K*((N:ℝ)*mesh κ w) := by nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 3*K by positivity)]
      _ ≤ (36*K*H)*(Real.log w)^3*Real.exp (-κ*Real.sqrt (Real.log w)) := by
        have hh := mul_le_mul_of_nonneg_left hmul (show 0 ≤ 36*K by positivity)
        simpa only [mul_assoc] using hh
      _ ≤ _ := hwe.2.2.2.1
  have herror := hfinite w ell S start hnorm hell hS0 hscale.1 hr hs hsS (mesh κ w) hm hwe.2.1 N hnum.2.1 hgap
  have hfail := (hrate w ((le_max_left _ _).trans hw) ell B start hs hell hB hlogB hcomp hr h23 hcons hsize).1
  have hsumfail : (∑ n ∈ range N,CouplingData.sourceLaw w ell S start hs (mesh κ w) n failed) ≤
      (N:ℝ≥0∞)*ENNReal.ofReal (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) := by
    calc
      _ ≤ ∑ _n ∈ range N,ENNReal.ofReal (Real.exp (-(κ/2)*Real.sqrt (Real.log w))) := by
        apply Finset.sum_le_sum
        intro n hn
        exact (hfail n (show n ≤ N from (Finset.mem_range.mp hn).le)).1
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hfailSmall : ENNReal.ofReal (2*A)*(∑ n ∈ range N,CouplingData.sourceLaw w ell S start hs (mesh κ w) n failed) ≤
      ENNReal.ofReal (ε/2) := by
    refine (mul_le_mul_of_nonneg_left hsumfail zero_le).trans ?_
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (show 0 ≤ 2*A by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn := mul_le_mul_of_nonneg_left hN (show 0 ≤ 2*A by positivity)
    have he := mul_le_mul_of_nonneg_right hn (Real.exp_pos (-(κ/2)*Real.sqrt (Real.log w))).le
    have hlim := hwe.2.2.1
    nlinarith
  have hηeq : η*(3*K+1)=ε/2 := by dsimp [η]; field_simp
  rw [hηeq] at herror
  refine herror.trans ((add_le_add_right hfailSmall _).trans ?_)
  rw [← ENNReal.ofReal_add (show 0 ≤ ε/2 by positivity) (show 0 ≤ ε/2 by positivity)]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring : ε/2+ε/2=ε))

end NumberTheoryLean.SourceCompactCoupling

end

end Erdos970

end OAI
