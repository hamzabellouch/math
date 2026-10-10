import OAI.NumberTheory.Jacobsthal.Primes.PrimeTailSplit
import OAI.NumberTheory.Jacobsthal.Renewal.NonnegativeOriginalOccupation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceSuccessfulTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures TransitionKernels PrimeHistories PrimeKilledChain
open SuccessfulTailTransport ExponentialMesh HorizonMeshSmallness UniformBudgetRate LowStateHorizon
open RegeneratingInverseBands CostPrefixTransport

theorem even_source_cost_state {start : Node} (hs : Valid start.side start.ratio)
    (hi : start.side = .even) :
    ∃ s : EvenState,s.1 = start.ratio ∧ FlaggedSourceStart.sourceCostState hs = (.inl s,0) := by
  cases start with
  | mk i s r cap closed =>
    change i = .even at hi
    subst i
    exact ⟨⟨s,hs⟩,rfl,rfl⟩

theorem source_successful_tail (κ d c : ℝ) (hκ : 0 < κ) (hd : 0 < d) (hc : 0 < c) :
    ∃ b : ℕ → ℝ≥0∞,Tendsto b atTop (𝓝 0) ∧ ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ hs : Valid start.side start.ratio,
        1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ M : ℕ,(∑ n ∈ range N,∫⁻ q,cleanReward c (3*((M:ℝ)+1)) q
          ∂CouplingData.sourceLaw w ell S start hs (mesh κ w) (n+1)) ≤ b M := by
  obtain ⟨L,hL,htransport⟩ := actual_clean_tail_transport
  obtain ⟨b,hb,hband⟩ := EvenInverseBands.source_exponential_reward_tail (show 0 < c/3 by linarith)
  refine ⟨fun M => ENNReal.ofReal 27*b M,?_,?_⟩
  · simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a:=ENNReal.ofReal 27) hb (Or.inr ENNReal.ofReal_ne_top)
  let A := 5*d^3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hevent := (horizon_mesh_smallness hA hL.le hκ).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp hevent
  refine ⟨max normalizationThreshold wAux,normalizationThreshold_gt_one.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell _hB hlogB hcomp hr hi h199 h23
  dsimp only
  intro M
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hnorm : normalizationThreshold ≤ w := (le_max_left _ _).trans hw
  have hwe := hwAux w ((le_max_right _ _).trans hw)
  have hscale := source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hnum := hwe.1 S hS0 hscale.1 N hscale.2
  have hsum := htransport w ell S start hnorm hell hS0 hscale.1 hr hs hsS hS3
    (mesh κ w) (mesh_pos κ w) N hnum.2.1 hnum.2.2.1 M c hc
  obtain ⟨s,hsv,hcost⟩ := even_source_cost_state hs hi
  have htail := hband M s (by simpa only [hsv] using h199) (by simpa only [hsv] using h23)
    (Real.log start.gap) ell hell
  rw [hcost] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left htail zero_le)

end NumberTheoryLean.SourceSuccessfulTail

end

section

namespace NumberTheoryLean.SourceTailBudget

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeExponentialTail PrimeTailSplit InitialPrimeTail
open SourceSuccessfulTail SourceModerateFailure GrowingFarTail ExponentialMesh
open UniformBudgetRate LowStateHorizon

noncomputable def failureBudget (A c κ w : ℝ) : ℝ := (A/c^2)*Real.exp (-(κ/4)*Real.sqrt (Real.log w))

theorem failureBudget_tendsto_zero (A c : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (failureBudget A c κ) atTop (𝓝 0) := by
  change Tendsto (fun w : ℝ => (A/c^2)*Real.exp (-(κ/4)*Real.sqrt (Real.log w))) atTop (𝓝 0)
  simpa only [pow_zero,mul_one] using log_power_exp_tendsto (A/c^2) 0 (show 0 < κ/4 by linarith)

theorem source_tail_budget : ∃ κ₀ A C : ℝ,0 < κ₀ ∧ 0 < A ∧ 0 < C ∧
    ∀ κ : ℝ,0 < κ → κ ≤ κ₀ → ∀ d c : ℝ,0 < d → 0 < c →
      ∃ b : ℕ → ℝ≥0∞,Tendsto b atTop (𝓝 0) ∧ ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ _hs : Valid start.side start.ratio,
        1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
        0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        ∀ M : ℕ,(∑ n ∈ range N,∫⁻ z,tailReward c (3*((M:ℝ)+1)) z ∂pathLaw w ell S start n) ≤
          ENNReal.ofReal (2*initialBudget c B)+b M+
          ENNReal.ofReal (failureBudget A c κ w)+ENNReal.ofReal (farBudget C c d w) := by
  obtain ⟨κM,A,hκM,hA,hmoderate⟩ := source_moderate_failure
  obtain ⟨κF,C,hκF,hC,hfar⟩ := source_growing_far_tail
  refine ⟨min κM κF,A,C,lt_min hκM hκF,hA,hC,?_⟩
  intro κ hκ hκle d c hd hc
  obtain ⟨wM,hwM,hmoderate⟩ := hmoderate κ hκ (hκle.trans (min_le_left _ _)) d hd
  obtain ⟨wF,hwF,hfar⟩ := hfar κ hκ (hκle.trans (min_le_right _ _)) d hd
  obtain ⟨b,hb,wC,hwC,hclean⟩ := source_successful_tail κ d c hκ hd hc
  obtain ⟨wScale,hwScale⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  let w₀ := max (max wM wF) (max wC (max normalizationThreshold wScale))
  refine ⟨b,hb,w₀,hwM.trans_le ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut
  dsimp only
  intro M
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hwM' : wM ≤ w := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hw
  have hwF' : wF ≤ w := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hw
  have hwC' : wC ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hnorm : normalizationThreshold ≤ w :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hw
  have hwScale' : wScale ≤ w :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hw
  have hscale := source_scale_bound (hwScale w hwScale') hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hsize : B ≤ start.gap := by
    have he : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at he
    have hh := (eq_div_iff (valid_pos hs).ne').mp he
    nlinarith
  have hsplit := actual_finite_tail_split hnorm hell hS0 hscale.1 hr hs hsS c (3*((M:ℝ)+1))
    (growingCutoff w) (mesh κ w) N
  have hinitK := source_initial_tail (w:=w) (ell:=ell) (S:=S) (K:=3*((M:ℝ)+1)) hc hB hsize hi h199 h23
  have hinitT := source_initial_tail (w:=w) (ell:=ell) (S:=S) (K:=growingCutoff w) hc hB hsize hi h199 h23
  have hsuccess := hclean w hwC' ell B start hs hell hB hlogB hcomp hr hi h199 h23 M
  have hfailed := hmoderate w hwM' ell B start hs hell hellB hB hlogB hcomp hr h23 hcons hcut c hc
  have hfarther := hfar w hwF' ell B start hell hellB hB hlogB hcomp hr hi h199 h23 hcons hcut c hc
  have hI : 0 ≤ initialBudget c B := by unfold initialBudget; have h0 := initialConstant_pos; positivity
  have hIadd : ENNReal.ofReal (initialBudget c B)+ENNReal.ofReal (initialBudget c B) =
      ENNReal.ofReal (2*initialBudget c B) := by
    rw [← ENNReal.ofReal_add hI hI]
    congr 1
    ring
  have hbound := add_le_add (add_le_add (add_le_add (add_le_add hinitK hinitT) hsuccess) hfailed) hfarther
  rw [hIadd] at hbound
  exact hsplit.trans hbound

end NumberTheoryLean.SourceTailBudget

end

section

namespace NumberTheoryLean.SourceUniformTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeExponentialTail SourceTailBudget InitialPrimeTail GrowingFarTail LowStateHorizon

theorem four_quarters {ε : ℝ} (hε : 0 ≤ ε) :
    ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4) = ENNReal.ofReal ε := by
  have hq : 0 ≤ ε/4 := by positivity
  rw [← ENNReal.ofReal_add hq hq,← ENNReal.ofReal_add (by positivity) hq,
    ← ENNReal.ofReal_add (by positivity) hq]
  congr 1
  ring

theorem actual_uniform_inverse_tail (d c ε : ℝ) (hd : 0 < d) (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₀ : ℕ,∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧
      ∀ M : ℕ,M₀ ≤ M → ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      ∀ ell : ℝ,1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      ∀ start : Node,start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        (∑ n ∈ range N,∫⁻ z,tailReward c (3*((M:ℝ)+1)) z ∂pathLaw w ell S start n) ≤ ENNReal.ofReal ε := by
  obtain ⟨κ₀,A,C,hκ₀,hA,hC,hsource⟩ := source_tail_budget
  let κ := κ₀/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκle : κ ≤ κ₀ := by dsimp [κ]; linarith
  obtain ⟨b,hb,wP,hwP,hsource⟩ := hsource κ hκ hκle d c hd hc
  have hδ : 0 < ε/4 := by positivity
  obtain ⟨M₀,hM₀⟩ := eventually_atTop.mp (hb.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr hδ)))
  have hinit : Tendsto (fun B : ℝ => 2*initialBudget c B) atTop (𝓝 0) := by
    simpa only [mul_zero] using (initialBudget_tendsto_zero hc).const_mul 2
  obtain ⟨Baux,hBaux⟩ := eventually_atTop.mp (hinit.eventually (eventually_le_nhds hδ))
  obtain ⟨wFail,hwFail⟩ := eventually_atTop.mp
    ((failureBudget_tendsto_zero A c hκ).eventually (eventually_le_nhds hδ))
  obtain ⟨wFar,hwFar⟩ := eventually_atTop.mp
    ((farBudget_tendsto_zero C d hc).eventually (eventually_le_nhds hδ))
  let B₀ := max (Real.exp 2) Baux
  let w₀ := max wP (max wFail wFar)
  refine ⟨M₀,B₀,w₀,(Real.exp_pos 2).trans_le (le_max_left _ _),hwP.trans_le (le_max_left _ _),?_⟩
  intro M hM B w hB hw ell hell hellB hcomp start hi h199 h23 hcons hcut
  dsimp only
  have hBexp : Real.exp 2 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := (Real.exp_pos 2).trans_le hBexp
  have hlogB : 2 ≤ Real.log B := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hBexp
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hr : 0 < start.gap := by
    have he : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at he
    have hh := (eq_div_iff (valid_pos hs).ne').mp he
    rw [← hh]
    exact mul_pos hBpos (valid_pos hs)
  have hbudget := hsource w ((le_max_left _ _).trans hw) ell B start hs hell hellB hBpos hlogB hcomp hr hi h199 h23 hcons hcut M
  have hI := ENNReal.ofReal_le_ofReal (hBaux B ((le_max_right _ _).trans hB))
  have hF := ENNReal.ofReal_le_ofReal (hwFail w ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hw))
  have hG := ENNReal.ofReal_le_ofReal (hwFar w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw))
  have hsum := add_le_add (add_le_add (add_le_add hI (hM₀ M hM)) hF) hG
  rw [four_quarters hε.le] at hsum
  exact hbudget.trans hsum

end NumberTheoryLean.SourceUniformTail

end

section

namespace NumberTheoryLean.ScaledOriginalTail

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership DerivativeWeights
open PrimeCompactWeights PrimeCorrectionFactor PrimeExponentialTail SourceUniformTail LowStateHorizon

noncomputable def prefactorBound : ℝ := 2*weight .even (199/100)

theorem prefactorBound_pos : 0 < prefactorBound :=
  mul_pos (by norm_num) (weight_pos (by norm_num [Valid]))

noncomputable def scaledTail (c K w B : ℝ) {ell S : ℝ} (start : Node) : ChainState w ell S start → ℝ≥0∞
  | none => 0
  | some h => if K < h.node.gap then ENNReal.ofReal
      (scaledWeight w B start (some h)*Real.exp (-c*h.node.gap)) else 0

theorem scaled_reward_prefactor {w ell S B c : ℝ} {start : Node}
    (hB : 0 ≤ B) (hr : 0 < start.gap) (hsize : B ≤ start.gap)
    (hs : Valid start.side start.ratio) (hi : start.side = .even) (h199 : 199/100 ≤ start.ratio)
    (h : History w ell S start) (hcorr : (1+epsilon w)^h.primes.length ≤ 2) :
    scaledWeight w B start (some h)*Real.exp (-c*h.node.gap) ≤
      prefactorBound*(h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio) := by
  have hφ := weight_pos hs
  have hφg := weight_pos (terminal_valid hs h.admissible)
  have hφ0 : 0 < weight .even (199/100) := weight_pos (by norm_num [Valid])
  have hinit : weight start.side start.ratio ≤ weight .even (199/100) := by
    rw [hi]
    exact TwoStepDensityBounds.weight_antitone (by norm_num [Valid]) (hi ▸ hs) h199
  have hrat : B/start.gap ≤ 1 := (div_le_one hr).mpr hsize
  have hrat0 : 0 ≤ B/start.gap := div_nonneg hB hr.le
  have hrat2 : (B/start.gap)^2 ≤ 1 := by nlinarith
  have hcorr0 := pow_nonneg (normalizer_pos w).le h.primes.length
  have hcoef : ((B/start.gap)^2*(1+epsilon w)^h.primes.length)*weight start.side start.ratio ≤ prefactorBound := by
    have hh : (B/start.gap)^2*(1+epsilon w)^h.primes.length ≤ 2 :=
      (mul_le_mul hrat2 hcorr hcorr0 zero_le_one).trans_eq (one_mul 2)
    exact mul_le_mul hh hinit hφ.le (by norm_num)
  calc
    _ = (((B/start.gap)^2*(1+epsilon w)^h.primes.length)*weight start.side start.ratio)*
        (h.node.gap^2*Real.exp (-c*h.node.gap)/weight h.node.side h.node.ratio) := by
      unfold scaledWeight
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

theorem source_scaled_tail_envelope {d w ell B c K : ℝ} {start : Node}
    (hB : 0 < B) (hell : 1 ≤ ell) (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w)
    (hbudget : correctionBudget d w ≤ 1)
    (hi : start.side = .even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff = B)
    (z : ChainState w ell ((Real.log B)^2) start) :
    scaledTail c K w B start z ≤ ENNReal.ofReal prefactorBound*tailReward c K z := by
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have he : B*start.ratio = start.gap := by
    have hh : start.cutoff = start.gap/start.ratio := hcons
    rw [hcut] at hh
    exact (eq_div_iff (valid_pos hs).ne').mp hh
  have hr : 0 < start.gap := by rw [← he]; exact mul_pos hB (valid_pos hs)
  have hsize : B ≤ start.gap := by nlinarith
  have hupper : start.gap ≤ (23/10:ℝ)*B := by nlinarith
  cases z with
  | none => simp [scaledTail,tailReward]
  | some h =>
    have hcorrection : (1+epsilon w)^h.primes.length ≤ 2 := by
      have hh := (history_correction hlogB hcomp hell hr hs hB hupper h).2
      linarith
    have hbound := scaled_reward_prefactor (c:=c) hB.le hr hsize hs hi h199 h hcorrection
    by_cases hh : K < h.node.gap
    · rw [scaledTail,tailReward,ite_eq_left hh,ite_eq_left hh,← ENNReal.ofReal_mul prefactorBound_pos.le]
      exact ENNReal.ofReal_le_ofReal hbound
    · simp [scaledTail,tailReward,hh]

theorem actual_uniform_scaled_tail (d c ε : ℝ) (hd : 0 < d) (hc : 0 < c) (hε : 0 < ε) :
    ∃ M₀ : ℕ,∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧
      ∀ M : ℕ,M₀ ≤ M → ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      ∀ ell : ℝ,1 ≤ ell → ell ≤ B → Real.log B ≤ d*Real.log w →
      ∀ start : Node,start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff = B →
        let S := (Real.log B)^2
        let N := sourceHorizon S B
        (∑ n ∈ range N,∫⁻ z,scaledTail c (3*((M:ℝ)+1)) w B start z ∂pathLaw w ell S start n) ≤ ENNReal.ofReal ε := by
  have hD := prefactorBound_pos
  obtain ⟨M₀,BR,wR,hBR,hwR,hraw⟩ := actual_uniform_inverse_tail d c (ε/prefactorBound) hd hc (div_pos hε hD)
  obtain ⟨wCorr,hwCorr⟩ := eventually_atTop.mp
    ((correctionBudget_tendsto_zero d).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)))
  refine ⟨M₀,max BR (Real.exp 2),max wR wCorr,hBR.trans_le (le_max_left _ _),hwR.trans_le (le_max_left _ _),?_⟩
  intro M hM B w hB hw ell hell hellB hcomp start hi h199 h23 hcons hcut
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hBR' : BR ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := hBR.trans_le hBR'
  have hlogB : 2 ≤ Real.log B := by
    have hh : Real.exp 2 ≤ B := (le_max_right _ _).trans hB
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hh
  have hbudget := hwCorr w ((le_max_right _ _).trans hw)
  have hb := hraw M hM B w hBR' ((le_max_left _ _).trans hw) ell hell hellB hcomp start hi h199 h23 hcons hcut
  have hpoint := source_scaled_tail_envelope (c:=c) (K:=3*((M:ℝ)+1)) hBpos hell hlogB hcomp hbudget hi h199 h23 hcons hcut
  calc
    _ ≤ ∑ n ∈ range N,ENNReal.ofReal prefactorBound*(∫⁻ z,tailReward c (3*((M:ℝ)+1)) z ∂pathLaw w ell S start n) := by
      apply Finset.sum_le_sum
      intro n _hn
      calc
        _ ≤ ∫⁻ z,ENNReal.ofReal prefactorBound*tailReward c (3*((M:ℝ)+1)) z ∂pathLaw w ell S start n := lintegral_mono hpoint
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal prefactorBound*ENNReal.ofReal (ε/prefactorBound) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hb zero_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul hD.le]
      congr 1
      field_simp

end NumberTheoryLean.ScaledOriginalTail

end

end Erdos970

end OAI
