import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import OAI.NumberTheory.Jacobsthal.Paths.FlaggedHarmonicTransform
import OAI.NumberTheory.Jacobsthal.Probability.SourceCompactCoupling

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SignedCompactTransfer

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain PrimeBinMembership
open CompactTestGeometry CompactTestMeasurable CompactCouplingError SourceCompactCoupling
open ActualProcessCoupling PersistentFailureFlag ContinuousKilledBins LowStateHorizon
open ExponentialMesh UniformBudgetRate

noncomputable def primeExpectation (F : Side → ℝ×ℝ → ℝ) (w ell S : ℝ) (start : Node) (N : ℕ) : ℝ :=
  ∑ n ∈ range N,∫ z,primeTest F z ∂pathLaw w ell S start n

noncomputable def continuousExpectation (F : Side → ℝ×ℝ → ℝ) (v ell S : ℝ) (z : CostState) (N : ℕ) : ℝ :=
  ∑ n ∈ range N,∫ y,continuousTest v F y ∂((continuousChain v ell S)^n) (.inl z)

variable {w ell S : ℝ} {start : Node}
variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hsS in
theorem actual_signed_difference (F : Side → ℝ×ℝ → ℝ) (hF : ∀ i,Measurable (F i))
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ i x,|F i x| ≤ A) (mesh : ℝ) (N : ℕ) :
    ENNReal.ofReal |primeExpectation F w ell S start N-
      continuousExpectation F (Real.log start.gap) ell S (FlaggedSourceStart.sourceCostState hs) N| ≤
        ∑ n ∈ range N,∫⁻ q,difference (Real.log start.gap) F q ∂CouplingData.sourceLaw w ell S start hs mesh n := by
  let μ := fun n => CouplingData.sourceLaw w ell S start hs mesh n
  let P := fun q : FlagState (JointState w ell S start) => primeTest F q.1.1
  let Q := fun q : FlagState (JointState w ell S start) => continuousTest (Real.log start.gap) F q.1.2
  have hP : Measurable P := (primeTest_measurable F).comp (measurable_fst.comp measurable_fst)
  have hQ : Measurable Q := (continuousTest_measurable _ F hF).comp (measurable_snd.comp measurable_fst)
  have hIP : ∀ n ∈ range N,Integrable P (μ n) := by
    intro n _hn
    let := CouplingData.source_probability hw hell hS0 hS hr hs hsS mesh n
    exact bounded_integrable hP (fun q => primeTest_bound hA hbound q.1.1)
  have hIQ : ∀ n ∈ range N,Integrable Q (μ n) := by
    intro n _hn
    let := CouplingData.source_probability hw hell hS0 hS hr hs hsS mesh n
    exact bounded_integrable hQ (fun q => continuousTest_bound hA hbound _ q.1.2)
  have hp : primeExpectation F w ell S start N = ∑ n ∈ range N,∫ q,P q ∂μ n := by
    apply Finset.sum_congr rfl
    intro n _hn
    rw [← CouplingData.source_prime hw hell hS0 hS hr hs hsS mesh n,
      integral_map (φ:=fun q : FlagState (JointState w ell S start) => q.1.1)
        (measurable_fst.comp measurable_fst).aemeasurable (primeTest_measurable F).aestronglyMeasurable]
  have hq : continuousExpectation F (Real.log start.gap) ell S (FlaggedSourceStart.sourceCostState hs) N =
      ∑ n ∈ range N,∫ q,Q q ∂μ n := by
    apply Finset.sum_congr rfl
    intro n _hn
    have he := FlaggedSourceStart.sourceLaw_continuous hw hell hS0 hS hr hs hsS mesh n
    rw [CouplingData.sourceLaw_eq hw hell hS0 hS hr hs hsS] at he
    rw [← he,integral_map (φ:=fun q : FlagState (JointState w ell S start) => q.1.2)
      (measurable_snd.comp measurable_fst).aemeasurable (continuousTest_measurable _ F hF).aestronglyMeasurable]
  rw [hp,hq]
  exact finite_integral_difference μ P Q N hIP hIQ

theorem source_signed_compact_transfer (F : Side → ℝ×ℝ → ℝ)
    (hF : ∀ i,UniformContinuous (F i)) {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hbound : ∀ i x,|F i x| ≤ A) (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → F i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      |primeExpectation F w ell S start N-
        continuousExpectation F (Real.log start.gap) ell S (FlaggedSourceStart.sourceCostState hs) N| ≤ ε := by
  obtain ⟨κ₀,hκ₀,hcouple⟩ := source_compact_coupling F hF hK hA hbound hsupport
  let κ := κ₀/2
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨wP,hwP,hcouple⟩ := hcouple κ hκ (by dsimp [κ]; linarith) d ε hd hε
  obtain ⟨wScale,hwScale⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  refine ⟨max wP (max normalizationThreshold wScale),hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hB hlogB hcomp hr h23 hcons hsize
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hscale := source_scale_bound
    (hwScale w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)) hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hdiff := actual_signed_difference hnorm hell hS0 hscale.1 hr hs hsS F
    (fun i => (hF i).continuous.measurable) hA hbound (mesh κ w) N
  have hsmall := hcouple w ((le_max_left _ _).trans hw) ell B start hs hell hB hlogB hcomp hr h23 hcons hsize
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp (hdiff.trans hsmall)

end NumberTheoryLean.SignedCompactTransfer

end

section

namespace NumberTheoryLean.CompactInverseTest

open _root_.Set
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open DerivativeWeights CompactTestGeometry SignedCompactTransfer InvariantInverseWeights

noncomputable def lowerRatio : Side → ℝ | .even => 198/100 | .odd => 95/100

theorem valid_lower (i : Side) (s : ℝ) : Valid i s ↔ lowerRatio i ≤ s := by cases i <;> rfl

noncomputable def safeWeight (i : Side) (s : ℝ) : ℝ := weight i (max (lowerRatio i) s)

theorem safeWeight_pos (i : Side) (s : ℝ) : 0 < safeWeight i s :=
  weight_pos ((valid_lower _ _).mpr (le_max_left _ _))

theorem safeWeight_eq {i : Side} {s : ℝ} (hs : Valid i s) : safeWeight i s = weight i s := by
  unfold safeWeight
  rw [max_eq_right ((valid_lower _ _).mp hs)]

theorem safeWeight_continuous (i : Side) : Continuous (safeWeight i) := by
  cases i with
  | even =>
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : 1 < max (198/100:ℝ) x := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    exact (phiEven_continuousAt hx).comp (continuous_const.max continuous_id).continuousAt
  | odd => exact phiOdd_continuous.comp (continuous_const.max continuous_id)

noncomputable def inverseTest (H : Side → ℝ×ℝ → ℝ) (i : Side) (x : ℝ×ℝ) : ℝ :=
  x.1^2*H i x/safeWeight i x.2

theorem inverseTest_continuous {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,Continuous (H i)) (i : Side) :
    Continuous (inverseTest H i) :=
  ((continuous_fst.pow 2).mul (hH i)).div ((safeWeight_continuous i).comp continuous_snd)
    (fun x => (safeWeight_pos i x.2).ne')

theorem inverseTest_compact {H : Side → ℝ×ℝ → ℝ} (hH : ∀ i,HasCompactSupport (H i)) (i : Side) :
    HasCompactSupport (inverseTest H i) := by
  have he : inverseTest H i = (fun x : ℝ×ℝ => x.1^2/safeWeight i x.2)*(H i) := by
    funext x
    dsimp [inverseTest]
    ring
  rw [he]
  exact (hH i).mul_left

theorem inverseTest_uniform {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i)) :
    ∀ i,UniformContinuous (inverseTest H i) := fun i =>
  (inverseTest_compact hcompact i).uniformContinuous_of_continuous (inverseTest_continuous hH i)

theorem inverseTest_bounded {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i)) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ i x,|inverseTest H i x| ≤ A := by
  obtain ⟨Ae,he⟩ := (inverseTest_continuous hH .even).bounded_above_of_compact_support (inverseTest_compact hcompact .even)
  obtain ⟨Ao,ho⟩ := (inverseTest_continuous hH .odd).bounded_above_of_compact_support (inverseTest_compact hcompact .odd)
  refine ⟨max 0 (max Ae Ao),le_max_left _ _,?_⟩
  intro i x
  cases i with
  | even =>
    have hx : |inverseTest H .even x| ≤ Ae := by simpa only [Real.norm_eq_abs] using he x
    exact hx.trans ((le_max_left _ _).trans (le_max_right _ _))
  | odd =>
    have hx : |inverseTest H .odd x| ≤ Ao := by simpa only [Real.norm_eq_abs] using ho x
    exact hx.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem inverseTest_gap_support {H : Side → ℝ×ℝ → ℝ} {K : ℝ}
    (hH : ∀ i : Side,∀ r s : ℝ,K < r → H i (r,s)=0) :
    ∀ i : Side,∀ r s : ℝ,K < r → inverseTest H i (r,s)=0 := by
  intro i r s hr
  simp [inverseTest,hH i r s hr]

theorem inverseTest_eq {H : Side → ℝ×ℝ → ℝ} {i : Side} {r s : ℝ} (hs : Valid i s) :
    inverseTest H i (r,s) = r^2*H i (r,s)/weight i s := by
  simp only [inverseTest,safeWeight_eq hs]

theorem prime_inverseTest_eq {w ell S : ℝ} {start : Node} {H : Side → ℝ×ℝ → ℝ}
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    primeTest (inverseTest H) (some h) =
      h.node.gap^2*H h.node.side (h.node.gap,h.node.ratio)/weight h.node.side h.node.ratio :=
  inverseTest_eq (terminal_valid hs h.admissible)

end NumberTheoryLean.CompactInverseTest

end

section

namespace NumberTheoryLean.CompactNormalizationCorrection

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactVisits
open CompactTestGeometry CompactTestMeasurable SignedCompactTransfer PrimeCorrectionFactor

variable {w ell S : ℝ} {start : Node}

noncomputable def correctedTest (F : Side → ℝ×ℝ → ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => (1+epsilon w)^h.primes.length*F h.node.side (h.node.gap,h.node.ratio)

noncomputable def correctedExpectation (F : Side → ℝ×ℝ → ℝ) (w ell S : ℝ) (start : Node) (N : ℕ) : ℝ :=
  ∑ n ∈ range N,∫ z,correctedTest F z ∂pathLaw w ell S start n

theorem correctedTest_measurable (F : Side → ℝ×ℝ → ℝ) :
    Measurable (correctedTest (w:=w) (ell:=ell) (S:=S) (start:=start) F) := measurable_of_countable _

theorem correction_difference_bound {d w ell B K A : ℝ} {start : Node}
    (F : Side → ℝ×ℝ → ℝ) (_hA : 0 ≤ A) (hbound : ∀ i x,|F i x| ≤ A)
    (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → F i (r,s)=0)
    (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) (hell : 1 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B)
    (z : ChainState w ell ((Real.log B)^2) start) :
    |correctedTest F z-primeTest F z| ≤ (correctionBudget d w*A)*visit K z := by
  cases z with
  | none => simp [correctedTest,primeTest,visit]
  | some h =>
    have hc := history_correction hlogB hcomp hell hr hs hB hsize h
    by_cases hh : h.node.gap ≤ K
    · have hnon : 0 ≤ (1+epsilon w)^h.primes.length-1 := hc.1
      change |(1+epsilon w)^h.primes.length*F h.node.side (h.node.gap,h.node.ratio)-F h.node.side (h.node.gap,h.node.ratio)| ≤ _
      rw [show (1+epsilon w)^h.primes.length*F h.node.side (h.node.gap,h.node.ratio)-F h.node.side (h.node.gap,h.node.ratio) =
        ((1+epsilon w)^h.primes.length-1)*F h.node.side (h.node.gap,h.node.ratio) by ring,
        abs_mul,abs_of_nonneg hnon]
      simp only [visit,ite_eq_left hh,mul_one]
      exact mul_le_mul hc.2 (hbound _ _) (abs_nonneg _) ((hnon.trans hc.2))
    · have hf := hsupport h.node.side h.node.gap h.node.ratio (lt_of_not_ge hh)
      simp [correctedTest,primeTest,visit,hf,hh]

theorem correctedTest_bound {d w ell B A : ℝ} {start : Node}
    (F : Side → ℝ×ℝ → ℝ) (hA : 0 ≤ A) (hbound : ∀ i x,|F i x| ≤ A)
    (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) (hell : 1 ≤ ell)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B)
    (z : ChainState w ell ((Real.log B)^2) start) :
    |correctedTest F z| ≤ (1+correctionBudget d w)*A := by
  have he := history_correction hlogB hcomp hell hr hs hB hsize (History.empty : History w ell ((Real.log B)^2) start)
  have hb0 : 0 ≤ correctionBudget d w := by simpa only [History.empty,List.length_nil,pow_zero,sub_self] using he.2
  cases z with
  | none => change |(0:ℝ)| ≤ _; rw [abs_zero]; positivity
  | some h =>
    have hc := history_correction hlogB hcomp hell hr hs hB hsize h
    have hpow : 0 ≤ (1+epsilon w)^h.primes.length := pow_nonneg (normalizer_pos w).le _
    change |(1+epsilon w)^h.primes.length*F h.node.side (h.node.gap,h.node.ratio)| ≤ _
    rw [abs_mul,abs_of_nonneg hpow]
    exact mul_le_mul (by linarith : (1+epsilon w)^h.primes.length ≤ 1+correctionBudget d w)
      (hbound _ _) (abs_nonneg _) (by linarith)

theorem actual_compact_correction {d w ell B K A : ℝ} {start : Node}
    (F : Side → ℝ×ℝ → ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hbound : ∀ i x,|F i x| ≤ A)
    (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → F i (r,s)=0)
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS : (Real.log B)^2 ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ (Real.log B)^2)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10:ℝ)*B)
    (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) (N : ℕ) :
    |correctedExpectation F w ell ((Real.log B)^2) start N-primeExpectation F w ell ((Real.log B)^2) start N| ≤
      correctionBudget d w*A*(K+1) := by
  have he := history_correction hlogB hcomp hell hr hs hB hsize (History.empty : History w ell ((Real.log B)^2) start)
  have hb0 : 0 ≤ correctionBudget d w := by simpa only [History.empty,List.length_nil,pow_zero,sub_self] using he.2
  have hδ0 : 0 ≤ correctionBudget d w*A := mul_nonneg hb0 hA
  have hIC : ∀ n ∈ range N,Integrable (correctedTest F) (pathLaw w ell ((Real.log B)^2) start n) := by
    intro n _hn
    let := pathLaw_isProbability hw hell (sq_nonneg _) hS hr hs hsS n
    exact bounded_integrable (correctedTest_measurable F) (correctedTest_bound F hA hbound hlogB hcomp hell hr hs hB hsize)
  have hIP : ∀ n ∈ range N,Integrable (primeTest F) (pathLaw w ell ((Real.log B)^2) start n) := by
    intro n _hn
    let := pathLaw_isProbability hw hell (sq_nonneg _) hS hr hs hsS n
    exact bounded_integrable (primeTest_measurable F) (primeTest_bound hA hbound)
  have hdiff := finite_integral_difference (fun n => pathLaw w ell ((Real.log B)^2) start n)
    (correctedTest F) (primeTest F) N hIC hIP
  have hpoint := correction_difference_bound F hA hbound hsupport hlogB hcomp hell hr hs hB hsize
  have hsum : (∑ n ∈ range N,∫⁻ z,ENNReal.ofReal |correctedTest F z-primeTest F z| ∂pathLaw w ell ((Real.log B)^2) start n) ≤
      ENNReal.ofReal (correctionBudget d w*A)*(∑ n ∈ range N,∫⁻ z,ENNReal.ofReal (visit K z) ∂pathLaw w ell ((Real.log B)^2) start n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _hn
    calc
      _ ≤ ∫⁻ z,ENNReal.ofReal (correctionBudget d w*A)*ENNReal.ofReal (visit K z) ∂pathLaw w ell ((Real.log B)^2) start n := by
        apply lintegral_mono
        intro z
        change ENNReal.ofReal |correctedTest F z-primeTest F z| ≤ ENNReal.ofReal (correctionBudget d w*A)*ENNReal.ofReal (visit K z)
        rw [← ENNReal.ofReal_mul hδ0]
        exact ENNReal.ofReal_le_ofReal (hpoint z)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hvisit := finite_compact_visits hw hell (sq_nonneg _) hS hr hs hsS hK N
  have h := hdiff.trans (hsum.trans (mul_le_mul_of_nonneg_left hvisit zero_le))
  rw [← ENNReal.ofReal_mul hδ0] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ correctionBudget d w*A*(K+1))).mp h

end NumberTheoryLean.CompactNormalizationCorrection

end

section

namespace NumberTheoryLean.ContinuousCompactHighError

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures CompactTestGeometry CompactTestMeasurable CompactInverseTest
open RegeneratingInverseBands InvariantInverseWeights OriginalHarmonicOccupation
open ContinuousHighPartition FlaggedHarmonicTransform FiniteAdmittedOccupation
open LowStateHorizon AdmittedHarmonicPaths

noncomputable def baseReward (v : ℝ) (H : FinitePathGeometry.Side → ℝ×ℝ → ℝ) (z : CostState) : ℝ :=
  H (stateSide z.1) (gapValue v z,stateRatio z.1)

noncomputable def inverseReward (v : ℝ) (H : FinitePathGeometry.Side → ℝ×ℝ → ℝ) (z : CostState) : ℝ :=
  continuousTest v (inverseTest H) (.inl z)

theorem baseReward_measurable (v : ℝ) {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) : Measurable (baseReward v H) :=
  (continuousTest_measurable v H (fun i => (hH i).measurable)).comp measurable_inl

theorem inverseReward_measurable (v : ℝ) {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) : Measurable (inverseReward v H) :=
  (continuousTest_measurable v (inverseTest H) (fun i => (inverseTest_continuous hH i).measurable)).comp measurable_inl

theorem inverseReward_abs (v : ℝ) (H : FinitePathGeometry.Side → ℝ×ℝ → ℝ) (z : CostState) :
    ENNReal.ofReal |inverseReward v H z| = gapSquaredWeight v z*ENNReal.ofReal |baseReward v H z| := by
  have hs := stateRatio_valid z.1
  change ENNReal.ofReal |inverseTest H (stateSide z.1) (gapValue v z,stateRatio z.1)| = _
  rw [inverseTest_eq hs,← SuccessfulRewardComparison.stateWeight_eq]
  unfold gapSquaredWeight baseReward
  rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_pos (stateWeight_pos z.1),
    ← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (stateWeight_pos z.1).le)]
  congr 1
  ring

theorem phase_compact_bound {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i)) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ i x,|H i x| ≤ A := by
  obtain ⟨Ae,he⟩ := (hH .even).bounded_above_of_compact_support (hcompact .even)
  obtain ⟨Ao,ho⟩ := (hH .odd).bounded_above_of_compact_support (hcompact .odd)
  refine ⟨max 0 (max Ae Ao),le_max_left _ _,?_⟩
  intro i x
  cases i with
  | even =>
    have hx : |H .even x| ≤ Ae := by simpa only [Real.norm_eq_abs] using he x
    exact hx.trans ((le_max_left _ _).trans (le_max_right _ _))
  | odd =>
    have hx : |H .odd x| ≤ Ao := by simpa only [Real.norm_eq_abs] using ho x
    exact hx.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem compact_high_error_bound {H : FinitePathGeometry.Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {K : ℝ} (hsupport : ∀ i : FinitePathGeometry.Side,∀ r s : ℝ,K < r → H i (r,s)=0) :
    ∃ A : ℝ,0 ≤ A ∧ ∀ v ell S B : ℝ,1 ≤ ell → 0 < S → 0 < B →
      ∀ s : State,stateRatio s ≤ S → gapValue v (s,0) ≤ (23/10:ℝ)*B →
      ENNReal.ofReal |(∫ z,inverseReward v H z ∂occupation (admittedTilted v ell) (s,0))-
        (∫ z,inverseReward v H z ∂occupation (lowKernel costKernel v ell S) (s,0))| ≤
        ENNReal.ofReal ((Real.exp v)^2/stateWeight s)*ENNReal.ofReal A*
          AdmittedHighRemoval.lowHighMass v ell S (s,0) K := by
  obtain ⟨A,hA,hbase⟩ := phase_compact_bound hH hcompact
  obtain ⟨D,hD,hinverse⟩ := inverseTest_bounded hH hcompact
  refine ⟨A,hA,?_⟩
  intro v ell S B hell hS hB s hs hgap
  have hG : ∀ z : CostState,|inverseReward v H z| ≤ D := fun z => hinverse _ _
  have herr := admitted_low_signed_error v ell S B hell hS hB s hs hgap (inverseReward_measurable v hH) hG
  have hbaseM : Measurable (fun z => ENNReal.ofReal |baseReward v H z|) :=
    ENNReal.measurable_ofReal.comp (baseReward_measurable v hH).abs
  have hb : ∀ z : CostState,ENNReal.ofReal |baseReward v H z| ≤ ENNReal.ofReal A :=
    fun z => ENNReal.ofReal_le_ofReal (hbase _ _)
  have hz : ∀ z : CostState,K < gapValue v z → ENNReal.ofReal |baseReward v H z| = 0 := by
    intro z hz
    simp [baseReward,hsupport _ _ _ hz]
  have hhigh := high_inverse_compact_le v ell S s hbaseM ENNReal.ofReal_ne_top hb hz
  have he : (fun z : CostState => ENNReal.ofReal |inverseReward v H z|) =
      (fun z => gapSquaredWeight v z*ENNReal.ofReal |baseReward v H z|) := funext (inverseReward_abs v H)
  rw [he] at herr
  exact herr.trans hhigh

end NumberTheoryLean.ContinuousCompactHighError

end

section

namespace NumberTheoryLean.CorrectedCompactTransfer

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open CompactTestGeometry CompactNormalizationCorrection CompactInverseTest
open SignedCompactTransfer PrimeCorrectionFactor UniformBudgetRate LowStateHorizon

theorem source_corrected_compact_transfer (F : Side → ℝ×ℝ → ℝ)
    (hF : ∀ i,UniformContinuous (F i)) {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hbound : ∀ i x,|F i x| ≤ A) (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → F i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      |correctedExpectation F w ell S start N-
        continuousExpectation F (Real.log start.gap) ell S (FlaggedSourceStart.sourceCostState hs) N| ≤ ε := by
  obtain ⟨wP,hwP,htransfer⟩ := source_signed_compact_transfer F hF hK hA hbound hsupport d (ε/2) hd (by linarith)
  have hlimit : Tendsto (fun w : ℝ => correctionBudget d w*A*(K+1)) atTop (𝓝 0) := by
    simpa only [zero_mul] using ((correctionBudget_tendsto_zero d).mul_const A).mul_const (K+1)
  have hevent := (hlimit.eventually (eventually_le_nhds (show 0 < ε/2 by linarith))).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨wAux,hwAux⟩ := eventually_atTop.mp hevent
  refine ⟨max wP (max normalizationThreshold wAux),hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hB hlogB hcomp hr h23 hcons hsize
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  have hnorm : normalizationThreshold ≤ w := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hw
  have hwe := hwAux w ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hw)
  have hscale := source_scale_bound hwe.2 hlogB hcomp
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hsS : start.ratio ≤ S := by linarith
  have hcorrection := actual_compact_correction F hK hA hbound hsupport hnorm hell hscale.1
    hr hs hsS hB hsize hlogB hcomp N
  have hprime := htransfer w ((le_max_left _ _).trans hw) ell B start hs hell hB hlogB hcomp hr h23 hcons hsize
  have htri := abs_sub_le (correctedExpectation F w ell S start N) (primeExpectation F w ell S start N)
    (continuousExpectation F (Real.log start.gap) ell S (FlaggedSourceStart.sourceCostState hs) N)
  linarith

theorem source_inverse_compact_transfer (H : Side → ℝ×ℝ → ℝ)
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {K : ℝ} (hK : 0 ≤ K) (hsupport : ∀ i : Side,∀ r s : ℝ,K < r → H i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,∀ start : Node,∀ hs : Valid start.side start.ratio,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      0 < start.gap → start.ratio ≤ 23/10 → Consistent start → start.gap ≤ (23/10:ℝ)*B →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      |correctedExpectation (inverseTest H) w ell S start N-
        continuousExpectation (inverseTest H) (Real.log start.gap) ell S (FlaggedSourceStart.sourceCostState hs) N| ≤ ε := by
  obtain ⟨A,hA,hbound⟩ := inverseTest_bounded hH hcompact
  exact source_corrected_compact_transfer (inverseTest H) (inverseTest_uniform hH hcompact) hK hA hbound
    (inverseTest_gap_support hsupport) d ε hd hε

end NumberTheoryLean.CorrectedCompactTransfer

end

end Erdos970

end OAI
