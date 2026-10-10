import OAI.NumberTheory.Jacobsthal.Paths.ActualFlaggedCompact

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SourceCompactOccupation

open _root_.Set _root_.Filter _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeBinMembership
open PrimeCompactVisits PrimeCompactWeights PrimeCorrectionFactor
open FlaggedOccupationBound PersistentFailureFlag ActualProcessCoupling ActualFlaggedCompact

variable {w ell S B : ℝ} {start : Node}

noncomputable def compactReward (K w B : ℝ) {ell S : ℝ} (start : Node)
    (z : ChainState w ell S start) : ℝ≥0∞ :=
  ENNReal.ofReal (scaledWeight w B start z*visit K z)

theorem literal_scaled_weight (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (h : History w ell S start) :
    B^2*ErdosPrimeInputs.PrimePrefixMass.prefixWeight h.primes =
      (pathLaw w ell S start h.primes.length {some h}).toReal*scaledWeight w B start (some h) := by
  rw [PrimeChainProbabilities.source_prime_weight_identity hell hr hs h]
  unfold scaledWeight
  ring

theorem compact_reward_envelope {K D : ℝ}
    (hbound : ∀ h : History w ell S start,h.node.gap ≤ K → scaledWeight w B start (some h) ≤ D)
    (z : ChainState w ell S start) :
    compactReward K w B start z ≤ ENNReal.ofReal D*ENNReal.ofReal (visit K z) := by
  cases z with
  | none => simp [compactReward,visit]
  | some h =>
    by_cases hh : h.node.gap ≤ K
    · simpa only [compactReward,visit,ite_eq_left hh,mul_one,ENNReal.ofReal_one]
        using ENNReal.ofReal_le_ofReal (hbound h hh)
    · simp [compactReward,visit,hh]

theorem finite_reward_envelope {K D : ℝ}
    (hbound : ∀ h : History w ell S start,h.node.gap ≤ K → scaledWeight w B start (some h) ≤ D)
    (N : ℕ) :
    (∑ n ∈ range N, ∫⁻ z,compactReward K w B start z ∂pathLaw w ell S start n) ≤
      ENNReal.ofReal D*(∑ n ∈ range N, ∫⁻ z,ENNReal.ofReal (visit K z) ∂pathLaw w ell S start n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _hn
  calc
    _ ≤ ∫⁻ z,ENNReal.ofReal D*ENNReal.ofReal (visit K z) ∂pathLaw w ell S start n :=
      lintegral_mono (compact_reward_envelope hbound)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem finite_selected_reward_envelope {K D mesh : ℝ} (hs : Valid start.side start.ratio)
    (hbound : ∀ h : History w ell S start,h.node.gap ≤ K → scaledWeight w B start (some h) ≤ D)
    (N : ℕ) :
    (∑ n ∈ range N, ∫⁻ z,selected (fun q : JointState w ell S start => compactReward K w B start q.1) z
      ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
      ENNReal.ofReal D*(∑ n ∈ range N, ∫⁻ z,selected (compactVisit K) z
        ∂CouplingData.sourceLaw w ell S start hs mesh n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _hn
  calc
    _ ≤ ∫⁻ z,ENNReal.ofReal D*selected (compactVisit K) z ∂CouplingData.sourceLaw w ell S start hs mesh n := by
      apply lintegral_mono
      rintro ⟨q,b⟩
      cases b with
      | false => simp only [selected_false,mul_zero,le_refl]
      | true => simpa only [selected_true,compactVisit] using compact_reward_envelope hbound q.1
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem source_compact_occupation (K : ℝ) (hK : 3 ≤ K) (d : ℝ) (_hd : 0 < d) :
    ∃ C w₀ : ℝ, 0 < C ∧ 1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ ell B : ℝ,
      ∀ start : Node,∀ hs : Valid start.side start.ratio,
      1 ≤ ell → ell ≤ B → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      Consistent start → start.cutoff = B →
      let S := (Real.log B)^2
      (∀ N : ℕ,(∑ n ∈ range N, ∫⁻ z,compactReward K w B start z ∂pathLaw w ell S start n) ≤ ENNReal.ofReal C) ∧
      (∀ mesh : ℝ,∀ N : ℕ,
        (∑ n ∈ range N, ∫⁻ z,selected (fun q : JointState w ell S start => compactReward K w B start q.1) z
          ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
          ENNReal.ofReal C*CouplingData.sourceLaw w ell S start hs mesh N failed) := by
  have hDK := compactConstant_pos hK
  have hevent := ((correctionBudget_tendsto_zero d).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))).and
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2)))
  obtain ⟨W,hW⟩ := eventually_atTop.mp hevent
  refine ⟨compactConstant K*(K+1),max normalizationThreshold W,by positivity,
    normalizationThreshold_gt_one.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hs hell hellB hB hlogB hcomp hi h199 h23 hc hcut
  dsimp only
  have hnorm : normalizationThreshold ≤ w := (le_max_left _ _).trans hw
  have hwe := hW w ((le_max_right _ _).trans hw)
  have hscale := UniformBudgetRate.source_scale_bound hwe.2 hlogB hcomp
  have hS0 : 0 ≤ (Real.log B)^2 := sq_nonneg _
  have hS3 : 3 ≤ (Real.log B)^2 := by nlinarith
  have hsS : start.ratio ≤ (Real.log B)^2 := by linarith
  have he : start.gap = B*start.ratio := by
    have hh : start.cutoff = start.gap/start.ratio := hc
    rw [hcut] at hh
    exact ((eq_div_iff (valid_pos hs).ne').mp hh).symm
  have hr : 0 < start.gap := by rw [he]; exact mul_pos hB (valid_pos hs)
  have hbound := scaled_compact_bound hK hB hell hellB hlogB hcomp hwe.1 hi h199 h23 hc hcut
  have hprod : ENNReal.ofReal (compactConstant K)*ENNReal.ofReal (K+1) =
      ENNReal.ofReal (compactConstant K*(K+1)) := (ENNReal.ofReal_mul hDK.le).symm
  constructor
  · intro N
    refine (finite_reward_envelope hbound N).trans ?_
    calc
      _ ≤ ENNReal.ofReal (compactConstant K)*ENNReal.ofReal (K+1) :=
        mul_le_mul_of_nonneg_left (finite_compact_visits hnorm hell hS0 hscale.1 hr hs hsS (K := K) (by linarith) N) zero_le
      _ = _ := hprod
  · intro mesh N
    refine (finite_selected_reward_envelope hs hbound N).trans ?_
    calc
      _ ≤ ENNReal.ofReal (compactConstant K)*(ENNReal.ofReal (K+1)*
          CouplingData.sourceLaw w ell ((Real.log B)^2) start hs mesh N failed) :=
        mul_le_mul_of_nonneg_left (actual_flagged_compact_visits hnorm hell hS0 hscale.1 hr hs hsS (K := K) (by linarith) mesh N) zero_le
      _ = _ := by rw [← mul_assoc,hprod]

end NumberTheoryLean.SourceCompactOccupation

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeChainHorizon
open PrimeCompactWeights SourceCompactOccupation
open ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}

theorem singleton_off_stage (n : ℕ) (h : History w ell S start) (hne : h.primes.length ≠ n) :
    pathLaw w ell S start n {some h} = 0 := by
  have hsub : ({some h} : Set (ChainState w ell S start)) ⊆ {z | ¬stage n z} := by
    intro z hz
    have he : z = some h := hz
    subst z
    exact hne
  exact measure_mono_null hsub (ae_iff.mp (pathLaw_stage n))

noncomputable def listReward (F : List ℕ → ℝ) : ChainState w ell S start → ℝ
  | none => 0
  | some h => F h.primes

theorem singleton_scaled_reward (hell : 0 ≤ ell) (hr : 0 < start.gap)
    (hs : Valid start.side start.ratio) (n : ℕ) (h : History w ell S start)
    (F : List ℕ → ℝ) :
    (pathLaw w ell S start n).real {some h} *
      (scaledWeight w B start (some h)*F h.primes) =
      if n = h.primes.length then B^2*prefixWeight h.primes*F h.primes else 0 := by
  classical
  by_cases hn : n = h.primes.length
  · rw [ite_eq_left hn,hn,measureReal_def]
    rw [← mul_assoc,← literal_scaled_weight hell hr hs h]
  · rw [ite_eq_right hn,measureReal_def,singleton_off_stage n h (Ne.symm hn)]
    simp

theorem finite_signed_original_occupation (hw : normalizationThreshold ≤ w)
    (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (F : List ℕ → ℝ) :
    (∑ n ∈ range (LowStateHorizon.sourceHorizon S B),
      ∫ z,scaledWeight w B start z*listReward F z ∂pathLaw w ell S start n) =
      B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps) := by
  classical
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell := ell) (S := S) hw1 start
  have hterm (n : ℕ) :
      (∫ z,scaledWeight w B start z*listReward F z ∂pathLaw w ell S start n) =
        ∑ h : History w ell S start,
          if n = h.primes.length then B^2*prefixWeight h.primes*F h.primes else 0 := by
    let := pathLaw_isProbability hw hell hS0 hS hr hs hsS n
    rw [integral_fintype Integrable.of_finite,Fintype.sum_option]
    simp only [scaledWeight,listReward,mul_zero,smul_zero,zero_add]
    apply Finset.sum_congr rfl
    intro h _hh
    exact singleton_scaled_reward (by linarith) hr hs n h F
  simp_rw [hterm]
  rw [Finset.sum_comm]
  have hlen (h : History w ell S start) : h.primes.length ∈ range (LowStateHorizon.sourceHorizon S B) :=
    mem_range.mpr (PrimeHistoryHorizon.history_length_lt hell hS0 hr hs hB hsize h)
  simp only [Finset.sum_ite_eq',hlen,ite_true]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [mul_assoc] using sum_histories hw1 start (fun ps => prefixWeight ps*F ps)

end NumberTheoryLean.PrimeFamilyOccupation

end

section

namespace NumberTheoryLean.PrimeFamilyOccupation
open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeCompactWeights
open ErdosPrimeInputs.PrimePrefixMass

variable {w ell S B : ℝ} {start : Node}

theorem listReward_nonneg (F : List ℕ → ℝ)
    (hF : ∀ ps,allowed w ell S start ps → 0 ≤ F ps) (z : ChainState w ell S start) :
    0 ≤ listReward F z := by
  cases z with
  | none => exact le_rfl
  | some h => exact hF h.primes h.admissible

theorem finite_nonnegative_original_occupation (hw : normalizationThreshold ≤ w)
    (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)
    (hB : 0 < B) (hsize : start.gap ≤ (23/10 : ℝ)*B) (F : List ℕ → ℝ)
    (hF : ∀ ps,allowed w ell S start ps → 0 ≤ F ps) :
    (∑ n ∈ range (LowStateHorizon.sourceHorizon S B),
      ∫⁻ z,ENNReal.ofReal (scaledWeight w B start z*listReward F z) ∂pathLaw w ell S start n) =
      ENNReal.ofReal (B^2*(∑ ps ∈ retainedPrefixes w ell S start,prefixWeight ps*F ps)) := by
  classical
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell := ell) (S := S) hw1 start
  have hnon (z : ChainState w ell S start) : 0 ≤ scaledWeight w B start z*listReward F z :=
    mul_nonneg (scaledWeight_nonneg hs z) (listReward_nonneg F hF z)
  rw [← finite_signed_original_occupation hw hell hS0 hS hr hs hsS hB hsize F]
  rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => integral_nonneg hnon)]
  apply Finset.sum_congr rfl
  intro n _hn
  let := pathLaw_isProbability hw hell hS0 hS hr hs hsS n
  exact (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (Filter.Eventually.of_forall hnon)).symm

end NumberTheoryLean.PrimeFamilyOccupation

end

end Erdos970

end OAI
