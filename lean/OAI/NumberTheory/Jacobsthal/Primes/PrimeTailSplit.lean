import OAI.NumberTheory.Jacobsthal.Estimates.GrowingFarTail
import OAI.NumberTheory.Jacobsthal.Partitions.SuccessfulTailTransport

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.InitialPrimeTail

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain DerivativeWeights
open PrimeExponentialTail ExponentialMeshTail SuccessfulTailTransport

noncomputable def initialConstant : ℝ := 8/weight .even (23/10)

theorem initialConstant_pos : 0 < initialConstant :=
  div_pos (by norm_num) (weight_pos (by norm_num [Valid]))

noncomputable def initialBudget (c B : ℝ) : ℝ := (initialConstant/c^2)*Real.exp (-(c/2)*B)

theorem initialBudget_tendsto_zero {c : ℝ} (hc : 0 < c) : Tendsto (initialBudget c) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (c/2) (by linarith : 0 < c/2)
  have h' := h.const_mul (initialConstant/c^2)
  change Tendsto (fun B : ℝ => (initialConstant/c^2)*Real.exp (-(c/2)*B)) atTop (𝓝 0)
  simpa only [Real.rpow_zero,one_mul,mul_zero] using h'

theorem initial_tail_integral (w ell S c K : ℝ) (start : Node) :
    (∫⁻ z,tailReward c K z ∂pathLaw w ell S start 0) =
      tailReward c K (some (History.empty : History w ell S start)) := by
  change (∫⁻ z,tailReward c K z ∂Measure.dirac (some History.empty)) = _
  rw [lintegral_dirac' _ (measurable_of_countable _)]

theorem clean_initial_integral (w ell S c K mesh : ℝ) (start : Node) (hs : Valid start.side start.ratio) :
    (∫⁻ z,cleanReward c K z ∂CouplingData.sourceLaw w ell S start hs mesh 0) =
      tailReward c K (some (History.empty : History w ell S start)) := by
  change (∫⁻ z,cleanReward c K z ∂Measure.dirac (FlaggedSourceStart.sourceJoint w ell S start hs,false)) = _
  rw [lintegral_dirac' _ (cleanReward_measurable c K)]
  rfl

theorem source_initial_tail {w ell S B c K : ℝ} {start : Node}
    (hc : 0 < c) (hB : 0 < B) (hsize : B ≤ start.gap)
    (hi : start.side = .even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10) :
    tailReward c K (some (History.empty : History w ell S start)) ≤ ENNReal.ofReal (initialBudget c B) := by
  have hr : 0 < start.gap := hB.trans_le hsize
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hφ := weight_pos hs
  have hφend : 0 < weight .even (23/10) := weight_pos (by norm_num [Valid])
  have hmono : weight .even (23/10) ≤ weight start.side start.ratio := by
    rw [hi]
    exact TwoStepDensityBounds.weight_antitone (by change 198/100 ≤ start.ratio; linarith) (by norm_num [Valid]) h23
  have hinv := one_div_le_one_div_of_le hφend hmono
  have hraw := quadratic_exp_majorant hc hr.le
  have hexp : Real.exp (-c*start.gap/2) ≤ Real.exp (-(c/2)*B) := Real.exp_le_exp.mpr (by nlinarith)
  have hbound : start.gap^2*Real.exp (-c*start.gap)/weight start.side start.ratio ≤ initialBudget c B := by
    calc
      _ = (start.gap^2*Real.exp (-c*start.gap))*(1/weight start.side start.ratio) := by ring
      _ ≤ ((8/c^2)*Real.exp (-c*start.gap/2))*(1/weight .even (23/10)) :=
        mul_le_mul hraw hinv (by positivity) (by positivity)
      _ ≤ ((8/c^2)*Real.exp (-(c/2)*B))*(1/weight .even (23/10)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity)
      _ = _ := by unfold initialBudget initialConstant; ring
  change (if K < start.gap then ENNReal.ofReal _ else 0) ≤ _
  split_ifs
  · exact ENNReal.ofReal_le_ofReal hbound
  · exact zero_le

end NumberTheoryLean.InitialPrimeTail

end

section


namespace NumberTheoryLean.PrimeTailSplit

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling
open PersistentFailureFlag FlaggedOccupationBound PrimeExponentialTail
open SuccessfulTailTransport ModerateFailedReward InitialPrimeTail

variable {w ell S : ℝ} {start : Node}

theorem tail_split_pointwise (c K T : ℝ) (q : FlagState (JointState w ell S start)) :
    tailReward c K q.1.1 ≤ cleanReward c K q+
      selected (fun p : JointState w ell S start => moderateReward c T p.1) q+tailReward c T q.1.1 := by
  rcases q with ⟨⟨p,y⟩,b⟩
  cases b with
  | false =>
    simp only [cleanReward,selected_false,add_zero]
    exact le_add_of_nonneg_right zero_le
  | true =>
    simp only [cleanReward,Bool.true_eq_false,ite_false,selected_true,zero_add]
    cases p with
    | none => simp [tailReward,moderateReward]
    | some h =>
      by_cases hK : K < h.node.gap
      · rw [tailReward,ite_eq_left hK]
        by_cases hT : h.node.gap ≤ T
        · simp only [moderateReward,PrimeCompactVisits.visit,ite_eq_left hT,ENNReal.ofReal_one,mul_one]
          exact le_add_of_nonneg_right zero_le
        · rw [tailReward,ite_eq_left (lt_of_not_ge hT)]
          exact le_add_of_nonneg_left zero_le
      · rw [tailReward,ite_eq_right hK]
        exact zero_le

theorem finite_le_initial_plus_successors (a : ℕ → ℝ≥0∞) (N : ℕ) :
    (∑ n ∈ range N,a n) ≤ a 0+∑ n ∈ range N,a (n+1) := by
  calc
    _ ≤ ∑ n ∈ range (N+1),a n := by rw [Finset.sum_range_succ]; exact le_add_of_nonneg_right zero_le
    _ = _ := by rw [Finset.sum_range_succ']; exact add_comm _ _

private theorem add_tail_bounds {a b c x y p q : ℝ≥0∞}
    (ha : a ≤ x + p) (hc : c ≤ y + q) : a + b + c ≤ x + y + p + b + q := by
  calc
    _ ≤ (x + p) + b + (y + q) := add_le_add (add_le_add ha (le_refl b)) hc
    _ = _ := by ac_rfl

variable (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S) (hS : S ≤ (Real.log w)^3)
    (hr : 0 < start.gap) (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

include hw hell hS0 hS hr hsS in

theorem actual_finite_tail_split (c K T mesh : ℝ) (N : ℕ) :
    (∑ n ∈ range N,∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      tailReward c K (some (History.empty : History w ell S start))+
      tailReward c T (some (History.empty : History w ell S start))+
      (∑ n ∈ range N,∫⁻ q,cleanReward c K q ∂CouplingData.sourceLaw w ell S start hs mesh (n+1))+
      (∑ n ∈ range N,∫⁻ q,selected (fun p : JointState w ell S start => moderateReward c T p.1) q
        ∂CouplingData.sourceLaw w ell S start hs mesh n)+
      (∑ n ∈ range N,∫⁻ z,tailReward c T z ∂pathLaw w ell S start (n+1)) := by
  have htail (R : ℝ) : Measurable (tailReward (w:=w) (ell:=ell) (S:=S) (start:=start) c R) := measurable_of_countable _
  have hmod : Measurable (fun p : JointState w ell S start => moderateReward c T p.1) :=
    (measurable_of_countable (moderateReward c T)).comp measurable_fst
  have hone : ∀ n : ℕ,(∫⁻ z,tailReward c K z ∂pathLaw w ell S start n) ≤
      (∫⁻ q,cleanReward c K q ∂CouplingData.sourceLaw w ell S start hs mesh n)+
      (∫⁻ q,selected (fun p : JointState w ell S start => moderateReward c T p.1) q
        ∂CouplingData.sourceLaw w ell S start hs mesh n)+
      (∫⁻ z,tailReward c T z ∂pathLaw w ell S start n) := by
    intro n
    have he := CouplingData.source_prime hw hell hS0 hS hr hs hsS mesh n
    rw [← he,lintegral_map (g:=fun q : FlagState (JointState w ell S start) => q.1.1)
      (htail K) (measurable_fst.comp measurable_fst)]
    have h := lintegral_mono (μ:=CouplingData.sourceLaw w ell S start hs mesh n) (tail_split_pointwise c K T)
    rw [lintegral_add_left (f:=fun q : FlagState (JointState w ell S start) => cleanReward c K q+selected (fun p : JointState w ell S start => moderateReward c T p.1) q)
        ((cleanReward_measurable c K).add (selected_measurable hmod)),
      lintegral_add_left (cleanReward_measurable c K)] at h
    rw [← lintegral_map (g:=fun q : FlagState (JointState w ell S start) => q.1.1)
      (htail T) (measurable_fst.comp measurable_fst),he] at h
    rw [he]
    exact h
  have hclean := finite_le_initial_plus_successors
    (fun n => ∫⁻ q,cleanReward c K q ∂CouplingData.sourceLaw w ell S start hs mesh n) N
  rw [clean_initial_integral] at hclean
  have hfar := finite_le_initial_plus_successors (fun n => ∫⁻ z,tailReward c T z ∂pathLaw w ell S start n) N
  rw [initial_tail_integral] at hfar
  have hsum := Finset.sum_le_sum (s:=range N) (fun n _ => hone n)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at hsum
  exact hsum.trans (add_tail_bounds hclean hfar)

end NumberTheoryLean.PrimeTailSplit

end

end Erdos970

end OAI
