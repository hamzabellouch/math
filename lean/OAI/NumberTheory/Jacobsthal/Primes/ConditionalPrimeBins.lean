import OAI.NumberTheory.Jacobsthal.Partitions.RetainedIntervalUpper

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.PrimeCompletedIntervalUpper

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeHistories PrimeKilledChain
open RetainedIntervalUpper

variable {w ell S : ℝ} {start : Node}

def closedLiveBin (a b : ℝ) : Set (ChainState w ell S start) :=
  fun z => match z with
    | none => False
    | some h => a ≤ h.node.ratio ∧ h.node.ratio ≤ b

theorem mem_closedLiveBin_some (h : History w ell S start) (a b : ℝ) :
    some h ∈ closedLiveBin a b ↔ a ≤ h.node.ratio ∧ h.node.ratio ≤ b := Iff.rfl

theorem not_mem_closedLiveBin_none (a b : ℝ) :
    (none : ChainState w ell S start) ∉ closedLiveBin a b := by
  change ¬False
  exact not_false

theorem chain_closedBin_formula (h : History w ell S start) (a b : ℝ) :
    chain w ell S start (some h) (closedLiveBin a b) =
      ∑ p ∈ nodeChildren w ell S h.node,
        if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p ≤ b
        then childProbability w ell S start h p else 0 := by
  classical
  simp only [chain_some,completedLaw,Measure.add_apply,liveLaw,Measure.finsetSum_apply,
    Measure.smul_apply,smul_eq_mul,Measure.dirac_apply,Set.indicator,mem_closedLiveBin_some,
    not_mem_closedLiveBin_none,History.append_node,step,Pi.one_apply,mul_ite,mul_one,mul_zero,ite_false,add_zero]
  exact Finset.sum_attach _ (fun p : ℕ =>
    if a ≤ childRatio w h.node.gap p ∧ childRatio w h.node.gap p ≤ b
    then childProbability w ell S start h p else 0)

theorem chain_interval_le_tilt (h : History w ell S start) (hs : Valid h.node.side h.node.ratio) (a b : ℝ) :
    chain w ell S start (some h) (closedLiveBin a b) ≤
      ENNReal.ofReal (retainedIntervalTilt w ell S h.node.side h.node.ratio h.node.gap h.node.cutoff h.node.closed a b) := by
  classical
  rw [chain_closedBin_formula,← Finset.sum_filter]
  change (∑ p ∈ retainedInterval w ell S h.node.side h.node.ratio h.node.gap h.node.cutoff h.node.closed a b,
    childProbability w ell S start h p) ≤ _
  unfold retainedIntervalTilt
  rw [ENNReal.ofReal_sum_of_nonneg
    (s := retainedInterval w ell S h.node.side h.node.ratio h.node.gap h.node.cutoff h.node.closed a b)
    (f := fun p => primeTilt w h.node.gap h.node.side h.node.ratio p)
    (fun p hp => primeTilt_nonneg hs (Finset.mem_filter.mp hp).1)]
  apply Finset.sum_le_sum
  intro p hp
  apply ENNReal.ofReal_le_ofReal
  exact div_le_self (primeTilt_nonneg hs (Finset.mem_filter.mp hp).1) (by linarith [epsilon_pos w])

theorem prime_completed_interval_upper : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S →
      ∀ h : History w ell S start, ∀ a b : ℝ, 0 < a → a ≤ b → b-a ≤ 1 →
        chain w ell S start (some h) (closedLiveBin a b) ≤
          ENNReal.ofReal (C*(1+S)^2*((b-a)+Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w)))) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := retained_short_interval_upper
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S start hell hr hs hsS h a b ha hab hwidth
  have hv := terminal_valid hs h.admissible
  have hg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs h.admissible
  have hS := terminal_ratio_le hsS h.admissible
  exact (chain_interval_le_tilt h hv a b).trans (ENNReal.ofReal_le_ofReal
    (hbound w hw ell S h.node.side h.node.ratio h.node.gap h.node.cutoff a b h.node.closed
      hell hg hv hS ha hab hwidth))

end NumberTheoryLean.PrimeCompletedIntervalUpper



namespace NumberTheoryLean.ConditionalPrimeBins

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry PrimeTiltGeometry PrimeTiltBounds PrimeTiltMonotone
open PrimeCumulativeBound PrimeRatioBins RetainedIntervalUpper PrimeCompletedIntervalUpper
open PrimeHistories PrimeKilledChain DerivativeWeights WeightFutureIntegrals

theorem multiplier_valid_antitone {i : Side} {s a t : ℝ} (hs : Valid i s)
    (ha : Valid i.flip a) (ht : Valid i.flip t) (hat : a ≤ t) :
    multiplier i s t ≤ multiplier i s a := by
  have ha0 := valid_pos ha
  have ht0 := valid_pos ht
  have hphi := TwoStepDensityBounds.weight_antitone ha ht hat
  have hq : (t+1)/t ≤ (a+1)/a := by
    rw [add_div,div_self ht0.ne',add_div,div_self ha0.ne']
    exact add_le_add_right (one_div_le_one_div_of_le ha0 hat) 1
  have hqt : 0 ≤ (t+1)/t := by positivity
  have hqa : 0 ≤ (a+1)/a := by positivity
  have hsq : ((t+1)/t)^2 ≤ ((a+1)/a)^2 := by nlinarith
  unfold multiplier
  apply div_le_div_of_nonneg_right _ (weight_pos hs).le
  exact mul_le_mul hsq hphi (weight_pos ht).le (sq_nonneg _)

theorem retained_tilt_le_multiplier {w ell S s r cap a b : ℝ} {i : Side} {closed : Bool}
    (hw : 1 < w) (hs : Valid i s) (ha : Valid i.flip a) (hab : a ≤ b) :
    retainedIntervalTilt w ell S i s r cap closed a b ≤ multiplier i s a*closedMass w r a b := by
  classical
  let A := retainedInterval w ell S i s r cap closed a b
  have hraw : (∑ p ∈ A,(p:ℝ)⁻¹) ≤ closedMass w r a b :=
    Finset.sum_le_sum_of_subset_of_nonneg (retained_subset_closed hw (valid_pos ha) hab)
      (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  calc
    _ ≤ multiplier i s a*(∑ p ∈ A,(p:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hchild,hat,_⟩
      have hm := multiplier_valid_antitone hs ha (child_valid hs hchild) hat
      rw [primeTilt_eq_multiplier,mul_comm (multiplier i s a)]
      exact mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (Nat.cast_nonneg p))
    _ ≤ _ := mul_le_mul_of_nonneg_left hraw (multiplier_pos hs ha).le

theorem retained_conditional_bin : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ i : Side, ∀ s r cap a h : ℝ, ∀ closed : Bool,
      1 ≤ ell → 0 < r → Valid i s → Valid i.flip a → 0 < h → h ≤ 1 →
      retainedIntervalTilt w ell S i s r cap closed a (a+h) ≤
        (1+C*(a+1)*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/h)*
          h*W a*(weight i.flip a/weight i s) := by
  classical
  obtain ⟨c,C,w₀,hc,hC,hw₀,herror⟩ := closed_prime_error
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S i s r cap a h closed hell hr hs ha hh hh1
  have ha0 := valid_pos ha
  have hma := (multiplier_pos hs ha).le
  let A := retainedInterval w ell S i s r cap closed a (a+h)
  let e := Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))
  by_cases hne : A.Nonempty
  · have hlow := short_interval_lower_exponent hell hs ha0 (by linarith : a ≤ a+h)
      (by linarith : a+h-a ≤ 1) hne
    have herr := herror w hw r a (a+h) hr ha0 (by linarith) hlow
    have hlog := (bin_log_width_bounds ha0 (show a ≤ a+h by linarith)).2
    have hraw : closedMass w r a (a+h) ≤ h/(a+1)+C*e := by
      rw [add_sub_cancel_left] at hlog
      linarith [(abs_le.mp herr).2]
    calc
      _ ≤ multiplier i s a*closedMass w r a (a+h) := retained_tilt_le_multiplier (hw₀.trans_le hw) hs ha (by linarith)
      _ ≤ multiplier i s a*(h/(a+1)+C*e) := mul_le_mul_of_nonneg_left hraw hma
      _ = _ := by
        unfold multiplier W
        dsimp only [e]
        field_simp [hh.ne',ha0.ne',(weight_pos hs).ne']
  · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (∑ p ∈ A,_) ≤ _
    rw [hempty,Finset.sum_empty]
    have hW := (W_pos ha0).le
    have hratio := (div_pos (weight_pos ha) (weight_pos hs)).le
    positivity

variable {w ell S : ℝ} {start : Node}

theorem actual_conditional_bin : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell S : ℝ, ∀ start : Node,
      1 ≤ ell → 0 < start.gap → Valid start.side start.ratio →
      ∀ g : History w ell S start, ∀ a h : ℝ, Valid g.node.side.flip a → 0 < h → h ≤ 1 →
      chain w ell S start (some g) (ActualPrimeBins.liveBin a (a+h)) ≤
        ENNReal.ofReal ((1+C*(a+1)*Real.exp (-c*Real.sqrt ((1/2:ℝ)*Real.log w))/h)*
          h*W a*(weight g.node.side.flip a/weight g.node.side g.node.ratio)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hbound⟩ := retained_conditional_bin
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro w hw ell S start hell hr hs g a h ha hh hh1
  have hv := terminal_valid hs g.admissible
  have hg := terminal_gap_positive (show 0 ≤ ell by linarith) hr hs g.admissible
  have hsubset : ActualPrimeBins.liveBin a (a+h) ⊆ (closedLiveBin (w:=w) (ell:=ell) (S:=S) (start:=start) a (a+h)) := by
    intro p hp
    cases p with
    | none => exact False.elim hp
    | some p => exact ⟨hp.1,hp.2.le⟩
  exact (measure_mono hsubset).trans ((chain_interval_le_tilt g hv a (a+h)).trans
    (ENNReal.ofReal_le_ofReal (hbound w hw ell S g.node.side g.node.ratio g.node.gap g.node.cutoff a h g.node.closed
      hell hg hv ha hh hh1)))

end NumberTheoryLean.ConditionalPrimeBins


end Erdos970

end OAI
