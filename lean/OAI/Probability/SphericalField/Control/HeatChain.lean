import Mathlib
import OAI.Probability.SphericalField.Control.Backward

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
inductive HeatChain (m : Trial) (g : Jet3) : Time → Time → Jet3 → Prop
  | nil (a : Time) : HeatChain m g a a g
  | cons {a t b : Time} {h : Jet3} (d : ℝ≥0) (hat : a < t) (htb : t ≤ b)
      (hm : ∀ r ∈ Set.Ioc a t, m r = (d : ℝ)) (tail : HeatChain m g t b h) :
      HeatChain m g a b (h.heatLog (timeSpan a t) d)

lemma HeatChain.left_le_right {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) : a ≤ b := by
  cases H with
  | nil => exact le_rfl
  | cons _ hat htb _ _ => exact hat.le.trans htb

lemma controls_equal_prefix {m : Trial} {v w : Time → BrownianPath → ℝ} {a b r : Time}
    (h : ∀ t ∉ Set.Ioc a b, ∀ ω, w t ω = v t ω) (hr : r ≤ a) (ω : BrownianPath) :
    controlledPrefix m w r ω = controlledPrefix m v r ω := by
  unfold controlledPrefix
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t ht
  dsimp only
  rw [h t (fun hh => not_lt_of_ge (ht.trans hr) hh.1) ω]

lemma controls_equal_cost_prefix {m : Trial} {v w : Time → BrownianPath → ℝ} {a b r s : Time}
    (h : ∀ t ∉ Set.Ioc a b, ∀ ω, w t ω = v t ω) (hr : r ≤ a) (ω : BrownianPath) :
    intervalControlCost m w s r ω = intervalControlCost m v s r ω := by
  unfold intervalControlCost
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [h t (fun hh => not_lt_of_ge (ht.2.trans hr) hh.1) ω]

lemma HeatChain.upper {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    {v : Time → BrownianPath → ℝ} (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L) :
    (∫ ω, g.f (controlledPrefix m v b ω) ∂P) -
      (∫ ω, intervalControlCost m v a b ω ∂P)/2 ≤
        (∫ ω, h.f (controlledPrefix m v a ω) ∂P) := by
  induction H with
  | nil a => simp [intervalControlCost]
  | @cons a t b h d hat htb hm tail ih =>
    have hi := brownian_control_interval_upper P hB m L d hv hL hat.le hm h
    have hc := expected_intervalControlCost_add P m L hv hL hat.le htb
    rw [Jet3.heatLog_f]
    simp only [heatLogBCF_coe]
    linarith only [ih,hi,hc]

lemma HeatChain.lower {m : Trial} {g h : Jet3} {a b : Time}
    (H : HeatChain m g a b h) (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (L : ℝ≥0)
    (v : Time → BrownianPath → ℝ) (hv : Progressive P v) (hL : ∀ r ω, |v r ω| ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ≥0, ∃ w : Time → BrownianPath → ℝ, Progressive P w ∧ (∀ r ω, |w r ω| ≤ K) ∧
      (∀ r ∉ Set.Ioc a b, ∀ ω, w r ω = v r ω) ∧
      (∫ ω, h.f (controlledPrefix m v a ω) ∂P) - ε ≤
        (∫ ω, g.f (controlledPrefix m w b ω) ∂P) -
          (∫ ω, intervalControlCost m w a b ω ∂P)/2 := by
  induction H generalizing v L ε with
  | nil a =>
    refine ⟨L,v,hv,hL,fun _ _ _ => rfl,?_⟩
    simp only [intervalControlCost,Set.Ioc_self,Measure.restrict_empty,integral_zero_measure,
      integral_zero,zero_div,sub_zero]
    linarith
  | @cons a t b h d hat htb hm tail ih =>
    obtain ⟨K,u,hu,huK,huout,huval⟩ :=
      brownian_control_interval_lower P hB m d L h hat hm v hv hL (by positivity : 0 < ε/2)
    obtain ⟨K',w,hw,hwK,hwout,hwval⟩ := ih K u hu huK (by positivity : 0 < ε/2)
    have hc := expected_intervalControlCost_add P m K' hw hwK hat.le htb
    have he : ∀ ω, intervalControlCost m w a t ω = intervalControlCost m u a t ω :=
      controls_equal_cost_prefix hwout le_rfl
    simp only [he] at hc
    refine ⟨K',w,hw,hwK,?_,?_⟩
    · intro r hr ω
      rw [hwout r (fun hh => hr ⟨hat.trans hh.1,hh.2⟩) ω]
      exact huout r (fun hh => hr ⟨hh.1,hh.2.trans htb⟩) ω
    · rw [Jet3.heatLog_f]
      simp only [heatLogBCF_coe]
      linarith only [huval,hwval,hc]

lemma controlledPrefix_one (m : Trial) (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    controlledPrefix m v 1 ω = brownianEval 1 ω + controlDrift m v ω := by
  simp only [controlledPrefix,controlDrift,show Set.Iic (1 : Time) = Set.univ from Set.Iic_top,
    Measure.restrict_univ]
  rfl

lemma controlledPrefix_zero (P : Measure BrownianPath) (hB : IsBrownianReal brownianEval P)
    (m : Trial) (v : Time → BrownianPath → ℝ) : controlledPrefix m v 0 =ᵐ[P] fun _ => 0 := by
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  simp only [controlledPrefix,show Set.Iic (0 : Time) = {0} from Set.Iic_bot,
    Measure.restrict_singleton,measure_singleton,zero_smul,integral_zero_measure,add_zero]
  exact hω

lemma intervalControlCost_full (m : Trial) (v : Time → BrownianPath → ℝ)
    (ω : BrownianPath) (hm : Measurable (v · ω)) :
    intervalControlCost m v 0 1 ω = (pathControlCost m v ω).toReal := by
  unfold intervalControlCost
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := timeLaw)), show Set.Icc (0 : Time) 1 = Set.univ from Set.Icc_bot_top,
    Measure.restrict_univ]
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun r => mul_nonneg (m.nonneg r) (sq_nonneg _))
    ((m.measurable.mul (hm.pow_const 2)).aestronglyMeasurable)

end SphericalPerceptron
end
end

end OAI
