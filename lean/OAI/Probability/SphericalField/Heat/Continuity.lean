import Mathlib
import OAI.Probability.SphericalField.Heat.Boundary

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma heatLogBCF_time_continuousAt_all (g : Jet3) (d : ℝ≥0) (s : ℝ) :
    ContinuousAt (fun t : ℝ => heatLogBCF t.toNNReal d g.f) s := by
  by_cases hd : d = 0
  · subst d
    have he : (fun t : ℝ => heatLogBCF t.toNNReal 0 g.f) =
        (fun t => gaussianAverageBCF t.toNNReal g.f) := by ext t x; simp [heatLog]
    rw [he]
    exact (gaussianAverageBCF_time_continuous_of_deriv g.f g.d1 g.has1).continuousAt
  let A : ℝ → (ℝ →ᵇ ℝ) := fun t => gaussianAverageBCF t.toNNReal (expBCF d g.f)
  let c : ℝ := Real.exp (-(d : ℝ)*‖g.f‖)
  have hc : 0 < c := Real.exp_pos _
  have hb t : ∀ x, c ≤ A t x := fun x => (gaussianAverage_exp_bounds t.toNNReal d d.coe_nonneg g.f x).1
  have ha : ContinuousAt A s := (gaussianAverageBCF_time_continuous_of_deriv (g.exp d).f (g.exp d).d1 (g.exp d).has1).continuousAt
  have hbd t : ‖heatLogBCF t.toNNReal d g.f - heatLogBCF s.toNNReal d g.f‖ ≤
      (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change |heatLog t.toNNReal d g.f x-heatLog s.toNNReal d g.f x| ≤ _
    simp only [heatLog,hd,↓reduceIte,← mul_sub,abs_mul,abs_inv,abs_of_nonneg d.coe_nonneg]
    calc
      _ ≤ (d : ℝ)⁻¹*(c⁻¹*|A t x-A s x|) :=
        mul_le_mul_of_nonneg_left (log_lipschitz_above hc (hb s x) (hb t x)) (by positivity)
      _ ≤ (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left ((A t-A s).norm_coe_le_norm x) (by positivity)
  have ht : Tendsto (fun t => (d : ℝ)⁻¹*c⁻¹*‖A t-A s‖) (𝓝 s) (𝓝 0) := by
    simpa only [Pi.sub_apply,sub_self,norm_zero,mul_zero] using
      (ha.sub (continuousAt_const (y := A s))).norm.const_mul ((d : ℝ)⁻¹*c⁻¹) |>.tendsto
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbd ht)

lemma heatLogBCF_terminal_norm_le (s d : ℝ≥0) (f h : ℝ→ᵇ ℝ) :
    ‖heatLogBCF s d f-heatLogBCF s d h‖ ≤ ‖f-h‖ := by
  have hb (u : ℝ→ᵇ ℝ) : ‖heatTiltCLM s d u‖ ≤ 1 := by
    apply (heatTiltCLM s d u).opNorm_le_bound (by norm_num)
    intro v
    change ‖heatTiltBCF s d u v‖ ≤ 1*‖v‖
    simpa only [one_mul] using heatTiltBCF_norm_le s d u v
  simpa only [one_mul] using (convex_univ : Convex ℝ (Set.univ : Set (ℝ→ᵇ ℝ))).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u _ => (heatLogBCF_hasFDerivAt s d u).hasFDerivWithinAt)
    (fun u _ => hb u) (mem_univ h) (mem_univ f)

lemma heatLogBCF_moving_continuousAt (g : Jet3) (d : ℝ≥0)
    (s : ℝ→ℝ) (F : ℝ→(ℝ→ᵇ ℝ)) (t : ℝ)
    (hs : ContinuousAt s t) (hF : ContinuousAt F t) (he : F t = g.f) :
    ContinuousAt (fun r => heatLogBCF (s r).toNNReal d (F r)) t := by
  have hc := (heatLogBCF_time_continuousAt_all g d (s t)).comp hs
  have hb r : ‖heatLogBCF (s r).toNNReal d (F r)-heatLogBCF (s t).toNNReal d (F t)‖ ≤
      ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖ := by
    calc
      _ ≤ ‖heatLogBCF (s r).toNNReal d (F r)-heatLogBCF (s r).toNNReal d (F t)‖+
          ‖heatLogBCF (s r).toNNReal d (F t)-heatLogBCF (s t).toNNReal d (F t)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        have H := add_le_add_right (heatLogBCF_terminal_norm_le (s r).toNNReal d (F r) (F t))
          ‖heatLogBCF (s r).toNNReal d (F t)-heatLogBCF (s t).toNNReal d (F t)‖
        simpa only [he,add_comm] using H
  have hz : Tendsto (fun r => ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖) (𝓝 t) (𝓝 0) := by
    have H := ((hF.sub (continuousAt_const (y := F t))).norm.add
        (hc.sub (continuousAt_const (y := heatLogBCF (s t).toNNReal d g.f))).norm).tendsto
    change Tendsto (fun r => ‖F r-F t‖+‖heatLogBCF (s r).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖) (𝓝 t)
      (𝓝 (‖F t-F t‖+‖heatLogBCF (s t).toNNReal d g.f-heatLogBCF (s t).toNNReal d g.f‖)) at H
    simpa only [sub_self,norm_zero,zero_add] using H
  exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hb hz)

lemma parametricHeatJet_continuousAt (g : Jet3) (ps : List HeatIntervalParam) (t : ℝ)
    (hp : ∀ p ∈ ps, ContinuousAt p.duration t) :
    ContinuousAt (fun r => (parametricHeatJet g ps r).f) t := by
  induction ps with
  | nil => exact continuousAt_const
  | cons p ps ih =>
    simp only [parametricHeatJet,Jet3.heatLog_f]
    exact heatLogBCF_moving_continuousAt (parametricHeatJet g ps t) p.coefficient p.duration
      (fun r => (parametricHeatJet g ps r).f) t (hp p (List.mem_cons_self))
        (ih fun q hq => hp q (List.mem_cons_of_mem p hq)) rfl

lemma parametricHeatJet_tail_order (g : Jet3) (ps : List HeatIntervalParam)
    (hc : ∀ p ∈ ps, Continuous p.duration)
    (hp : ∀ t ∈ Ioo (0:ℝ) 1, ∀ p ∈ ps, HasDerivAt p.duration p.rate t ∧ 0 < p.duration t)
    (hend : (ps.map HeatIntervalParam.rate).sum = 0)
    (ht : ∀ t ∈ Ioo (0:ℝ) 1, ∀ zs : List (ℝ×(ℝ→ᵇ ℝ)),
      zs.IsSuffix (heatBoundaryTerms g t ps 0) → 0 ≤ (zs.map Prod.fst).sum)
    (x : ℝ) : (parametricHeatJet g ps 1).f x ≤ (parametricHeatJet g ps 0).f x := by
  have hcont : Continuous (fun t => (parametricHeatJet g ps t).f x) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (BoundedContinuousFunction.evalCLM ℝ x).continuous.continuousAt.comp
      (parametricHeatJet_continuousAt g ps t (fun p h => (hc p h).continuousAt))
  have hdiff : DifferentiableOn ℝ (fun t => (parametricHeatJet g ps t).f x) (interior (Icc (0:ℝ) 1)) := by
    rw [interior_Icc]
    intro t ht
    exact ((BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t
      (parametricHeatJet_hasDerivAt g ps t (hp t ht))).differentiableAt.differentiableWithinAt
  have hn := antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) 1) hcont.continuousOn hdiff
    (fun t h => parametricHeatJet_deriv_nonpos g t ps (hp t (by simpa only [interior_Icc] using h))
      hend (ht t (by simpa only [interior_Icc] using h)) x)
  exact hn ⟨le_rfl,zero_le_one⟩ ⟨zero_le_one,le_rfl⟩ zero_le_one

end SphericalPerceptron
end
end
end

end OAI
