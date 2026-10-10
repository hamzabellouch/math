import OAI.Probability.SpanningForest.BrownianCanonicalPosterior
import OAI.Probability.SpanningForest.ObservedBrownianMartingale

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.CanonicalPosteriorMartingale

def observation {I Ω : Type*} (X : Ω → I → Bool)
    (B : I → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) (i : I) : ℝ :=
  (t : ℝ) * TiltLimit.bit (X ω i) + B i t ω

lemma measurable_observation {I Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → I → Bool) (hX : Measurable X) (B : I → ℝ≥0 → Ω → ℝ)
    (hBm : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (i : I) :
    Measurable (fun ω => observation X B t ω i) :=
  ((TiltLimit.continuous_bit.measurable.comp
    ((measurable_pi_apply i).comp hX)).const_mul _).add (hBm i t)

theorem martingale_nnInnovation
    {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure (I → Bool))
    (X : Ω → I → Bool) (hX : Measurable X)
    (hprior : P.map X = (μ : Measure (I → Bool)))
    (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hBcont : ∀ ω i, Continuous (fun t => B i t ω))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (hXB : IndepFun X (fun ω (p : I × ℝ≥0) => B p.1 p.2 ω) P)
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n) :
    Martingale (Innovation.nnInnovation (fun ω => TiltLimit.bit (X ω e)) (B e)
      (fun s ω => PosteriorDrift.drift μ S s
        (observation X B s.toNNReal ω) e))
      (Innovation.observationHistoryFiltration (observation X B)
        (measurable_observation X hX B hBm)) P := by
  let R : (I → Bool) → I → ℝ := fun x i => TiltLimit.bit (x i)
  have hR : Measurable R := Measurable.of_eval (fun i =>
    TiltLimit.continuous_bit.measurable.comp (measurable_pi_apply i))
  have hXI : IndepFun (R ∘ X) (fun ω i t => B i t ω) P :=
    hXB.comp hR (Measurable.of_eval (fun i =>
      Measurable.of_eval (fun t => measurable_pi_apply (i, t))))
  have hYcont : ∀ ω i, Continuous (fun t => observation X B t ω i) := by
    intro ω i
    exact (continuous_subtype_val.mul continuous_const).add (hBcont ω i)
  have hbound : ∀ t y,
      ‖PosteriorDrift.drift μ S (t : ℝ≥0) y e‖ ≤ (1 : ℝ) := by
    intro t y
    have h := PosteriorDrift.drift_mem_Icc μ S t y e
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  have hb : Measurable (Function.uncurry
      (fun (t : ℝ≥0) y => PosteriorDrift.drift μ S t y e)) := by
    let f : ℝ≥0 × (I → ℝ) → ℝ × (I → ℝ) :=
      fun p => ((p.1 : ℝ), p.2)
    have hf : Measurable f :=
      (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
    exact (PosteriorDrift.measurable_drift_coordinate μ S e).comp (f := f) hf
  have hM := Innovation.martingale_nnInnovation_of_brownian_family P
    (observation X B) (measurable_observation X hX B hBm) hYcont
    B hB hBm hI (R ∘ X) (hR.comp hX) hXI (fun _ _ _ => rfl) e
    (fun ω => by cases h : X ω e <;> simp [R, TiltLimit.bit, h])
    (fun t y => PosteriorDrift.drift μ S t y e) hb hbound
    (fun t => Observation.drift_eq_condExp_brownian_history_all_times
      P μ X hX hprior B hB hI hBm hXB S e hS hcover t)
  have heq : Innovation.nnInnovation (fun ω => TiltLimit.bit (X ω e)) (B e)
      (fun s ω => PosteriorDrift.drift μ S (s.toNNReal : ℝ)
        (observation X B s.toNNReal ω) e) =
      Innovation.nnInnovation (fun ω => TiltLimit.bit (X ω e)) (B e)
      (fun s ω => PosteriorDrift.drift μ S s
        (observation X B s.toNNReal ω) e) := by
    funext t ω
    simp only [Innovation.nnInnovation_apply]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.2
    have hs0 : 0 ≤ s := by
      simpa only [min_eq_left ht] using hs.1
    dsimp only
    rw [Real.coe_toNNReal s hs0]
  change Martingale (Innovation.nnInnovation (fun ω => TiltLimit.bit (X ω e)) (B e)
      (fun s ω => PosteriorDrift.drift μ S (s.toNNReal : ℝ)
        (observation X B s.toNNReal ω) e)) _ P at hM
  rw [heq] at hM
  exact hM

end Problem336.CanonicalPosteriorMartingale

end

end OAI
