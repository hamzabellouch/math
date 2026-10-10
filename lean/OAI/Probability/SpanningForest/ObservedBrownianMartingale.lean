import OAI.Probability.SpanningForest.InnovationAdapted
import OAI.Probability.SpanningForest.BrownianFamilyPast

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace Problem336.Innovation

def observationHistoryFiltration {I Ω : Type*} {mΩ : MeasurableSpace Ω}
    (Y : ℝ≥0 → Ω → I → ℝ) (hY : ∀ t i, Measurable (fun ω => Y t ω i)) :
    Filtration ℝ≥0 mΩ where
  seq t := MeasurableSpace.comap (fun ω (p : I × Iic t) => Y p.2 ω p.1) inferInstance
  mono' := by
    intro u v huv
    let restrict : (I × Iic v → ℝ) → (I × Iic u → ℝ) :=
      fun f p => f (p.1, ⟨p.2, p.2.2.trans huv⟩)
    have hr : Measurable restrict := by fun_prop
    have heq : (fun ω (p : I × Iic u) => Y p.2 ω p.1) =
        restrict ∘ (fun ω (p : I × Iic v) => Y p.2 ω p.1) := rfl
    dsimp only
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hr.comap_le
  le' t := (Measurable.of_eval (fun p : I × Iic t => hY p.2 p.1)).comap_le

theorem measurable_observationHistoryFiltration {I Ω : Type*}
    {mΩ : MeasurableSpace Ω} (Y : ℝ≥0 → Ω → I → ℝ)
    (hY : ∀ t i, Measurable (fun ω => Y t ω i)) (t : ℝ≥0) (i : I) :
    Measurable[observationHistoryFiltration (mΩ := mΩ) Y hY t] (fun ω => Y t ω i) := by
  exact (measurable_pi_apply ((i, ⟨t, by simp⟩) : I × Iic t)).comp
    (comap_measurable (fun ω (p : I × Iic t) => Y p.2 ω p.1))

theorem martingale_nnInnovation_of_brownian_family
    {I Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (Y : ℝ≥0 → Ω → I → ℝ)
    (hYmeas : ∀ t i, Measurable (fun ω => Y t ω i))
    (hYcont : ∀ ω i, Continuous (fun t => Y t ω i))
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (X : Ω → I → ℝ) (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (hobs : ∀ t ω i, Y t ω i = (t : ℝ) * X ω i + B i t ω)
    (i : I) (hXbound : ∀ ω, X ω i ∈ Icc (0 : ℝ) 1)
    (b : ℝ≥0 → (I → ℝ) → ℝ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hbound : ∀ t y, ‖b t y‖ ≤ C)
    (hposterior : ∀ t : ℝ≥0, (fun ω => b t (Y t ω)) =ᵐ[P]
      P[(fun ω => X ω i) | observationHistoryFiltration Y hYmeas t]) :
    Martingale (nnInnovation (fun ω => X ω i) (B i)
      (fun s ω => b s.toNNReal (Y s.toNNReal ω)))
      (observationHistoryFiltration Y hYmeas) P := by
  classical
  let : IsProbabilityMeasure P := hI.isProbabilityMeasure
  have hXi : Integrable (fun ω => X ω i) P :=
    Integrable.of_bound ((measurable_pi_apply i).comp hX).aestronglyMeasurable 1 (by
      apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hXbound ω).1]
      exact (hXbound ω).2)
  have hnoise : ∀ u v : ℝ≥0, u ≤ v → ∀ A : Set Ω,
      MeasurableSet[observationHistoryFiltration Y hYmeas u] A →
      (∫ ω in A, (B i v ω - B i u ω) ∂P) = 0 := by
    intro u v huv A hA
    have hA' : MeasurableSet[MeasurableSpace.comap
        (fun ω (p : I × Iic u) => (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω)
        inferInstance] A := by
      change MeasurableSet[MeasurableSpace.comap
        (fun ω (p : I × Iic u) => Y p.2 ω p.1) inferInstance] A at hA
      have hhist : (fun ω (p : I × Iic u) => Y p.2 ω p.1) =
          (fun ω (p : I × Iic u) => (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) := by
        funext ω p
        exact hobs p.2 ω p.1
      rw [hhist] at hA
      exact hA
    have hz := BrownianFamilyPast.setIntegral_weighted_increment_observation_eq_zero
      hB hBm hI hX hXB {i} (fun _ => (1 : ℝ)) u (v - u) hA'
    simpa only [Finset.sum_singleton, one_mul, add_tsub_cancel_of_le huv] using hz
  have heq : nnInnovation (fun ω => X ω i) (B i)
      (fun s ω => b s.toNNReal (Y s.toNNReal ω)) =
      (fun t ω => Y t ω i -
        ∫ s in (0 : ℝ)..t, b s.toNNReal (Y s.toNNReal ω)) := by
    funext t ω
    rw [nnInnovation_apply, hobs]
  rw [heq]
  exact martingale_borel_observation P (observationHistoryFiltration Y hYmeas)
    Y hYcont (measurable_observationHistoryFiltration Y hYmeas) i
    (fun ω => X ω i) (B i) (fun t ω => hobs t ω i) hXi
    (fun t => (hB i).integrable_eval t) b hb hbound hposterior hnoise

end Problem336.Innovation

end

end OAI
