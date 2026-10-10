import OAI.Probability.SpanningForest.BrownianBridge

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.BrownianReference

variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
  (ν : Measure A) (ρ : Measure W) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]

def coupling : Measure (A × (I → W)) := ν.prod (Measure.infinitePi (fun _ : I => ρ))

instance coupling_probability : IsProbabilityMeasure (coupling (I := I) ν ρ) := by
  unfold coupling
  infer_instance

omit [IsProbabilityMeasure ν] in
theorem hidden_hasLaw : HasLaw (fun q : A × (I → W) => q.1) ν (coupling ν ρ) :=
  measurePreserving_fst.hasLaw

theorem noise_coordinate_preserving (i : I) :
    MeasurePreserving (fun q : A × (I → W) => q.2 i) (coupling ν ρ) ρ :=
  (measurePreserving_eval_infinitePi (fun _ : I => ρ) i).comp measurePreserving_snd

theorem independent_samples :
    iIndepFun (fun (i : I) (q : A × (I → W)) => q.2 i) (coupling ν ρ) := by
  have hm : ∀ i : I, Measurable (fun q : A × (I → W) => q.2 i) :=
    fun i => (measurable_pi_apply i).comp measurable_snd
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map hm).2
  simp_rw [(noise_coordinate_preserving ν ρ _).map_eq]
  exact measurePreserving_snd.map_eq

theorem independent_processes (b : ℝ≥0 → W → ℝ) (hb : ∀ t, Measurable (b t)) :
    iIndepFun (fun (i : I) (q : A × (I → W)) t => b t (q.2 i)) (coupling ν ρ) :=
  (independent_samples ν ρ).comp (fun _ w t => b t w)
    (fun _ => Measurable.of_eval hb)

theorem hidden_independent_field (b : ℝ≥0 → W → ℝ) (hb : ∀ t, Measurable (b t)) :
    IndepFun (fun q : A × (I → W) => q.1)
      (fun q (p : I × ℝ≥0) => b p.2 (q.2 p.1)) (coupling ν ρ) := by
  have h : IndepFun (fun q : A × (I → W) => q.1) (fun q => q.2) (coupling ν ρ) :=
    indepFun_prod measurable_id measurable_id
  exact h.comp measurable_id
    (Measurable.of_eval (fun p : I × ℝ≥0 => (hb p.2).comp (measurable_pi_apply p.1)))

theorem measurable_process (b : ℝ≥0 → W → ℝ) (hb : ∀ t, Measurable (b t))
    (i : I) (t : ℝ≥0) : Measurable (fun q : A × (I → W) => b t (q.2 i)) :=
  (hb t).comp ((measurable_pi_apply i).comp measurable_snd)

theorem preBrownian_process {b : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal b ρ) (i : I) :
    IsPreBrownianReal (fun t (q : A × (I → W)) => b t (q.2 i)) (coupling ν ρ) := by
  constructor
  intro S
  exact (hB.hasLaw S).comp (noise_coordinate_preserving ν ρ i).hasLaw

theorem brownian_process {b : ℝ≥0 → W → ℝ} (hB : IsBrownianReal b ρ) (i : I) :
    IsBrownianReal (fun t (q : A × (I → W)) => b t (q.2 i)) (coupling ν ρ) where
  toIsPreBrownianReal := preBrownian_process ν ρ hB.toIsPreBrownianReal i
  cont := (noise_coordinate_preserving ν ρ i).quasiMeasurePreserving.ae hB.cont

theorem bridge_independent_hidden_endpoint (b : ℝ≥0 → W → ℝ)
    (hb : ∀ t, Measurable (b t)) (hB : IsPreBrownianReal b ρ)
    (D : A → I → ℝ) (hD : Measurable D) (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun
      (fun (q : A × (I → W)) (p : I × Set.Iic t) =>
        BrownianBridge.residual (fun s q => b s (q.2 p.1)) t p.2 q)
      (fun q => (q.1, fun i => (t : ℝ) * D q.1 i + b t (q.2 i)))
      (coupling ν ρ) := by
  exact BrownianBridge.indepFun_residual_family_hidden_endpoint
    (fun i => preBrownian_process ν ρ hB i) (independent_processes ν ρ b hb)
    (fun i s => measurable_process b hb i s) measurable_fst D hD
    (hidden_independent_field ν ρ b hb) t ht

end Problem336.BrownianReference

end

end OAI
