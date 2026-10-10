import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaLaw

namespace OAI

/-! Bounded finite-prefix integration while retaining the same disorder
that determines both the Gibbs kernel and the spectral projection. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_disorder_replica_prefix_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) {C : ℝ}
    (hbound : ∀ p, ‖F p‖ ≤ C) :
    (∫ p, F (p.1, fun i : Fin r => p.2 i) ∂disorderReplicaLaw P ν hν) =
      ∫ ω, ∫ σ, F (ω, σ) ∂Measure.pi (fun _ : Fin r => ν ω) ∂P := by
  have hm : Measurable (fun p : Ω × (ℕ → X) => F (p.1, fun i : Fin r => p.2 i)) :=
    hF.comp (measurable_fst.prodMk (Measurable.of_eval fun i =>
      (measurable_pi_apply (i : ℕ)).comp measurable_snd))
  have hi : Integrable (fun p : Ω × (ℕ → X) => F (p.1, fun i : Fin r => p.2 i))
      (disorderReplicaLaw P ν hν) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => hbound _)
  rw [disorderReplicaLaw, Measure.integral_compProd hi]
  apply integral_congr_ae
  exact ae_of_all _ fun ω =>
    (HasLaw.mk ((Measurable.of_eval fun i : Fin r => measurable_pi_apply (i : ℕ)).aemeasurable)
      (replica_prefix_map (ν ω) r)).integral_comp
      (hF.comp measurable_prodMk_left).aestronglyMeasurable


lemma cavity_disorder_replica_prefix_swap {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (Q : Measure U) [IsProbabilityMeasure Q] {r : ℕ}
    (G : (Ω × (Fin r → X)) × U → ℝ) (hG : Measurable G) {C : ℝ}
    (hb : ∀ p, ‖G p‖ ≤ C) :
    (∫ ω, ∫ u, ∫ σ, G ((ω, σ), u) ∂Measure.pi (fun _ : Fin r => ν ω) ∂Q ∂P) =
      ∫ p, ∫ u, G ((p.1, fun i : Fin r => p.2 i), u) ∂Q ∂disorderReplicaLaw P ν hν := by
  let H : Ω × (Fin r → X) → ℝ := fun p => ∫ u, G (p, u) ∂Q
  have hH : Measurable H := hG.stronglyMeasurable.integral_prod_right'.measurable
  have hHb p : ‖H p‖ ≤ C := by
    simpa only [H, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := Q) (ae_of_all _ fun u => hb (p, u)))
  have hp := cavity_disorder_replica_prefix_integral P ν hν H hH hHb
  change _ = ∫ p, H (p.1, fun i : Fin r => p.2 i) ∂disorderReplicaLaw P ν hν
  rw [hp]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    have hm : Measurable (fun p : (Fin r → X) × U => G ((ω, p.1), p.2)) :=
      hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hi : Integrable (fun p : (Fin r → X) × U => G ((ω, p.1), p.2))
        ((Measure.pi (fun _ : Fin r => ν ω)).prod Q) :=
      (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => hb ((ω, p.1), p.2))
    exact (integral_integral_swap hi).symm

lemma cavity_disorder_replica_prefix_swap_raw {Ω X U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace U]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (Q : Measure U) [IsProbabilityMeasure Q] {r : ℕ}
    (G : (Ω × U) × (Fin r → X) → ℝ) (hG : Measurable G) {C : ℝ}
    (hb : ∀ p, ‖G p‖ ≤ C) :
    (∫ ω, ∫ u, ∫ σ, G ((ω, u), σ) ∂Measure.pi (fun _ : Fin r => ν ω) ∂Q ∂P) =
      ∫ p, ∫ u, G ((p.1, u), fun i : Fin r => p.2 i) ∂Q ∂disorderReplicaLaw P ν hν := by
  exact cavity_disorder_replica_prefix_swap P ν hν Q
    (fun p => G ((p.1.1, p.2), p.1.2))
    (hG.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))
    (fun p => hb ((p.1.1, p.2), p.1.2))

end InvariantIsing

end

end OAI
