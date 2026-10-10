import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCutoff

namespace OAI

/-! A random cutoff changes bounded replica tests by its discarded
one-replica probability, after averaging over the common disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_cutoff_replica_abs_le {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F| ≤ M := by
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F]
  have h := norm_integral_le_of_norm_le_const
    (μ := cond (Measure.pi (fun _ : Fin 2 => ν.tilted H)) (univ.pi (fun _ => s)))
    (f := F) (C := M) (ae_of_all _ (fun σ => by
      simpa only [Real.norm_eq_abs] using hF σ))
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_of_le_one_right hM measureReal_le_one)

theorem cavity_random_cutoff_error {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hmH : Measurable H)
    (hiH : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω, x))) ν)
    (s : Ω → Set X) (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hmF : Measurable F)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ ω σ, |F (ω, σ)| ≤ M) :
    |(∫ ω, cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω) (fun σ => F (ω, σ)) ∂P) -
      (∫ ω, referenceReplicaMean ν (fun x => H (ω, x)) (fun σ => F (ω, σ)) ∂P)| ≤
      4 * M * ∫ ω, referenceReplicaMean ν (fun x => H (ω, x))
        (fun σ : Fin 2 → X => if σ 0 ∈ (s ω)ᶜ then 1 else 0) ∂P := by
  have hms (ω : Ω) : MeasurableSet (s ω) := hs.preimage measurable_prodMk_left
  have hmcut := measurable_cavityCutoffReplicaMean ν H hmH s hs F hmF
  have hmfull := measurable_referenceReplicaMean ν (H := H) hmH hmF
  have hmTail : Measurable (fun ω => referenceReplicaMean ν (fun x => H (ω, x))
      (fun σ : Fin 2 → X => if σ 0 ∈ (s ω)ᶜ then (1 : ℝ) else 0)) := by
    apply measurable_referenceReplicaMean ν (H := H)
      (D := fun p : Ω × (Fin 2 → X) => if p.2 0 ∈ (s p.1)ᶜ then 1 else 0) hmH
    exact Measurable.ite ((hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).compl)
      measurable_const measurable_const
  have hic : Integrable (fun ω =>
      cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω) (fun σ => F (ω, σ))) P :=
    Integrable.of_bound hmcut.aestronglyMeasurable M (hiH.mono fun ω hω => by
      simpa only [Real.norm_eq_abs] using
        cavity_cutoff_replica_abs_le ν _ hω _ (hms ω) _ hM (hF ω))
  have hif : Integrable (fun ω => referenceReplicaMean ν (fun x => H (ω, x))
      (fun σ => F (ω, σ))) P := Integrable.of_bound hmfull.aestronglyMeasurable M
    (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs] using referenceReplicaMean_abs_le ν _ _
        (measurable_of_countable _) hM (hF ω))
  have hit : Integrable (fun ω => referenceReplicaMean ν (fun x => H (ω, x))
      (fun σ : Fin 2 → X => if σ 0 ∈ (s ω)ᶜ then (1 : ℝ) else 0)) P :=
    Integrable.of_bound hmTail.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      apply referenceReplicaMean_abs_le ν _ _ (measurable_of_countable _) zero_le_one
      intro σ
      split_ifs <;> norm_num)
  rw [← integral_sub hic hif]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae (hic.sub hif).norm (hit.const_mul _)
  filter_upwards [hiH] with ω hω
  rw [Real.norm_eq_abs, cavity_reference_tail_eq ν _ hω _ (hms ω)]
  exact cavity_cutoff_replica_error ν _ hω _ (hms ω) _ hM (hF ω)

end InvariantIsing

end

end OAI
