import OAI.Probability.InvariantIsing.Cavity.CavityWeightedMoments

namespace OAI

/-! Products of a replica numerator and powers of its normalizer are
single expectations over additional replicas of the same prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_extra_replica_identity {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hw : Measurable w) (hF : Measurable F) (k : ℕ) :
    (∫ σ : Fin r → X, (∏ i, w (σ i)) * F σ ∂Measure.pi (fun _ => ν)) *
      (∫ x, w x ∂ν) ^ k =
    ∫ ξ : (Fin r ⊕ Fin k) → X, (∏ i, w (ξ i)) * F (fun i => ξ (.inl i))
      ∂Measure.pi (fun _ => ν) := by
  let f : (Fin r → X) → ℝ := fun σ => (∏ i, w (σ i)) * F σ
  let g : (Fin k → X) → ℝ := fun τ => ∏ i, w (τ i)
  have hk : (∫ x, w x ∂ν) ^ k = ∫ τ : Fin k → X, g τ ∂Measure.pi (fun _ => ν) := by
    simpa only [g, Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin k) (μ := ν) w).symm
  rw [hk, ← integral_prod_mul f g]
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin k => X)
  have hp : MeasurePreserving e (Measure.pi (fun _ : Fin r ⊕ Fin k => ν))
      ((Measure.pi (fun _ : Fin r => ν)).prod (Measure.pi (fun _ : Fin k => ν))) :=
    measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin k => ν)
  have hfg : Measurable (fun p : (Fin r → X) × (Fin k → X) => f p.1 * g p.2) := by
    apply Measurable.mul
    · exact ((Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)).mul hF).comp
        measurable_fst
    · exact (Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)).comp measurable_snd
  rw [← hp.hasLaw.integral_comp hfg.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    change ((∏ i : Fin r, w (ξ (.inl i))) * F (fun i => ξ (.inl i))) *
      (∏ j : Fin k, w (ξ (.inr j))) = _
    dsimp only
    rw [Fintype.prod_sum_type]
    ring

end InvariantIsing

end

end OAI
