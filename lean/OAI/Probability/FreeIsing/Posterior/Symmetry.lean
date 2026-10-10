import OAI.Probability.FreeIsing.Conditioning.Naturality
import OAI.Probability.FreeIsing.Posterior.PlantedSymmetry

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367.PlantedSymmetry

def plantedFlipEquiv (ι : Type*) :
    ((ι → IsingSpin) × (ι → ℝ)) ≃ᵐ ((ι → IsingSpin) × (ι → ℝ)) where
  toFun := Prod.map flipConfig Neg.neg
  invFun := Prod.map flipConfig Neg.neg
  left_inv := by
    rintro ⟨sigma, noise⟩
    change (flipConfig (flipConfig sigma), - -noise) = (sigma, noise)
    simp
  right_inv := by
    rintro ⟨sigma, noise⟩
    change (flipConfig (flipConfig sigma), - -noise) = (sigma, noise)
    simp
  measurable_toFun := measurable_flipConfig.prodMap measurable_neg
  measurable_invFun := measurable_flipConfig.prodMap measurable_neg

@[implicit_reducible] def observationSigma (ι : Type*) (t : ℝ) :
    MeasurableSpace ((ι → IsingSpin) × (ι → ℝ)) :=
  MeasurableSpace.comap (observation t) inferInstance

theorem observationSigma_le (ι : Type*) (t : ℝ) :
    observationSigma ι t ≤ (inferInstance : MeasurableSpace ((ι → IsingSpin) × (ι → ℝ))) :=
  (measurable_observation t).comap_le

theorem measurable_plantedFlip_observationSigma (ι : Type*) (t : ℝ) :
    Measurable[observationSigma ι t, observationSigma ι t] (plantedFlipEquiv ι) := by
  apply measurable_comap_iff.mpr
  have heq : observation t ∘ plantedFlipEquiv ι = fun p => -observation t p := by
    funext p
    exact observation_flip t p
  rw [heq]
  exact (comap_measurable (observation t)).neg

theorem integrable_plantedSpin {ι : Type*}
    (rho : Measure ((ι → IsingSpin) × (ι → ℝ))) [IsFiniteMeasure rho] (v : ι) :
    Integrable (fun p => spinSign (p.1 v)) rho := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  apply Integrable.of_bound
    ((hsign.comp ((measurable_pi_apply v).comp measurable_fst)).aestronglyMeasurable) 1
  apply Filter.Eventually.of_forall
  intro p
  cases hs : p.1 v <;> norm_num [spinSign, hs]

def posteriorMagnetization {ι : Type*}
    (rho : Measure ((ι → IsingSpin) × (ι → ℝ))) (t : ℝ) (v : ι) :
    ((ι → IsingSpin) × (ι → ℝ)) → ℝ :=
  rho[fun p => spinSign (p.1 v) | observationSigma ι t]

theorem measurable_posteriorMagnetization {ι : Type*}
    (rho : Measure ((ι → IsingSpin) × (ι → ℝ))) (t : ℝ) (v : ι) :
    Measurable (posteriorMagnetization rho t v) := by
  exact stronglyMeasurable_condExp.measurable.mono (observationSigma_le ι t) le_rfl

theorem posteriorMagnetization_abs_le_one {ι : Type*}
    (rho : Measure ((ι → IsingSpin) × (ι → ℝ))) (t : ℝ) (v : ι) :
    ∀ᵐ p ∂rho, |posteriorMagnetization rho t v p| ≤ 1 := by
  apply ae_bdd_abs_condExp_of_ae_bdd_abs
  apply Filter.Eventually.of_forall
  intro p
  cases hs : p.1 v <;> norm_num [spinSign, hs]

theorem posteriorMagnetization_flip_ae {ι : Type*}
    {mu : Measure (ι → IsingSpin)} {nu : Measure (ι → ℝ)}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu.map flipConfig = mu) (hnu : nu.map Neg.neg = nu) (t : ℝ) (v : ι) :
    (posteriorMagnetization (mu.prod nu) t v) ∘ plantedFlipEquiv ι =ᵐ[mu.prod nu]
      -posteriorMagnetization (mu.prod nu) t v := by
  have hnat := condExp_comp_measurePreserving_equiv
    (observationSigma_le ι t) (plantedFlipEquiv ι)
    (product_measurePreserving_flip hmu hnu)
    (measurable_plantedFlip_observationSigma ι t)
    (measurable_plantedFlip_observationSigma ι t)
    (integrable_plantedSpin (mu.prod nu) v)
  have hodd : (fun p : (ι → IsingSpin) × (ι → ℝ) => spinSign (p.1 v)) ∘
      plantedFlipEquiv ι = -(fun p : (ι → IsingSpin) × (ι → ℝ) => spinSign (p.1 v)) := by
    funext p
    cases hs : p.1 v <;>
      simp [plantedFlipEquiv, flipConfig, IsingSpin.flip, spinSign, hs]
  rw [hodd] at hnat
  exact hnat.trans (condExp_neg _ _)

theorem posteriorMagnetizationLaw_neg_invariant {ι : Type*}
    {mu : Measure (ι → IsingSpin)} {nu : Measure (ι → ℝ)}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu.map flipConfig = mu) (hnu : nu.map Neg.neg = nu) (t : ℝ) (v : ι) :
    ((mu.prod nu).map (posteriorMagnetization (mu.prod nu) t v)).map Neg.neg =
      (mu.prod nu).map (posteriorMagnetization (mu.prod nu) t v) := by
  exact FactorTransport.map_invariant_of_ae_equivariant
    (product_measurePreserving_flip hmu hnu) measurable_neg
    (measurable_posteriorMagnetization (mu.prod nu) t v)
    (posteriorMagnetization_flip_ae hmu hnu t v)

theorem freeIsing_gaussian_posteriorLaw_neg_invariant {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (t : ℝ) (variance : NNReal) (v : TreeVertex d) :
    (((mu.prod (gaussianNoiseLaw (TreeVertex d) variance)).map
      (posteriorMagnetization (mu.prod (gaussianNoiseLaw (TreeVertex d) variance)) t v)).map
        Neg.neg) =
      (mu.prod (gaussianNoiseLaw (TreeVertex d) variance)).map
        (posteriorMagnetization (mu.prod (gaussianNoiseLaw (TreeVertex d) variance)) t v) := by
  let : IsFiniteMeasure mu :=
    hmu.finite_of_connected (ConnectedHull.hull ∅) (ConnectedHull.connected_hull ∅)
  exact posteriorMagnetizationLaw_neg_invariant hmu.flip_invariant
    (gaussianNoiseLaw_map_neg (TreeVertex d) variance) t v

end Problem367.PlantedSymmetry

end

end OAI
