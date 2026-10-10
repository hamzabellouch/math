import OAI.Probability.FreeIsing.Posterior.PlantedStationarity
import OAI.Probability.FreeIsing.Posterior.Symmetry

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367.PosteriorStationarity

open PlantedSymmetry PlantedStationarity

variable {d : ℕ}

def plantedRelabelEquiv (g : TreeAut d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) ≃ᵐ
      ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) where
  toFun := Prod.map (relabel g) (relabel g)
  invFun := fun p => (fun v => p.1 (g.toEquiv v), fun v => p.2 (g.toEquiv v))
  left_inv := by
    rintro ⟨sigma, noise⟩
    apply Prod.ext <;> funext v <;> simp [relabel]
  right_inv := by
    rintro ⟨sigma, noise⟩
    apply Prod.ext <;> funext v <;> simp [relabel]
  measurable_toFun := (measurable_relabel g).prodMap (measurable_relabel g)
  measurable_invFun := by
    apply Measurable.prodMk <;>
      exact Measurable.of_eval (fun _ => (measurable_pi_apply _).comp
        (by fun_prop))

theorem measurable_plantedRelabel_observationSigma (g : TreeAut d) (t : ℝ) :
    Measurable[observationSigma (TreeVertex d) t,
      observationSigma (TreeVertex d) t] (plantedRelabelEquiv g) := by
  apply measurable_comap_iff.mpr
  have heq : observation t ∘ plantedRelabelEquiv g = relabel g ∘ observation t := rfl
  rw [heq]
  exact (measurable_relabel g).comp (comap_measurable (observation t))

theorem measurable_plantedRelabel_symm_observationSigma (g : TreeAut d) (t : ℝ) :
    Measurable[observationSigma (TreeVertex d) t,
      observationSigma (TreeVertex d) t] (plantedRelabelEquiv g).symm := by
  apply measurable_comap_iff.mpr
  have heq : observation t ∘ (plantedRelabelEquiv g).symm =
      (fun x v => x (g.toEquiv v)) ∘ observation t := rfl
  rw [heq]
  exact (Measurable.of_eval (fun _ => measurable_pi_apply _)).comp
    (comap_measurable (observation t))

theorem posteriorMagnetization_relabel_ae {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (t : ℝ) (g : TreeAut d)
    (v : TreeVertex d) :
    posteriorMagnetization (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      t v ∘ plantedRelabelEquiv g =ᵐ[mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))]
    posteriorMagnetization (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      t (g.toEquiv.symm v) := by
  let := hmu.isProbabilityMeasure
  exact condExp_comp_measurePreserving_equiv
    (observationSigma_le (TreeVertex d) t) (plantedRelabelEquiv g)
    (measurePreserving_planted_relabel hmu nu g)
    (measurable_plantedRelabel_observationSigma g t)
    (measurable_plantedRelabel_symm_observationSigma g t)
    (integrable_plantedSpin (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) v)

def posteriorArray (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)))
    (t : ℝ) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : TreeVertex d → ℝ :=
  fun v => posteriorMagnetization rho t v p

theorem measurable_posteriorArray
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))) (t : ℝ) :
    Measurable (posteriorArray rho t) :=
  Measurable.of_eval (fun v => measurable_posteriorMagnetization rho t v)

theorem posteriorArray_relabel_ae {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (t : ℝ) (g : TreeAut d) :
    posteriorArray (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) t ∘
      plantedRelabelEquiv g =ᵐ[mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))]
    relabel g ∘ posteriorArray (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) t := by
  filter_upwards [ae_all_iff.mpr (fun v => posteriorMagnetization_relabel_ae hmu nu t g v)]
    with p hp
  exact funext hp

theorem posteriorArrayLaw_relabel {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure ℝ) [IsProbabilityMeasure nu] (t : ℝ) (g : TreeAut d) :
    ((mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map
      (posteriorArray (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) t)).map
      (relabel g) =
    (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))).map
      (posteriorArray (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) t) := by
  exact FactorTransport.map_invariant_of_ae_equivariant
    (measurePreserving_planted_relabel hmu nu g) (measurable_relabel g)
    (measurable_posteriorArray _ t) (posteriorArray_relabel_ae hmu nu t g)

end Problem367.PosteriorStationarity

end

end OAI
