import OAI.Probability.FreeIsing.Trees.RootComponentAttenuation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

theorem condExp_attenuation_le_critical_relabel_root_others
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (g : TreeAut d)
    {B : Type*} [mB : MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (G : NoisyRootOtherData ℝ c → B) (hG : Measurable G)
    (shift : B → ℝ) (hs : Measurable shift) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let X := (G ∘ noisyRootOtherArray c) ∘ Prod.map (relabel g) (relabel g)
    let Q := selectedPosterior P (fun s z => (t : ℝ) * spinSign s + z)
      (fun i => g.toEquiv.symm (componentIndexVertex (c := c) i))
      (g.toEquiv.symm (RootedBroadcast.branchRoot c))
    ∀ᵐ w ∂P,
      (P[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
        1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    Prod.map (relabel g) (relabel g)
  let X := G ∘ noisyRootOtherArray (A := ℝ) c
  let f := fun v => responseAttenuation theta
    (shift (X v) + statisticMessage theta (posteriorMean μ c t v)) ^ 2
  have hX : Measurable X := hG.comp (measurable_noisyRootOtherArray c)
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have hfm : Measurable f :=
    ((continuous_responseAttenuation hθsq).measurable.comp
      ((hs.comp hX).add ((measurable_statisticMessage theta).comp
        (measurable_posteriorMean μ c t)))).pow_const 2
  have hfi : Integrable f P := by
    apply (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hpos := responseAttenuation_pos hθsq
      (shift (X v) + statisticMessage theta (posteriorMean μ c t v))
    have hle := responseAttenuation_le_one hθsq
      (shift (X v) + statisticMessage theta (posteriorMean μ c t v))
    dsimp only [f]
    nlinarith
  have hmp : MeasurePreserving T P P :=
    PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g
  have hCE := condExp_comp_measurePreserving P P T hmp (mB.comap X) hX.comap_le hfi
  have hbase := hmp.quasiMeasurePreserving.ae
    (condExp_attenuation_le_critical_root_others hμ hθ0 hθ1 c hcritical ht G hG shift hs)
  have hchannel : Measurable (Function.uncurry
      (fun s z => (t : ℝ) * spinSign s + z)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hpost := selectedPosterior_relabel_ae hμ (gaussianReal 0 t) hchannel
    (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) g
  have hfc : f ∘ T =ᵐ[P] fun v => responseAttenuation theta
      (shift ((X ∘ T) v) + statisticMessage theta
        (selectedPosterior P (fun s z => (t : ℝ) * spinSign s + z)
          (fun i => g.toEquiv.symm (componentIndexVertex (c := c) i))
          (g.toEquiv.symm (RootedBroadcast.branchRoot c)) v)) ^ 2 := by
    filter_upwards [hpost] with v hv
    exact congrArg (fun q => responseAttenuation theta
      (shift ((X ∘ T) v) + statisticMessage theta q) ^ 2) hv
  have hcongr := condExp_congr_ae (m := mB.comap (X ∘ T)) hfc
  rw [MeasurableSpace.comap_comp] at hCE
  filter_upwards [hCE, hcongr, hbase] with w hw hc hb
  exact hc.symm.trans_le (hw.trans_le hb)

end Problem367.ComponentSignalAttenuation

end

end OAI
