import OAI.Probability.FreeIsing.Conditioning.InformationTransport
import OAI.Probability.FreeIsing.Gaussian.NoiseSlope

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem preBrownian_array_eval_measurePreserving
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (ι : Type*) (t : ℝ≥0) :
    MeasurePreserving (fun x : ι → Ω => fun i => B t (x i))
      (Measure.infinitePi (fun _ : ι => P)) (PlantedSymmetry.gaussianNoiseLaw ι t) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨Measurable.of_eval (fun i => (hBm t).comp (measurable_pi_apply i)), ?_⟩
  rw [Measure.infinitePi_map_pi _ (fun _ => hBm t)]
  simp only [(hB.hasLaw_eval t).map_eq, PlantedSymmetry.gaussianNoiseLaw]

theorem HasFreeIsingLaw.component_critical_information_brownian
    {d : ℕ} {theta : ℝ} {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (M : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)))
    (hM : M ≤ MeasurableSpace.prod inferInstance inferInstance)
    (hobs : ∀ u : ComponentIndex c, Measurable[M]
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        (t : ℝ) * spinSign (p.1 (componentIndexVertex u)) +
          B t (p.2 (componentIndexVertex u)))) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤
      ∫ p, (condExp M (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => P)))
        (fun q => spinSign (q.1 ⟨[c], List.IsChain.singleton c⟩)) p) ^ 2
          ∂mu.prod (Measure.infinitePi (fun _ : TreeVertex d => P)) := by
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) :=
    MeasurableSpace.prod inferInstance inferInstance
  let := hmu.isProbabilityMeasure
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let e : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    Prod.map id (fun x i => B t (x i))
  have he : MeasurePreserving e
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => P)))
      (mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id mu).prod
      (preBrownian_array_eval_measurePreserving P B hB hBm (TreeVertex d) t)
  apply hmu.component_critical_information_lower_transport hlo hhi c hcritical ht
    (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => P))) e he M hM
  have hm : Measurable[M] (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
      fun u : ComponentIndex c => (t : ℝ) * spinSign (p.1 (componentIndexVertex u)) +
        B t (p.2 (componentIndexVertex u))) := by
    let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) := M
    exact Measurable.of_eval hobs
  simpa only [PlantedInformation.observationSigma, MeasurableSpace.comap_comp,
    Function.comp_def, PlantedSymmetry.observation, e, Prod.map, id_eq] using hm.comap_le

end Problem367

end

end OAI
