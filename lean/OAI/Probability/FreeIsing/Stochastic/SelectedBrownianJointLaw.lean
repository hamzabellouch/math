import OAI.Probability.FreeIsing.Stochastic.SelectedBrownianFieldLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
open PlantedSymmetry

theorem measurePreserving_cond_preimage
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {P : Measure X} {Q : Measure Y} {T : X → Y}
    (hT : MeasurePreserving T P Q) {E : Set Y} (hE : MeasurableSet E) :
    MeasurePreserving T (P[|T ⁻¹' E]) (Q[|E]) := by
  unfold ProbabilityTheory.cond
  rw [hT.measure_preimage hE.nullMeasurableSet]
  exact (hT.restrict_preimage hE).smul_measure ((Q E)⁻¹)

theorem selectedBrownianFamily_identDistrib_gaussian_cond
    {d : ℕ} {J Ω : Type*} [Countable J] [MeasurableSpace Ω]
    {ι : J → Type*}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : (j : J) → ι j → TreeVertex d)
    (hv : ∀ j, Function.Injective (v j)) (r : J → TreeVertex d)
    (E : Set (TreeVertex d → IsingSpin)) (hE : MeasurableSet E) :
    IdentDistrib
      (fun p => (p.1, fun j => selectedBrownianField μ ν B t (v j) (r j) p))
      (fun p => (p.1, fun j => selectedGaussianField μ t (v j) (r j) p))
      ((μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[|{p | p.1 ∈ E}])
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 ∈ E}]) := by
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let Q := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    fun p => (p.1, fun i => B t (p.2 i))
  have hT : MeasurePreserving T P Q :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving
      (fun _ : TreeVertex d => ν) (fun _ => hB) (fun _ => hmB) t)
  have hTc : MeasurePreserving T (P[|{p | p.1 ∈ E}]) (Q[|{p | p.1 ∈ E}]) :=
    measurePreserving_cond_preimage hT (hE.preimage measurable_fst)
  let F := fun p => (p.1, fun j => selectedBrownianField μ ν B t (v j) (r j) p)
  let G := fun p => (p.1, fun j => selectedGaussianField μ t (v j) (r j) p)
  have hF : Measurable F := measurable_fst.prodMk
    (Measurable.of_eval (fun index =>
      measurable_selectedBrownianField μ ν hmB t (v index) (r index)))
  have hG : Measurable G := measurable_fst.prodMk
    (Measurable.of_eval (fun index => measurable_selectedGaussianField μ t (v index) (r index)))
  have heq : F =ᵐ[P] G ∘ T := by
    filter_upwards [ae_all_iff.mpr (fun j =>
      selectedBrownianField_eq_gaussian_ae μ ν hB hmB t (v j) (hv j) (r j))]
      with p hp
    exact Prod.ext rfl (funext hp)
  have heqc : F =ᵐ[P[|{p | p.1 ∈ E}]] G ∘ T :=
    cond_absolutelyContinuous.ae_le heq
  refine ⟨hF.aemeasurable, hG.aemeasurable, ?_⟩
  rw [Measure.map_congr heqc, ← Measure.map_map hG hTc.measurable, hTc.map_eq]

theorem selectedBrownianFamily_identDistrib_gaussian
    {d : ℕ} {J Ω : Type*} [Countable J] [MeasurableSpace Ω]
    {ι : J → Type*}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : (j : J) → ι j → TreeVertex d)
    (hv : ∀ j, Function.Injective (v j)) (r : J → TreeVertex d) :
    IdentDistrib
      (fun p => (p.1, fun j => selectedBrownianField μ ν B t (v j) (r j) p))
      (fun p => (p.1, fun j => selectedGaussianField μ t (v j) (r j) p))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  simpa using selectedBrownianFamily_identDistrib_gaussian_cond μ ν hB hmB
    t v hv r Set.univ MeasurableSet.univ

end Problem367

end

end OAI
