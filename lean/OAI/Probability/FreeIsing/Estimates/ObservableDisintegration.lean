import OAI.Probability.FreeIsing.Conditioning.Copies
import OAI.Probability.FreeIsing.Factors.Transport

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.ObservableDisintegration

variable {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
  [StandardBorelSpace X] [Nonempty X]

def graphLaw (P : Measure X) (Z : X → W) : Measure (W × X) :=
  P.map (fun x => (Z x, x))

instance graphLaw_finite (P : Measure X) [IsFiniteMeasure P] (Z : X → W) :
    IsFiniteMeasure (graphLaw P Z) := by
  unfold graphLaw
  infer_instance

omit [StandardBorelSpace X] [Nonempty X] in
private theorem measurable_graphMap {Z : X → W} (hZ : Measurable Z) :
    Measurable (fun x => (Z x, x)) := hZ.prodMk measurable_id

def kernel (P : Measure X) [IsFiniteMeasure P] (Z : X → W) : Kernel W X :=
  (graphLaw P Z).condKernel

instance kernel_isMarkov (P : Measure X) [IsFiniteMeasure P] (Z : X → W) :
    IsMarkovKernel (kernel P Z) := by
  unfold kernel
  infer_instance

omit [StandardBorelSpace X] [Nonempty X] in
theorem fst_graphLaw (P : Measure X) {Z : X → W} (hZ : Measurable Z) :
    (graphLaw P Z).fst = P.map Z := by
  change (P.map (fun x => (Z x, x))).map Prod.fst = P.map Z
  rw [Measure.map_map measurable_fst (measurable_graphMap hZ)]
  rfl

omit [StandardBorelSpace X] [Nonempty X] in
theorem snd_graphLaw (P : Measure X) {Z : X → W} (hZ : Measurable Z) :
    (graphLaw P Z).snd = P := by
  change (P.map (fun x => (Z x, x))).map Prod.snd = P
  rw [Measure.map_map measurable_snd (measurable_graphMap hZ)]
  exact Measure.map_id

theorem compProd_kernel (P : Measure X) [IsFiniteMeasure P]
    {Z : X → W} (hZ : Measurable Z) :
    (P.map Z) ⊗ₘ kernel P Z = graphLaw P Z := by
  rw [← fst_graphLaw P hZ]
  exact Measure.disintegrate (graphLaw P Z) (graphLaw P Z).condKernel

theorem compProd_kernel_of_map_eq (P : Measure X) [IsFiniteMeasure P]
    {Z : X → W} (hZ : Measurable Z) (mu : Measure W)
    (hLaw : P.map Z = mu) : mu ⊗ₘ kernel P Z = graphLaw P Z := by
  rw [← hLaw]
  exact compProd_kernel P hZ

theorem measurePreserving_snd_kernel (P : Measure X) [IsFiniteMeasure P]
    {Z : X → W} (hZ : Measurable Z) :
    MeasurePreserving Prod.snd ((P.map Z) ⊗ₘ kernel P Z) P := by
  refine ⟨measurable_snd, ?_⟩
  rw [compProd_kernel P hZ]
  exact snd_graphLaw P hZ

theorem ae_observable_eq_input [MeasurableEq W]
    (P : Measure X) [IsFiniteMeasure P] {Z : X → W} (hZ : Measurable Z) :
    ∀ᵐ p ∂(P.map Z) ⊗ₘ kernel P Z, Z p.2 = p.1 := by
  rw [compProd_kernel P hZ]
  apply (ae_map_iff (hZ.prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun (hZ.comp measurable_snd) measurable_fst)).2
  exact Filter.Eventually.of_forall (fun _ => rfl)

omit [StandardBorelSpace X] [Nonempty X] in

theorem graphLaw_invariant (P : Measure X)
    {Z : X → W} (hZ : Measurable Z)
    {T : W → W} {S : X → X} (hT : Measurable T)
    (hS : MeasurePreserving S P P)
    (heq : ∀ᵐ x ∂P, Z (S x) = T (Z x)) :
    (graphLaw P Z).map (Prod.map T S) = graphLaw P Z := by
  apply FactorTransport.map_invariant_of_ae_equivariant hS
    (hT.prodMap hS.measurable) (hZ.prodMk measurable_id)
  filter_upwards [heq] with x hx
  exact Prod.ext hx rfl

theorem joint_kernel_invariant (P : Measure X) [IsFiniteMeasure P]
    {Z : X → W} (hZ : Measurable Z)
    {T : W → W} {S : X → X} (hT : Measurable T)
    (hS : MeasurePreserving S P P)
    (heq : ∀ᵐ x ∂P, Z (S x) = T (Z x)) :
    ((P.map Z) ⊗ₘ kernel P Z).map (Prod.map T S) =
      (P.map Z) ⊗ₘ kernel P Z := by
  rw [compProd_kernel P hZ]
  exact graphLaw_invariant P hZ hT hS heq

theorem ae_conditionalCopies_observable [MeasurableEq W]
    (P : Measure X) [IsFiniteMeasure P] {Z : X → W} (hZ : Measurable Z) :
    ∀ᵐ p ∂(P.map Z) ⊗ₘ ((kernel P Z) ×ₖ (kernel P Z)),
      Z p.2.1 = p.1 ∧ Z p.2.2 = p.1 := by
  have hf := (measurePreserving_conditionalCopy_fst (P.map Z) (kernel P Z)).quasiMeasurePreserving.ae
    (ae_observable_eq_input P hZ)
  have hs := (measurePreserving_conditionalCopy_snd (P.map Z) (kernel P Z)).quasiMeasurePreserving.ae
    (ae_observable_eq_input P hZ)
  filter_upwards [hf, hs] with p hp hq
  exact ⟨hp, hq⟩

end Problem367.ObservableDisintegration

end

end OAI
