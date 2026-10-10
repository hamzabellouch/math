import OAI.NumberTheory.Jacobsthal.Paths.QuantitativeOrdinaryHit

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.InitialRegeneration
open NumberTheoryLean.FirstHitKernels NumberTheoryLean.TransitionKernels

abbrev RawInitialPackedTrace (a : ℕ) := Σ k : ℕ, RawHistory ((a+1)+2*k)

def packRawInitialEven (a : ℕ) : RawInitialEvenTrace a → RawInitialPackedTrace a
  | Sum.inl h => @Sigma.mk ℕ (fun k => RawHistory ((a+1)+2*k)) 0 h
  | Sum.inr r => @Sigma.mk ℕ (fun k => RawHistory ((a+1)+2*k)) (r.1+1) r.2

lemma packRawInitialEven_measurable (a : ℕ) : Measurable (packRawInitialEven a) := by
  apply Measurable.sumElim
  · exact measurableSigmaMk (X := fun k : ℕ => RawHistory ((a+1)+2*k)) 0
  · apply measurable_sigma_family
    intro n
    exact measurableSigmaMk (X := fun k : ℕ => RawHistory ((a+1)+2*k)) (n+1)

noncomputable def packedInitialKernel (a : ℕ) : Kernel (RawHistory a) (RawInitialPackedTrace a) :=
  (rawInitialEvenKernel a).map (packRawInitialEven a)

instance packedInitialKernel_isFiniteKernel (a : ℕ) : IsFiniteKernel (packedInitialKernel a) := by
  unfold packedInitialKernel
  infer_instance

noncomputable def packedInitialEndpoint (a : ℕ) (r : RawInitialPackedTrace a) : CostState :=
  rawLast ((a+1)+2*r.1) r.2

lemma packedInitialEndpoint_measurable (a : ℕ) : Measurable (packedInitialEndpoint a) := by
  apply measurable_sigma_family
  intro k
  exact rawLast_measurable _

lemma packedInitialEndpoint_pack (a : ℕ) (r : RawInitialEvenTrace a) :
    packedInitialEndpoint a (packRawInitialEven a r)=rawInitialEndpointState a r := by
  cases r with
  | inl h => rfl
  | inr r => rfl

theorem packedInitial_endpoint_law (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    (packedInitialKernel a h).map (packedInitialEndpoint a)=(delayedRegeneration s).map embedOdd := by
  rw [packedInitialKernel,Kernel.map_apply _ (packRawInitialEven_measurable a),
    Measure.map_map (packedInitialEndpoint_measurable a) (packRawInitialEven_measurable a)]
  have he : packedInitialEndpoint a ∘ packRawInitialEven a=rawInitialEndpointState a :=
    funext (packedInitialEndpoint_pack a)
  rw [he,rawInitialEven_endpoint a h s hs]

lemma packedInitial_ae_regeneration (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) :
    ∀ᵐ r ∂packedInitialKernel a h, packedInitialEndpoint a r ∈ regenerationSet := by
  apply (ae_map_iff (packedInitialEndpoint_measurable a).aemeasurable regenerationSet_measurable).mp
  rw [packedInitial_endpoint_law a h s hs]
  apply (ae_map_iff embedOdd_measurable.aemeasurable regenerationSet_measurable).mpr
  exact delayedRegeneration_ae_regeneration s

lemma packedInitial_mass_one (a : ℕ) (h : RawHistory a) (s : EvenState)
    (hs : rawLast a h=(Sum.inl s,0)) : packedInitialKernel a h univ=1 := by
  rw [packedInitialKernel,Kernel.map_apply' _ (packRawInitialEven_measurable a) _ MeasurableSet.univ,preimage_univ]
  exact rawInitialEven_mass_one a h s hs

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
