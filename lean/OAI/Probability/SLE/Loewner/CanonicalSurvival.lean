import OAI.Probability.SLE.Geometry.CanonicalBoundaryLimit

namespace OAI

/-! The measurable canonical trace has exactly the raw surviving domain,
simultaneously for every time and point. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance survivalComplexMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance survivalComplexBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
local instance survivalDriverPolish : PolishSpace Target.Driver :=
  ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace
local instance survivalDriverMetric : MetricSpace Target.Driver :=
  TopologicalSpace.metrizableSpaceMetric Target.Driver

lemma ae_canonical_survival
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (Ψ : Target.Driver → C(ℝ≥0,ℂ)) (hΨ : Measurable Ψ)
    (hΨeq : ∀ ω, Ψ (Target.normalizedDriver κ B hc h0 ω)=sourceTracePath γ (fun ω => (hw ω).1) ω) :
    ∀ᵐ b ∂W, ∀ (T : ℝ≥0) (z : ℂ),
      Target.Surviving κ b z (κ*T) ↔ z ∈ survivingDomain (Ψ b) T := by
  have : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let p (r : ℝ≥0 × ℂ) (b : Target.Driver) :=
    Target.Surviving κ b r.2 (κ.toNNReal*r.1) ↔ r.2 ∈ survivingDomain (Ψ b) r.1
  have hA : MeasurableSet {q : (ℝ≥0 × ℂ) × Target.Driver |
      Target.Surviving κ q.2 q.1.2 (κ.toNNReal*q.1.1)} := by
    have hmA : Measurable (fun q : (ℝ≥0 × ℂ) × Target.Driver =>
        (κ.toNNReal*q.1.1,(q.2,q.1.2))) :=
      (measurable_const.mul measurable_fst.fst).prodMk
        (measurable_snd.prodMk measurable_fst.snd)
    exact MeasurableSet.preimage
      (f := fun q : (ℝ≥0 × ℂ) × Target.Driver => (κ.toNNReal*q.1.1,(q.2,q.1.2)))
      (Target.measurableSet_surviving κ) hmA
  have hD : MeasurableSet {q : (ℝ≥0 × ℂ) × Target.Driver |
      q.1.2 ∈ survivingDomain (Ψ q.2) q.1.1} := by
    have hmD : Measurable (fun q : (ℝ≥0 × ℂ) × Target.Driver => ((Ψ q.2,q.1.1),q.1.2)) :=
      (((hΨ.comp measurable_snd).prodMk measurable_fst.fst).prodMk measurable_fst.snd)
    exact MeasurableSet.preimage
      (f := fun q : (ℝ≥0 × ℂ) × Target.Driver => ((Ψ q.2,q.1.1),q.1.2))
      source_survival_open.measurableSet hmD
  have hp : MeasurableSet {q : (ℝ≥0 × ℂ) × Target.Driver | p q.1 q.2} := by
    convert (hA.inter hD).union (hA.compl.inter hD.compl) using 1
    ext q
    simp only [p,mem_union,mem_inter_iff,mem_compl_iff,mem_ofPred_eq]
    tauto
  have hLaw := Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW
  have hsource : ∀ᵐ ω ∂P, ∀ r, p r (Target.normalizedDriver κ B hc h0 ω) := by
    apply ae_of_all
    rintro ω ⟨T,z⟩
    have he : (Ψ (Target.normalizedDriver κ B hc h0 ω) : ℝ≥0 → ℂ)=γ ω := by
      funext t
      have h := congrArg (fun e : C(ℝ≥0,ℂ) => e t) (hΨeq ω)
      simpa only [sourceTracePath,ContinuousMap.coe_mk] using h
    change Target.Surviving κ _ z (κ.toNNReal*T) ↔ z ∈ survivingDomain _ T
    rw [Real.coe_toNNReal _ hκ.le,he]
    exact Target.surviving_iff_witness κ hκ _ _ _ _ _ (hw ω)
      (Target.normalizedDriver_matches κ hκ B hc h0 ω) T z
  have hall := ae_forall_parameter_of_hasLaw hLaw p hp hsource
  filter_upwards [hall] with b hb T z
  simpa only [p,NNReal.coe_mul,Real.coe_toNNReal _ hκ.le] using hb (T,z)

end SLEExactGauge

end

end OAI
