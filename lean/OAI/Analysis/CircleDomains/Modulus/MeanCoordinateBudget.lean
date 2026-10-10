import OAI.Analysis.CircleDomains.Selection.MeanCoordinateData
import OAI.Analysis.CircleDomains.Modulus.SourceStokesBudgetEstimate
import OAI.Analysis.CircleDomains.Probability.SliceDensityNorm

namespace OAI

/-! The original smoothed mean, with its quantitative source Stokes
budget retained through physical coordinate assembly. -/

open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

theorem SmoothMeanPeriodData.exists_coordinate_data_with_budget
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (A : Set C(PathTime, Sphere)) (K : Set C(PathTime, ℂ))
    (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet) (η : ProbabilityMeasure A)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    {G U S M : Set Sphere} (hG : IsOpen G) (hdense : Dense U)
    (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U)
    (singular : T) (hbU : σ singular ∉ U)
    (hMS : M \ {σ singular} ⊆ S) (hbS : σ singular ∉ S)
    {π : Sphere → Sphere} (hπ : Continuous π)
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S))
    (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M (σ singular) π)
    (henergy : ∀ i : Fin 2, MemLp (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))))
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (hmiss : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map f : Measure K), F x ∉ range γ.val)
    {R : ℝ} (hR : 0 ≤ R) {N : ℝ≥0∞} (hN : N ≠ ∞)
    (hnorm : ∀ i : Fin 2,
      eLpNorm (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
        2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) ≤ N)
    (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
    (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s) :
    ∃ C : MaskedCoordinateData G U π σ,
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      C.sourceStokesBudget R ≤ 2 * Real.sqrt Real.pi * R * N.toReal +
        2 * Real.pi * R * (countingSquareNorm w).toReal := by
  obtain ⟨C, hg, hm, hs, hwidth, hv, hn⟩ := Q.exists_coordinate_data_with_norms
    hsch hsep A K hK hKS η F f hf hmap hG hdense hS hM hboundary σ hσ singular hbU hMS hbS
    hπ hPU hfreeU h0 h1 hstrict hF henergy hend hbudget hmiss
  refine ⟨C, hg, hm, hs, hwidth, hv, ?_⟩
  apply C.sourceStokesBudget_le hπ hR hN (fun i => (hn i).trans (hnorm i))
    w Subtype.val Subtype.val_injective _ hw
  intro s
  have hs' : (s : T) ≠ singular := by simpa only [hs] using s.property
  calc
    ENNReal.ofReal (C.upper s - C.lower s) ≤
        ENNReal.ofReal ((η : Measure A).real {γ | σ s ∈ range γ.val}) :=
      ENNReal.ofReal_le_ofReal (hwidth s)
    _ = (η : Measure A) {γ | σ s ∈ range γ.val} := ofReal_measureReal (measure_ne_top _ _)
    _ ≤ w s := hwp s hs'

end CircleDomainRigidity

end

end OAI
