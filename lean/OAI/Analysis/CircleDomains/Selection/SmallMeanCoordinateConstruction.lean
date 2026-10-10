import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanCoordinateConstruction
import OAI.Analysis.CircleDomains.Modulus.SmallMeanBudget

namespace OAI

/-! Arbitrarily small compact-law norms produce the actual masked
coordinate with a strictly small full Stokes budget. -/

open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem exists_smooth_mean_coordinate_with_small_budget
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcoarea : PlanarLipschitzFiberCoarea)
    {G U S M : Set Sphere} (e : G ≃ₜ U) (hG : IsOpen G) (hU : IsOpen U)
    (hdense : Dense U) (hS : IsOpen S) (hM : IsClosed M) (hboundary : frontier M ⊆ U)
    {T : Type*} (σ : T → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : T)
    (hbS : σ singular ∉ S) (hMS : M \ {σ singular} ⊆ S) (y₀ : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (hfreeU : π '' Gᶜ ⊆ Uᶜ) (hinf : π OnePoint.infty ∉ S)
    (A : Set C(PathTime, Sphere)) (hA : ∀ γ ∈ A, Injective γ)
    (η : ProbabilityMeasure A) (hfinite : ∀ γ ∈ A, physicalDomainLength e y₀ γ < ∞)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ (η.map Subtype.val) = sphericalArea.withDensity g)
    (henergy : (∫⁻ p, g p ^ 2 ∂sphericalArea) < ∞)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (F : C(Sphere, ℂ)) (f : A → K) (hf : Measurable f)
    (hmap : ∀ γ : A, (f γ).val = F.comp γ.val)
    (B : ℝ≥0) (hB : LipschitzOnWith B finiteCoord
      (((↑) : ℂ → Sphere) '' (((↑) : ℂ → Sphere) ⁻¹' G ∩
        (fun z : ℂ => π (z : Sphere)) ⁻¹' S)))
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1)
    (hstrict : ∀ x ∈ M \ U, ‖F x‖ < 1)
    (hF : ∀ γ : A, InjOn F (range γ.val ∪ S)) (hinj : InjOn F S)
    (hmiss : ∀ x ∈ U ∩ S, ∀ᵐ γ : A ∂(η : Measure A), x ∉ range γ.val)
    (hmissFree : ∀ x ∈ ((π '' Gᶜ) \ range σ) ∩ S,
      ∀ᵐ γ : K ∂(η.map f : Measure K), F x ∉ range γ.val)
    (hend : ∀ γ : A, σ singular ∈ range γ.val)
    (hbudget : Summable (fun s => ((η : Measure A).real {γ | σ s ∈ range γ.val}) ^ 2))
    (w : T → ℝ≥0∞) (hw : (∑' t, w t ^ 2) < ∞)
    (hwp : ∀ s, s ≠ singular → (η : Measure A) {γ | σ s ∈ range γ.val} ≤ w s)
    {R : ℝ} (hR : 0 ≤ R)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsmall : (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ) + countingSquareNorm w <
      meanBudgetTolerance B R ξ) :
    ∃ (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M (σ singular) π)
      (C : MaskedCoordinateData G U π σ),
      (∀ x, |Q.error x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      C.sourceStokesBudget R < ξ := by
  obtain ⟨Q, C, herr, hc, hm, hs, hh, hv, hb⟩ := exists_smooth_mean_coordinate_with_budget
    hsch hsep hcoarea e hG hU hdense hS hM hboundary σ hσ singular hbS hMS y₀ π hπ he
    hfreeU hinf A hA η hfinite g hg hocc henergy K hK hKS F f hf hmap B hB h0 h1
    hstrict hF hinj hmiss hmissFree hend hbudget w hw hwp hR δ hδ hδ1
    (meanBudgetTolerance_pos B hR hξ) (meanBudgetTolerance_ne_top B R ξ)
  exact ⟨Q, C, herr, hc, hm, hs, hh, hv,
    hb.trans_lt (mean_budget_lt_of_small_norms B hR hξ hsmall)⟩

end CircleDomainRigidity

end

end OAI
