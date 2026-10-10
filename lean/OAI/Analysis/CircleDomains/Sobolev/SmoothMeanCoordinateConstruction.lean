import OAI.Analysis.CircleDomains.Modulus.MeanCoordinateBudget

namespace OAI

/-! The compact arc law constructs one actual smooth masked coordinate,
with the smoothing error, original point-hit widths and full source
Stokes budget all retained from the same construction. -/

open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem exists_smooth_mean_coordinate_with_budget
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
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεfin : ε ≠ ∞) :
    ∃ (Q : SmoothMeanPeriodData hsch K hKS (η.map f) F G U S M (σ singular) π)
      (C : MaskedCoordinateData G U π σ),
      (∀ x, |Q.error x| ≤ dustSmoothingTolerance id Uᶜ δ x) ∧
      C.graph = periodBandGraph U M (σ singular) Q.patch Q.branch ∧
      C.mask = M ∧ C.singular = singular ∧
      (∀ s, C.upper s - C.lower s ≤ (η : Measure A).real {γ | σ s ∈ range γ.val}) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ S →
        C.physical (Complex.equivRealProdCLM z) = Q.physical z) ∧
      C.sourceStokesBudget R ≤
        2 * Real.sqrt Real.pi * R *
          (ε + (2 * (B : ℝ≥0∞)) * (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ)).toReal +
        2 * Real.pi * R * (countingSquareNorm w).toReal := by
  have hPU (z : ℂ) (hz : (z : Sphere) ∈ G) : π (z : Sphere) ∈ U := by
    rw [← he ⟨z, hz⟩]
    exact (e ⟨z, hz⟩).property
  obtain ⟨Q, herr, hgrad⟩ := exists_smooth_mean_period_data hsch hsep hcoarea e hG hU hS hM
    (σ singular) hbS (hσ singular) hMS y₀ π hπ he hinf A hA η hfinite g hg hocc henergy
    K hK hKS F f hf hmap B hB h0 h1 hF hinj hmiss δ hδ hδ1 hε
  let N := ε + (2 * (B : ℝ≥0∞)) * (∫⁻ p, g p ^ 2 ∂sphericalArea) ^ (1 / 2 : ℝ)
  have hN : N ≠ ∞ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨hεfin, ENNReal.mul_ne_top (by finiteness) ?_⟩
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) henergy.ne
  have hn (i : Fin 2) : eLpNorm
      (fun x => circleFDeriv Q.euclidean x (EuclideanSpace.single i 1))
      2 (volume.restrict (planeSphere ⁻¹' (G ∩ π ⁻¹' S))) ≤ N :=
    (hgrad i).2.trans (add_le_add le_rfl
      (sliceChartDensity_euclidean_eLpNorm_le B g hg henergy _))
  obtain ⟨C, hc, hm, hs, hh, hv, hb⟩ := Q.exists_coordinate_data_with_budget
    hsch hsep A K hK hKS η F f hf hmap hG hdense hS hM hboundary σ hσ singular
    (hσ singular) hMS hbS hπ hPU hfreeU h0 h1 hstrict hF (fun i => (hgrad i).1)
    hend hbudget hmissFree hR hN hn w hw hwp
  exact ⟨Q, C, herr, hc, hm, hs, hh, hv, hb⟩

end CircleDomainRigidity

end

end OAI
