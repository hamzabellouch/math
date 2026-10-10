import OAI.Geometry.RCD.Transport.MeetingSpliceOptimality
import OAI.Geometry.RCD.Transport.CompressedPlanMixture

namespace OAI

/-! # Conditional meeting pairs collapse by forward and backward nonbranching -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem contacting_pair_collapse (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    {φ ψ : X → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsProbabilityMeasure σ]
    (hl : σ.map Prod.fst=π) (hr : σ.map Prod.snd=π)
    (t : Time) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (hmeet : ∀ᵐ z ∂σ, z.1 t=z.2 t) : ∀ᵐ z ∂σ, z.1=z.2 := by
  let τ := σ.map (meetingSplice t)
  obtain ⟨hgτ,hτ₀,hτ₁,hpτ⟩ := meeting_splice_optimal π hg hp hφ hψ had hcontact σ hl hr t ht0 ht1 hmeet
  let ξ := (2:ℝ≥0∞)⁻¹ • (π+τ)
  obtain ⟨hprob,hgξ,hpξ,hπξ,hτξ⟩ := half_mixture_plan_data π τ hg hgτ hp hpτ
  let : IsProbabilityMeasure ξ := hprob
  let B : ℝ≥0 := C+C
  have hB : 0 < B := add_pos hC hC
  have hBe : ENNReal.ofReal B=ENNReal.ofReal C+ENNReal.ofReal C :=
    ENNReal.ofReal_add C.coe_nonneg C.coe_nonneg
  have hcπ (u : Time) : π.map (fun γ => γ u) ≤ ENNReal.ofReal B • hausdorff n X := by
    rw [hBe,add_smul]
    exact (hc u).trans (Measure.le_add_right le_rfl)
  have hcτ (u : Time) : τ.map (fun γ => γ u) ≤ ENNReal.ofReal B • hausdorff n X := by
    rw [hBe,add_smul]
    have h := meetingSplice_compression t u σ
    rw [hl,hr] at h
    exact h.trans (add_le_add (hc u) (hc u))
  have hcξ (u : Time) : ξ.map (fun γ => γ u) ≤ ENNReal.ofReal B • hausdorff n X :=
    half_mixture_compression (hausdorff n X) π τ hcπ hcτ u
  have hξ₀ : ξ.map (fun γ => γ 0)=π.map (fun γ => γ 0) := by
    rw [half_mixture_map_eval,hτ₀,half_smul_self]
  have hξ₁ : ξ.map (fun γ => γ 1)=π.map (fun γ => γ 1) := by
    rw [half_mixture_map_eval,hτ₁,half_smul_self]
  have hpξ' : IsOptimalCoupling (ξ.map (fun γ => γ 0)) (ξ.map (fun γ => γ 1))
      (ξ.map (fun γ => (γ 0,γ 1))) := by rwa [hξ₀,hξ₁]
  have hsξ₀ : ∀ᵐ x ∂ξ.map (fun γ => γ 0), dist x p ≤ R := by rwa [hξ₀]
  have hsξ₁ : ∀ᵐ x ∂ξ.map (fun γ => γ 1), dist x p ≤ R := by rwa [hξ₁]
  let F := fun z : C(Time,X)×C(Time,X) => (z.1,meetingSplice t z)
  let G := fun z : C(Time,X)×C(Time,X) => (z.2,meetingSplice t z)
  have hF : Measurable F := measurable_fst.prodMk (measurable_meetingSplice t)
  have hG : Measurable G := measurable_snd.prodMk (measurable_meetingSplice t)
  have hF₀ : (σ.map F).map Prod.fst=π := by
    simpa only [Measure.map_map measurable_fst hF,Function.comp_def,F] using hl
  have hG₀ : (σ.map G).map Prod.fst=π := by
    simpa only [Measure.map_map measurable_fst hG,Function.comp_def,G] using hr
  have hF₁ : (σ.map F).map Prod.snd=τ := by
    rw [Measure.map_map measurable_snd hF]; rfl
  have hG₁ : (σ.map G).map Prod.snd=τ := by
    rw [Measure.map_map measurable_snd hG]; rfl
  have hdomF₀ : ((2:ℝ≥0∞)⁻¹ • σ.map F).map Prod.fst ≤ ξ := by
    rw [Measure.map_smul _ measurable_fst.aemeasurable,hF₀]; exact hπξ
  have hdomF₁ : ((2:ℝ≥0∞)⁻¹ • σ.map F).map Prod.snd ≤ ξ := by
    rw [Measure.map_smul _ measurable_snd.aemeasurable,hF₁]; exact hτξ
  have hdomG₀ : ((2:ℝ≥0∞)⁻¹ • σ.map G).map Prod.fst ≤ ξ := by
    rw [Measure.map_smul _ measurable_fst.aemeasurable,hG₀]; exact hπξ
  have hdomG₁ : ((2:ℝ≥0∞)⁻¹ • σ.map G).map Prod.snd ≤ ξ := by
    rw [Measure.map_smul _ measurable_snd.aemeasurable,hG₁]; exact hτξ
  have hpast : ∀ᵐ z ∂((2:ℝ≥0∞)⁻¹ • σ.map F), z ∈ pathAgreement (t:ℝ) := by
    have hpast0 : ∀ᵐ z ∂σ.map F, z ∈ pathAgreement (t:ℝ) := by
      apply (ae_map_iff hF.aemeasurable (measurableSet_pathAgreement _)).mpr
      exact .of_forall fun z r hr => (meetingSplice_left t z hr).symm
    exact hpast0.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hsuffix : ∀ᵐ z ∂((2:ℝ≥0∞)⁻¹ • σ.map G), ∀ r : Time, t ≤ r → z.1 r=z.2 r := by
    have hsource : ∀ᵐ z ∂σ, ∀ r : Time, t ≤ r → z.2 r=meetingSplice t z r :=
      hmeet.mono fun z hz r hr => (meetingSplice_right t z hz hr).symm
    have hclosed : IsClosed {z : C(Time,X)×C(Time,X) | ∀ r : Time, t ≤ r → z.1 r=z.2 r} := by
      simp only [ofPred_forall]
      apply isClosed_iInter
      intro r
      apply isClosed_iInter
      intro _
      exact isClosed_eq ((continuous_eval_const r).comp continuous_fst)
        ((continuous_eval_const r).comp continuous_snd)
    have hh' : ∀ᵐ z ∂σ.map G, ∀ r : Time, t ≤ r → z.1 r=z.2 r :=
      (ae_map_iff hG.aemeasurable hclosed.measurableSet).mpr hsource
    exact hh'.filter_mono Measure.smul_absolutelyContinuous.ae_le
  let : IsFiniteMeasure ((2:ℝ≥0∞)⁻¹ • σ.map F) := (σ.map F).smul_finite (by norm_num)
  let : IsFiniteMeasure ((2:ℝ≥0∞)⁻¹ • σ.map G) := (σ.map G).smul_finite (by norm_num)
  have hleft := hX.paired_common_prefix_unique hn p hR ξ hgξ hpξ' hB hcξ hsξ₀ hsξ₁
    ((2:ℝ≥0∞)⁻¹ • σ.map F) hdomF₀ hdomF₁ t ht0 hpast
  have hright := hX.paired_common_suffix_unique hn p hR ξ hgξ hpξ' hB hcξ hsξ₀ hsξ₁
    ((2:ℝ≥0∞)⁻¹ • σ.map G) hdomG₀ hdomG₁ t ht1 hsuffix
  have haF := hleft.filter_mono (Measure.absolutelyContinuous_smul (by norm_num : (2:ℝ≥0∞)⁻¹ ≠ 0)).ae_le
  have haG := hright.filter_mono (Measure.absolutelyContinuous_smul (by norm_num : (2:ℝ≥0∞)⁻¹ ≠ 0)).ae_le
  have hleft' := ae_of_ae_map (p:=fun z : C(Time,X)×C(Time,X) => z.1=z.2) hF.aemeasurable haF
  have hright' := ae_of_ae_map (p:=fun z : C(Time,X)×C(Time,X) => z.1=z.2) hG.aemeasurable haG
  filter_upwards [hleft',hright'] with z hz₀ hz₁
  exact hz₀.trans hz₁.symm

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
