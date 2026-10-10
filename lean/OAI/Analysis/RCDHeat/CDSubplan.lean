import Mathlib
import OAI.Analysis.RCDHeat.CompactTransportVariation

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: CDSubplan, TransportExcess, TransportExcessVariational, GeodesicPlanCompact, TransportExcessLocalization. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

 theorem FiniteSecondMoment.of_le {ν η : Measure X} (h : FiniteSecondMoment ν)
    (hle : η ≤ ν) : FiniteSecondMoment η := by
  obtain ⟨p,hp⟩ := h
  exact ⟨p,lt_of_le_of_lt (lintegral_mono' hle (le_refl _)) hp⟩

 theorem FiniteSecondMoment.smul {ν : Measure X} (h : FiniteSecondMoment ν)
    {a : ℝ≥0∞} (ha : a ≠ ∞) : FiniteSecondMoment (a • ν) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨p,?_⟩
  rw [lintegral_smul_measure]
  exact ENNReal.mul_lt_top ha.lt_top hp

variable [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

 theorem FullCD.replace_subplan (μ : Measure X) (K : ℝ) (n : ℕ)
    (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀]
    (h0 : ν₀ ≪ μ) (h1 : ν₁ ≪ μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    {π σ : Measure C(Time,X)} [IsFiniteMeasure π]
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ) (hσ : σ ≤ π) (hσ0 : σ univ ≠ 0) :
    let η₀ := (σ univ)⁻¹ • σ.map (fun γ => γ 0)
    let η₁ := (σ univ)⁻¹ • σ.map (fun γ => γ 1)
    ∃ τ : Measure C(Time,X), IsProbabilityMeasure τ ∧
      (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      IsOptimalCoupling η₀ η₁ (τ.map (fun γ => (γ 0,γ 1))) ∧
      (∀ (N : ℝ), (n:ℝ) ≤ N → ∀ t : Time,
        (∫⁻ γ,
          tau K N (1-(t:ℝ)) (dist (γ 0) (γ 1)) *
            (η₀.rnDeriv μ (γ 0)) ^ (-(1/N)) +
          tau K N (t:ℝ) (dist (γ 0) (γ 1)) *
            (η₁.rnDeriv μ (γ 1)) ^ (-(1/N)) ∂τ) ≤
          renyiIntegral μ (τ.map (fun γ => γ t)) N) ∧
      IsProbabilityMeasure (π-σ+σ univ • τ) ∧
      (∀ᵐ γ ∂(π-σ+σ univ • τ), IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁
        ((π-σ+σ univ • τ).map (fun γ => (γ 0,γ 1))) := by
  let : IsFiniteMeasure σ := isFiniteMeasure_of_le π hσ
  let : NeZero σ := ⟨by intro he; exact hσ0 (by rw [he]; rfl)⟩
  have hσfin : σ univ ≠ ∞ := measure_ne_top σ univ
  let η₀ := (σ univ)⁻¹ • σ.map (fun γ => γ 0)
  let η₁ := (σ univ)⁻¹ • σ.map (fun γ => γ 1)
  have htprob : IsProbabilityMeasure ((σ univ)⁻¹ • σ) := inferInstance
  have he0 : (((σ univ)⁻¹ • σ).map (fun γ => γ 0)) = η₀ :=
    Measure.map_smul _ (measurable_path_eval 0).aemeasurable
  have he1 : (((σ univ)⁻¹ • σ).map (fun γ => γ 1)) = η₁ :=
    Measure.map_smul _ (measurable_path_eval 1).aemeasurable
  have hprob0 : IsProbabilityMeasure η₀ := he0 ▸ inferInstance
  have hprob1 : IsProbabilityMeasure η₁ := he1 ▸ inferInstance
  have hep := optimalPlan_endpoints ν₀ ν₁ π hp
  have hle0 : σ.map (fun γ => γ 0) ≤ ν₀ := by
    rw [←hep.1]
    exact Measure.map_mono hσ (measurable_path_eval 0)
  have hle1 : σ.map (fun γ => γ 1) ≤ ν₁ := by
    rw [←hep.2]
    exact Measure.map_mono hσ (measurable_path_eval 1)
  have ha : (σ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hσ0
  obtain ⟨τ,ht,hgt,hot,hRt⟩ := hcd η₀ η₁ hprob0 hprob1
    ((hle0.absolutelyContinuous.trans h0).smul_left _)
    ((hle1.absolutelyContinuous.trans h1).smul_left _)
    ((hm0.of_le hle0).smul ha) ((hm1.of_le hle1).smul ha)
  have hscaled : IsOptimalCoupling (σ.map (fun γ => γ 0)) (σ.map (fun γ => γ 1))
      ((σ univ • τ).map (fun γ => (γ 0,γ 1))) := by
    have hh := hot.smul hσ0 hσfin
    rw [Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable]
    simpa only [η₀,η₁,smul_smul,ENNReal.mul_inv_cancel hσ0 hσfin,one_smul] using hh
  have hgscaled : ∀ᵐ γ ∂(σ univ • τ), IsGeodesic γ :=
    hgt.filter_mono (Measure.smul_absolutelyContinuous.ae_le)
  exact ⟨τ,ht,hgt,hot,hRt,optimalPlan_replace_subplan hp hg hσ hscaled hgscaled⟩
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X]

 

noncomputable def transportExcessMass (μ ν : Measure X) (C : ℝ≥0∞) : ℝ≥0∞ :=
  (ν-C • μ) univ

 theorem transportExcessMass_zero_iff (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞) :
    transportExcessMass μ ν C = 0 ↔ ν ≤ C • μ := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  rw [transportExcessMass,Measure.measure_univ_eq_zero]
  constructor
  · intro h
    have hh : ν-C • μ ≤ (0 : Measure X) := h.le
    simpa only [zero_add] using Measure.sub_le_iff_le_add.mp hh
  · exact Measure.sub_eq_zero_of_le

 theorem transportExcessMass_le (μ ν : Measure X) (C : ℝ≥0∞) :
    transportExcessMass μ ν C ≤ ν univ := Measure.sub_le univ

 

 theorem transportExcessMass_eq_density (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hν : ν ≪ μ) {C : ℝ≥0∞} (hC : C ≠ ∞) :
    transportExcessMass μ ν C = ∫⁻x, (ν.rnDeriv μ x-C) ∂μ := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  have hi : IsFiniteMeasure (μ.withDensity (fun _ => C)) := by
    rw [withDensity_const]
    infer_instance
  have he := Measure.withDensity_sub (μ := μ) (ν.measurable_rnDeriv μ) (measurable_const (a := C))
  rw [Measure.withDensity_rnDeriv_eq ν μ hν,withDensity_const] at he
  rw [transportExcessMass,←he,withDensity_apply _ MeasurableSet.univ]
  simp

 

 theorem transportExcessMass_mixture (μ ν η : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure η] {C a b : ℝ≥0∞} (hC : C ≠ ∞)
    (hab : a+b=1) :
    transportExcessMass μ (a • ν+b • η) C ≤
      a*transportExcessMass μ ν C+b*transportExcessMass μ η C := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  have hν : ν ≤ (ν-C • μ)+C • μ := Measure.sub_le_iff_le_add.mp le_rfl
  have hη : η ≤ (η-C • μ)+C • μ := Measure.sub_le_iff_le_add.mp le_rfl
  have hm : a • ν+b • η ≤ (a • (ν-C • μ)+b • (η-C • μ))+C • μ := by
    calc
      _ ≤ a • ((ν-C • μ)+C • μ)+b • ((η-C • μ)+C • μ) :=
        add_le_add (fun s => by simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul_right (hν s) a)
          (fun s => by simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul_right (hη s) b)
      _ = _ := by
        rw [smul_add,smul_add]
        calc
          _ = (a • (ν-C • μ)+b • (η-C • μ))+(a • (C • μ)+b • (C • μ)) := by abel
          _ = _ := by rw [←add_smul,hab,one_smul]
  have hh := Measure.sub_le_of_le_add hm univ
  simpa only [transportExcessMass,Measure.add_apply,Measure.smul_apply,smul_eq_mul] using hh

 
 theorem transportExcessMass_set_le (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞) (s : Set X) :
    ν s-C*μ s ≤ transportExcessMass μ ν C := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  have hh : ν ≤ (ν-C • μ)+C • μ := Measure.sub_le_iff_le_add.mp le_rfl
  have hs : ν s ≤ (ν-C • μ) s+C*μ s := by
    simpa only [Measure.add_apply,Measure.smul_apply,smul_eq_mul] using hh s
  exact (tsub_le_iff_right.mpr hs).trans (measure_mono (subset_univ s))

 

 theorem transportExcessMass_attained (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞) :
    ∃ s : Set X, MeasurableSet s ∧ transportExcessMass μ ν C = ν s-C*μ s := by
  let : IsFiniteMeasure (C • μ) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top hC.lt_top (measure_lt_top μ univ)⟩
  obtain ⟨s,hs⟩ := exists_isHahnDecomposition ν (C • μ)
  refine ⟨sᶜ,hs.measurableSet.compl,?_⟩
  have hz : (ν-C • μ) s = 0 :=
    Measure.sub_apply_eq_zero_of_restrict_le_restrict hs.le_on hs.measurableSet
  calc
    transportExcessMass μ ν C = (ν-C • μ) s+(ν-C • μ) sᶜ :=
      (measure_add_measure_compl hs.measurableSet).symm
    _ = (ν-C • μ) sᶜ := by rw [hz,zero_add]
    _ = (ν.restrict sᶜ-(C • μ).restrict sᶜ) univ := by
      rw [←Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl]
      simp
    _ = ν sᶜ-C*μ sᶜ := by
      rw [Measure.sub_apply MeasurableSet.univ hs.ge_on_compl]
      simp only [Measure.restrict_apply_univ,Measure.smul_apply,smul_eq_mul]

variable [TopologicalSpace X] [OpensMeasurableSpace X]

omit [OpensMeasurableSpace X] in
 

 theorem transportExcessMass_le_iff_open (μ ν : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [Measure.OuterRegular μ] {C e : ℝ≥0∞} (hC : C ≠ ∞) :
    transportExcessMass μ ν C ≤ e ↔ ∀ U : Set X, IsOpen U → ν U ≤ e+C*μ U := by
  constructor
  · intro h U _
    exact tsub_le_iff_right.mp ((transportExcessMass_set_le μ ν hC U).trans h)
  · intro h
    obtain ⟨s,hs,he⟩ := transportExcessMass_attained μ ν hC
    rw [he,tsub_le_iff_right]
    let : Measure.OuterRegular (C • μ) := Measure.OuterRegular.smul μ hC
    have hm : C*μ s = ⨅ (U : Set X) (_ : s ⊆ U) (_ : IsOpen U), (C • μ) U := by
      simpa only [Measure.smul_apply,smul_eq_mul] using s.measure_eq_iInf_isOpen (C • μ)
    rw [hm]
    simp_rw [ENNReal.add_iInf]
    refine le_iInf fun U => le_iInf fun hU => le_iInf fun ho => ?_
    exact (measure_mono hU).trans (by simpa only [Measure.smul_apply,smul_eq_mul] using h U ho)

 

 theorem transportExcessMass_le_of_tendsto [HasOuterApproxClosed X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.OuterRegular μ]
    {ι : Type*} {L : Filter ι} [NeBot L]
    {ν : ProbabilityMeasure X} {νs : ι → ProbabilityMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {C e : ℝ≥0∞} (hC : C ≠ ∞)
    (he : ∀ᶠ i in L, transportExcessMass μ (νs i) C ≤ e) :
    transportExcessMass μ ν C ≤ e := by
  rw [transportExcessMass_le_iff_open μ ν hC]
  intro U hU
  have hl := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν hU
  refine hl.trans (liminf_le_of_frequently_le ?_)
  exact (he.mono fun i hi => (transportExcessMass_le_iff_open μ (νs i) hC).mp hi U hU).frequently
 

 theorem lowerSemicontinuous_transportExcessMass [HasOuterApproxClosed X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.OuterRegular μ]
    {C : ℝ≥0∞} (hC : C ≠ ∞) :
    LowerSemicontinuous (fun ν : ProbabilityMeasure X => transportExcessMass μ ν C) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro e
  apply isClosed_of_closure_subset
  intro ν hν
  let A := {η : ProbabilityMeasure X | transportExcessMass μ η C ≤ e}
  have : NeBot (𝓝[A] ν) := mem_closure_iff_nhdsWithin_neBot.mp hν
  exact transportExcessMass_le_of_tendsto μ (L := 𝓝[A] ν)
    (νs := id) (tendsto_id.mono_left nhdsWithin_le_nhds) hC self_mem_nhdsWithin

 

 theorem compact_family_minimizes_excess [HasOuterApproxClosed X]
    (μ : Measure X) [IsFiniteMeasure μ] [Measure.OuterRegular μ]
    {C : ℝ≥0∞} (hC : C ≠ ∞) {A : Set (ProbabilityMeasure X)}
    (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ ν ∈ A, ∀ η ∈ A, transportExcessMass μ ν C ≤ transportExcessMass μ η C := by
  exact ((lowerSemicontinuous_transportExcessMass μ hC).lowerSemicontinuousOn A).exists_isMinOn hne hA
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X]

 

 theorem isCompact_bounded_geodesics (p : X) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact {γ : C(Time,X) | IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ R} := by
  let G := fun f : Time → X =>
    (∀ s t : Time, dist (f s) (f t) = |(s:ℝ)-(t:ℝ)| * dist (f 0) (f 1)) ∧
      ∀ t, dist (f t) p ≤ R
  let C : ℝ≥0 := ⟨2*R,by positivity⟩
  have hLip (f : Time → X) (hf : G f) : LipschitzWith C f := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have hd : dist (f 0) (f 1) ≤ 2*R := by
      have hh := dist_triangle (f 0) p (f 1)
      rw [dist_comm p (f 1)] at hh
      have h0 := hf.2 0
      have h1 := hf.2 1
      linarith
    change dist (f s) (f t) ≤ (2*R)*dist s t
    rw [hf.1 s t]
    simpa only [Subtype.dist_eq,Real.dist_eq,mul_comm] using
      mul_le_mul_of_nonneg_left hd (abs_nonneg ((s:ℝ)-(t:ℝ)))
  have hG : IsClosed {f : Time → X | G f} := by
    change IsClosed ({f : Time → X | ∀ s t : Time,
      dist (f s) (f t) = |(s:ℝ)-(t:ℝ)| * dist (f 0) (f 1)} ∩
      {f : Time → X | ∀ t, dist (f t) p ≤ R})
    apply IsClosed.inter
    · simp only [ofPred_forall]
      exact isClosed_iInter fun s => isClosed_iInter fun t =>
        isClosed_eq (by fun_prop) (by fun_prop)
    · simp only [ofPred_forall]
      exact isClosed_iInter fun t => isClosed_le (by fun_prop) continuous_const
  have hK : IsCompact {f : Time → X | G f} := by
    apply (isCompact_pi_infinite (s := fun _ : Time => closedBall p R)
      (fun _ => isCompact_closedBall p R)).of_isClosed_subset hG
    intro f hf t
    exact hf.2 t
  let S := {γ : C(Time,X) | IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ R}
  have he : ContinuousMap.toFun '' S = {f : Time → X | G f} := by
    ext f
    constructor
    · rintro ⟨γ,hγ,rfl⟩
      exact hγ
    · intro hf
      exact ⟨⟨f,(hLip f hf).continuous⟩,hf,rfl⟩
  apply ArzelaAscoli.isCompact_of_equicontinuous S (he.symm ▸ hK)
  exact (LipschitzWith.uniformEquicontinuous (fun γ : S => (γ : C(Time,X))) C
    (fun γ => hLip γ γ.property)).equicontinuous

attribute [local instance] pathBorel pathBorelSpace

 

 theorem isCompact_bounded_geodesic_plans (p : X) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact {π : ProbabilityMeasure C(Time,X) |
      ∀ᵐ γ ∂(π : Measure C(Time,X)), IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ R} := by
  let S := {γ : C(Time,X) | IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ R}
  have hc := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ : ℕ => (0 : ℝ≥0)) (K := fun _ : ℕ => S) tendsto_const_nhds
    (fun _ => isCompact_bounded_geodesics p hR) (Or.inr monotone_const)
  convert hc using 1
  ext π
  simp only [mem_ofPred_eq,le_zero_iff,forall_const,
    ProbabilityMeasure.null_iff_toMeasure_null,ae_iff]
  rfl
end

 
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MeasurableSpace X]

 

 theorem compression_iff_localized (μ ν : Measure X) {B : Set X}
    (hν : ∀ᵐ x ∂ν, x ∈ B) (C : ℝ≥0∞) :
    ν ≤ C • μ ↔ ν ≤ C • μ.restrict B := by
  have he : ν.restrict B = ν := Measure.restrict_eq_self_of_ae_mem hν
  constructor
  · intro h
    calc
      ν = ν.restrict B := he.symm
      _ ≤ (C • μ).restrict B := Measure.restrict_mono subset_rfl h
      _ = C • μ.restrict B := Measure.restrict_smul _ _ _
  · intro h
    refine h.trans ?_
    intro s
    simpa only [Measure.smul_apply,smul_eq_mul] using
      mul_le_mul_right ((Measure.restrict_le_self (μ := μ) (s := B)) s) C

 

 theorem localized_excess_zero_iff (μ ν : Measure X) {B : Set X}
    [IsFiniteMeasure (μ.restrict B)] [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ B) {C : ℝ≥0∞} (hC : C ≠ ∞) :
    transportExcessMass (μ.restrict B) ν C = 0 ↔ ν ≤ C • μ := by
  rw [transportExcessMass_zero_iff (μ.restrict B) ν hC]
  exact (compression_iff_localized μ ν hν C).symm

end RegularPointCoordinates

end OAI
