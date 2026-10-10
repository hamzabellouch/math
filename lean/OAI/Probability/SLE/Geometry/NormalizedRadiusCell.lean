import OAI.Probability.SLE.Geometry.NormalizedCellAllTimes
import OAI.Probability.SLE.Geometry.NormalizedCanonicalRestart
import OAI.Probability.SLE.Geometry.NormalizedRadiusRestart
import OAI.Probability.SLE.Loewner.RawDiskRadiusLaw

namespace OAI

/-! The cell comparison at the actual future radius time. The normalized
disk variable is the same raw variable used in the prescribed coefficients. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance radiusCellMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance radiusCellBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma CanonicalMass.normalized_cell_bounds_at_finite_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E)
    (hEp : ∀ p∈E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (a : Ω → ℝ≥0) (haM : Measurable[hτ.measurableSpace] a) (ha : ∀ ω, 0 < a ω)
    (β : Ω → ℝ≥0 → ℂ) (G' F' : Ω → ℝ≥0 → ℂ → ℂ)
    (hβ : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ*normalizedRestartDriverPath B hc τ a ω t)
      (β ω) (G' ω) (F' ω)) :
    ∀ᵐ ω ∂P, ∀ (θ : ℝ) (_hθ : θ ∈ Ioo (0:ℝ) Real.pi)
      (z : ℂ) (_hz : z ∈ survivingDomain (γ ω) (τ ω))
      (r : ℝ) (_hr : 0 < r)
      (_hR : fullRadius (G ω) (τ ω) z=(2048*Real.pi)*r)
      (_hpolar : G ω (τ ω) z=(Real.sqrt κ*B (τ ω) ω:ℝ)+
        (a ω:ℂ)*Complex.exp (θ*Complex.I))
      (u : ℝ) (_hbase : fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u))
      (v : ℝ) (_hv : 0 < v)
      (_hf : radiusLevelTime (β ω) (G' ω) (Target.diskMapInv θ 0) v < ∞),
      let L := ENNReal.ofReal (R.diskAtRadius κ θ v (normalizedRestartDriverPath B hc τ a ω))
      let N := extendedCanonicalMass C.process C.rational.terminal
        (radiusLevelTime (γ ω) (G ω) z (u+v)) ω
      ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*L ≤
          N (Subtype.val ⁻¹' closedBall z ((4096*Real.pi)*r)) ∧
        ∀ A : Set ℂ, MeasurableSet A → A ⊆ closedBall z (2*r) →
          A ⊆ survivingDomain (γ ω) (τ ω) →
          N (Subtype.val ⁻¹' A) ≤ ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*L := by
  filter_upwards [C.normalized_cell_bounds_all_times hB hc hκ F hw R he E hE hEf hEp
    hgrowth hpublished τ hτ a haM ha,hβ] with ω hcell hb
  intro θ hθ z hz r hr hR hpolar u hbase v hv hf
  obtain ⟨t,ht,htR⟩ := exists_live_level_of_radiusLevelTime_lt_top _ _ _ _ hf
  have hU : Continuous (fun t => Real.sqrt κ*B t ω) := (hc ω).const_mul _
  have hb' : IsCapacityTwoWitness
      (normalizedRestartDriver (fun t => Real.sqrt κ*B t ω) (τ ω) (a ω))
      (β ω) (G' ω) (F' ω) := by
    rw [← normalizedRestartDriverPath_driver κ B hc τ a ω]
    exact hb
  have hF : F ω (τ ω) ((a ω:ℂ)*Target.diskMapInv θ 0+
      (Real.sqrt κ*B (τ ω) ω:ℝ))=z := by
    rw [Target.diskMapInv_zero]
    rw [add_comm,← hpolar]
    exact (hw ω).2.2.2.2.2.2.2.1 (τ ω) z hz
  have hphysical := (hw ω).normalized_restart_level_of_live_source hU (τ ω) (a ω)
    (ha ω) hb' (Target.diskMapInv θ 0) u v (by simpa only [hF] using hbase) t ht htR
  rw [hF] at hphysical
  have htime := radiusLevelTime_eq_of_live_level
    ((normalizedRestartDriverPath B hc τ a ω).continuous.const_mul _) hb _ v t ht htR
  have hdisk : R.diskAtRadius κ θ v (normalizedRestartDriverPath B hc τ a ω)=
      compactWeightedMass (Target.diskMassWeight κ θ hθ) (Target.diskSourceHalfPlane θ)
        (R.process t (normalizedRestartDriverPath B hc τ a ω)) := by
    unfold RawCanonicalMass.diskAtRadius
    rw [canonicalRadiusLevel_eq κ _ hb v hv.le,htime]
    simp only [extendedCanonicalMass,ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe,
      diskMassValue_toReal_eq κ θ hθ]
  dsimp only
  rw [hphysical.2]
  simp only [extendedCanonicalMass,ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe,hdisk]
  exact hcell t θ hθ z hz r hr hR hpolar

lemma CanonicalMass.normalized_cell_bounds_at_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E)
    (hEp : ∀ p∈E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (a : Ω → ℝ≥0) (haM : Measurable[hτ.measurableSpace] a) (ha : ∀ ω, 0 < a ω) :
    ∀ᵐ ω ∂P, ∀ (θ : ℝ) (_hθ : θ ∈ Ioo (0:ℝ) Real.pi)
      (z : ℂ) (_hz : z ∈ survivingDomain (γ ω) (τ ω))
      (r : ℝ) (_hr : 0 < r)
      (_hR : fullRadius (G ω) (τ ω) z=(2048*Real.pi)*r)
      (_hpolar : G ω (τ ω) z=(Real.sqrt κ*B (τ ω) ω:ℝ)+
        (a ω:ℂ)*Complex.exp (θ*Complex.I))
      (u : ℝ) (_hu : 0 ≤ u)
      (_hbase : fullRadius (G ω) (τ ω) z=(2*z.im)*Real.exp (-u))
      (v : ℝ) (_hv : 0 < v)
      (_hf : radiusLevelTime (γ ω) (G ω) z (u+v) < ∞),
      let L := ENNReal.ofReal (R.diskAtRadius κ θ v (normalizedRestartDriverPath B hc τ a ω))
      let N := extendedCanonicalMass C.process C.rational.terminal
        (radiusLevelTime (γ ω) (G ω) z (u+v)) ω
      ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*L ≤
          N (Subtype.val ⁻¹' closedBall z ((4096*Real.pi)*r)) ∧
        ∀ A : Set ℂ, MeasurableSet A → A ⊆ closedBall z (2*r) →
          A ⊆ survivingDomain (γ ω) (τ ω) →
          N (Subtype.val ⁻¹' A) ≤ ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*L := by
  obtain ⟨Φ,Gc,Fc,_hΦ,hW⟩ := exists_measurable_canonical_witness _ κ hpublished
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.of_uncurry_left
  let Y := normalizedRestartDriverPath B hc τ a
  have hY : Measurable Y := measurable_scaleDriverPath.comp
    ((haM.mono hτ.measurableSpace_le le_rfl).inv.prodMk
      (sourceRestartDriverPath_measurable B hm hc τ hτ))
  have hYlaw : P.map Y=P.map (sourceDriverPath B hc) := by
    change P.map (fun ω => scaleDriverPath (a ω)⁻¹
      (sourceRestartDriverPath B hc τ ω))=P.map (sourceDriverPath B hc)
    simpa only [Measure.restrict_univ,measure_univ,one_smul] using
      source_restart_random_scale_driver_law B hB hm hc τ hτ
        (fun ω => (a ω)⁻¹) haM.inv (fun ω => inv_pos.mpr (ha ω))
        univ MeasurableSet.univ
  have hβ := canonical_witness_pullback hW Y hY hYlaw
  filter_upwards [C.normalized_cell_bounds_at_finite_radius hB hc hκ F hw R he E hE
    hEf hEp hgrowth hpublished τ hτ a haM ha (fun ω => Φ (Y ω))
    (fun ω => Gc (Y ω)) (fun ω => Fc (Y ω)) hβ,hβ] with ω hcell hb
  intro θ hθ z hz r hr hR hpolar u hu hbase v hv hf
  have hF : F ω (τ ω) ((a ω:ℂ)*Target.diskMapInv θ 0+
      (Real.sqrt κ*B (τ ω) ω:ℝ))=z := by
    rw [Target.diskMapInv_zero,add_comm,← hpolar]
    exact (hw ω).2.2.2.2.2.2.2.1 (τ ω) z hz
  have hb' : IsCapacityTwoWitness
      (normalizedRestartDriver (fun t => Real.sqrt κ*B t ω) (τ ω) (a ω))
      (Φ (Y ω)) (Gc (Y ω)) (Fc (Y ω)) := by
    rw [← normalizedRestartDriverPath_driver κ B hc τ a ω]
    exact hb
  have hequiv := (hw ω).normalized_restart_radius_finite_iff ((hc ω).const_mul _)
    (τ ω) (a ω) (ha ω) hb' (Target.diskMapInv θ 0)
    (Target.diskMapInv_maps hθ (by simp)) u v hu hv (by simpa only [hF] using hbase)
  rw [hF] at hequiv
  exact hcell θ hθ z hz r hr hR hpolar u hbase v hv (hequiv.mp hf)

end SLEExactGauge.Multipoint

end

end OAI
