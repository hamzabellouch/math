import Mathlib
import OAI.Probability.SLE.HausdorffLimits

namespace OAI

/-! Actual Retained Kernel for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
def sourceFiniteGreenKernel (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) : Kernel a.samples ℂ :=
  (Kernel.const a.samples (volume.restrict (closedBall z₀ 1))).withDensity
    (fun ω z => ENNReal.ofReal (if spatialHitTime (γ ω) z ((2:ℝ)^(-(N:ℝ))) ≤ T then
      spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z ((2:ℝ)^(-(N:ℝ))) else 0))
lemma sourceFiniteGreenDensity_measurable (r : ℝ) (T : ℝ≥0) :
    Measurable (fun p : a.samples × ℂ => ENNReal.ofReal (if spatialHitTime (γ p.1) p.2 r ≤ T then
      spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t p.1) (γ p.1) (a.G p.1) p.2 r else 0)) := by
  have hm (t : ℝ≥0) : Measurable (fun ω : a.samples => γ ω t) :=
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl
  have ht := (spatialHitTime_measurable (fun ω : a.samples => γ ω) a.trace_continuous hm r).comp measurable_swap
  have hW := (a.spatialGreenWeight_measurable r).comp measurable_swap
  exact (Measurable.ite (measurableSet_le ht measurable_const) hW measurable_const).ennreal_ofReal
lemma sourceFiniteGreenKernel_apply (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples)
    (S : Set ℂ) (hS : MeasurableSet S) :
    a.sourceFiniteGreenKernel z₀ T N ω S = finiteSpatialGreenMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ((2:ℝ)^(-(N:ℝ))) T (closedBall z₀ 1 ∩ S) := by
  rw [sourceFiniteGreenKernel,Kernel.withDensity_apply' _ (a.sourceFiniteGreenDensity_measurable _ T)]
  simp only [Kernel.const_apply,finiteSpatialGreenMass,Measure.restrict_restrict hS,inter_comm]
  rfl
lemma sourceFiniteGreenKernel_univ (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples) :
    a.sourceFiniteGreenKernel z₀ T N ω univ = finiteSpatialGreenMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ((2:ℝ)^(-(N:ℝ))) T (closedBall z₀ 1) := by
  rw [a.sourceFiniteGreenKernel_apply z₀ T N ω univ MeasurableSet.univ,inter_univ]
lemma sourceFiniteGreenKernel_K (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples) :
    a.sourceFiniteGreenKernel z₀ T N ω (closedBall z₀ 1) = finiteSpatialGreenMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ((2:ℝ)^(-(N:ℝ))) T (closedBall z₀ 1) := by
  rw [a.sourceFiniteGreenKernel_apply z₀ T N ω _ measurableSet_closedBall,inter_self]
lemma sourceFiniteGreenKernel_supported (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples) :
    a.sourceFiniteGreenKernel z₀ T N ω (closedBall z₀ 1)ᶜ = 0 := by
  rw [a.sourceFiniteGreenKernel_apply z₀ T N ω _ measurableSet_closedBall.compl,inter_compl_self]
  simp [finiteSpatialGreenMass]
lemma sourceFiniteGreenKernel_finite (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 2 < z₀.im) (T : ℝ≥0) (N : ℕ) :
    IsFiniteKernel (a.sourceFiniteGreenKernel z₀ T N) := by
  let r := (2:ℝ)^(-(N:ℝ))
  have hr : 0 < r := source_dyadic_side_pos N
  have hr1 : r ≤ 1 := by
    dsimp [r]
    rw [source_dyadic_side_eq]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨⟨ENNReal.ofReal (r^(-codimension κ))*volume (closedBall z₀ 1),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_closedBall_lt_top),?_⟩⟩
  intro ω
  rw [a.sourceFiniteGreenKernel_univ]
  change (∫⁻ z in closedBall z₀ 1, ENNReal.ofReal (if spatialHitTime (γ ω) z r ≤ T then
    spatialGreenWeight κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) z r else 0)) ≤ _
  calc
    _ ≤ ∫⁻ z in closedBall z₀ 1, ENNReal.ofReal (r^(-codimension κ)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz'
      apply ENNReal.ofReal_le_ofReal
      split_ifs
      · exact (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _) hκ hκ8 hr z
          (hr1.trans (source_unit_ball_height hz hz').le) |>.2
      · exact Real.rpow_nonneg hr.le _
    _ = _ := by simp
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
lemma sourceFiniteGreenKernel_carrier (z₀ : ℂ) (T : ℝ≥0) (N : ℕ) (ω : a.samples) :
    a.sourceFiniteGreenKernel z₀ T N ω (cthickening ((2:ℝ)^(-(N:ℝ))) (γ ω '' Icc 0 T))ᶜ = 0 := by
  have hm := (isClosed_cthickening : IsClosed (cthickening ((2:ℝ)^(-(N:ℝ))) (γ ω '' Icc 0 T))).measurableSet
  rw [a.sourceFiniteGreenKernel_apply z₀ T N ω _ hm.compl,finiteSpatialGreenMass]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_closedBall.inter hm.compl)] with z hz
  have hn : ¬ spatialHitTime (γ ω) z ((2:ℝ)^(-(N:ℝ))) ≤ T := by
    intro ht
    obtain ⟨t,ht,hd⟩ := (spatialHitTime_le_iff (a.trace_continuous ω) z _ T).mp ht
    exact hz.2 (mem_cthickening_of_dist_le z (γ ω t) _ _ ⟨t,ht,rfl⟩ (by simpa [dist_comm] using hd.le))
  simp only [ite_eq_right hn, ENNReal.ofReal_zero,Pi.zero_apply]
end RegularSLEPresentation
lemma source_dyadic_tendsto : Tendsto (fun N : ℕ => (2:ℝ)^(-(N:ℝ))) atTop (𝓝 0) := by
  simp_rw [source_dyadic_side_eq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
lemma source_dyadic_eventually_le {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ N ≥ n, (2:ℝ)^(-(N:ℝ)) ≤ ε := by
  exact (eventually_atTop.mp (source_dyadic_tendsto.eventually (eventually_le_nhds hε)))
lemma retainedMeasure_zero_of_zero {Ω : Type*} [MeasurableSpace Ω] (κ D : ℝ)
    (ν : ℕ → Kernel Ω ℂ) (k₀ N : ℕ) (ω : Ω) {S : Set ℂ} (hS : ν N ω S = 0) :
    retainedMeasure κ D ν k₀ N ω S = 0 := by
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans hS.le) bot_le
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
lemma source_actual_retained_experiment [IsProbabilityMeasure P] (hκ : 4 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz₀ : 2 < z₀.im) :
    ∃ (T : ℝ≥0) (D b p : ℝ) (k₀ : ℕ), 0 < T ∧ 1 ≤ D ∧ 0 < b ∧ 0 < p ∧
      ENNReal.ofReal p ≤ (P.comap Subtype.val)
        {ω : a.samples | ∃ᶠ N in atTop, ENNReal.ofReal b ≤
          retainedMeasure κ D (a.sourceFiniteGreenKernel z₀ T) k₀ N ω (closedBall z₀ 1)} := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  have hk : 0 < κ := by linarith
  obtain ⟨T,e₀,m₀,m₂,hT,he,hm₀,hm₂,hm⟩ := sourceRetainedSeed_proved κ hκ hκ8
    Ω inferInstance P inferInstance γ a z₀ hz₀
  obtain ⟨A,c,k₁,hA,hc,ht⟩ := sourceActualSquareTail_proved κ hκ hκ8
    Ω inferInstance P inferInstance γ a z₀ hz₀
  obtain ⟨k₂,hk₂⟩ := source_dyadic_eventually_le he
  let kmin := max k₁ k₂
  let ν := a.sourceFiniteGreenKernel z₀ T
  have hν (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hk hκ8 z₀ hz₀ T N
  have hfirst (N : ℕ) (hN : kmin ≤ N) :
      ENNReal.ofReal m₀ ≤ ∫⁻ ω, ν N ω (closedBall z₀ 1) ∂(P.comap Subtype.val) := by
    simp only [ν,a.sourceFiniteGreenKernel_K]
    exact (hm _ (source_dyadic_side_pos N) (hk₂ N ((le_max_right _ _).trans hN))).1
  have hsecond (N : ℕ) (hN : kmin ≤ N) :
      (∫⁻ ω, (ν N ω (closedBall z₀ 1))^2 ∂(P.comap Subtype.val)) ≤ ENNReal.ofReal m₂ := by
    simp only [ν,a.sourceFiniteGreenKernel_K]
    exact (hm _ (source_dyadic_side_pos N) (hk₂ N ((le_max_right _ _).trans hN))).2
  have htail (N k : ℕ) (hkmin : kmin ≤ k) (hkN : k ≤ N) (ij : ℤ × ℤ) (u : ℝ) (hu : 1 ≤ u) :
      (P.comap Subtype.val) {ω : a.samples | ((2:ℝ)^(-(k:ℝ)))^dimension κ*u <
        (ν N ω (retainedDyadicSquare k ij)).toReal} ≤
        ENNReal.ofReal (A*((2:ℝ)^(-(k:ℝ)))^codimension κ*Real.exp (-c*u^(2/codimension κ))) := by
    simp only [ν,a.sourceFiniteGreenKernel_apply z₀ T N _ _ (retainedSquare_measurable k ij)]
    exact ht T N k ((le_max_left _ _).trans hkmin) hkN ij u hu
  obtain ⟨D,b,p,B,k₀,hD,hb,hp,hB,hk₀,hall,hlim⟩ := sourceRetainedConstruction a.samples
    inferInstance (P.comap Subtype.val) inferInstance κ hk hκ8 ν hν
    (closedBall z₀ 1) (isCompact_closedBall _ _) (fun N ω => a.sourceFiniteGreenKernel_supported z₀ T N ω)
    A c m₀ m₂ hA hc hm₀ hm₂ kmin hfirst hsecond htail
  exact ⟨T,D,b,p,k₀,hT,hD,hb,hp,hlim⟩
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
lemma source_actual_retained_pathwise (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz₀ : 2 < z₀.im) (T : ℝ≥0) (D b : ℝ) (hD : 0 < D) (hb : 0 < b) (k₀ : ℕ)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (ω : a.samples) (hω : ∃ᶠ N in atTop, ENNReal.ofReal b ≤
      retainedMeasure κ D (a.sourceFiniteGreenKernel z₀ T) k₀ N ω (closedBall z₀ 1)) :
    0 < hausdorffGauge h (γ ω '' Icc 0 T) := by
  let ν := a.sourceFiniteGreenKernel z₀ T
  let (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hκ hκ8 z₀ hz₀ T N
  let μ (N : ℕ) : FiniteMeasure ℂ := ⟨retainedMeasure κ D ν k₀ N ω, by
    dsimp [retainedMeasure]; infer_instance⟩
  have hmass : ∃ᶠ N in atTop, (⟨b,hb.le⟩ : ℝ≥0) ≤ (μ N).mass := by
    apply hω.mono
    intro N hN
    have hm : ENNReal.ofReal b ≤ (μ N : Measure ℂ) univ :=
      hN.trans (measure_mono (subset_univ _))
    change b ≤ ((μ N).mass : ℝ)
    have ht := ENNReal.toReal_mono (measure_ne_top (μ N : Measure ℂ) univ) hm
    simpa only [ENNReal.toReal_ofReal hb.le, ← FiniteMeasure.ennreal_mass,
      ENNReal.coe_toReal] using ht
  have hK (N : ℕ) : μ N (closedBall z₀ 1)ᶜ = 0 := by
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact retainedMeasure_zero_of_zero κ D ν k₀ N ω (a.sourceFiniteGreenKernel_supported z₀ T N ω)
  have hcarrier (N : ℕ) : (μ N : Measure ℂ) (cthickening ((2:ℝ)^(-(N:ℝ))) (γ ω '' Icc 0 T))ᶜ = 0 :=
    retainedMeasure_zero_of_zero κ D ν k₀ N ω (a.sourceFiniteGreenKernel_carrier z₀ T N ω)
  have htest (N k : ℕ) (hk₀ : k₀ ≤ k) (hkN : k ≤ N) (ij : ℤ × ℤ) :
      (μ N (retainedDyadicSquare k ij) : ℝ≥0∞) ≤ ENNReal.ofReal (retainedThreshold κ D k) := by
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact retainedMeasure_square_bound κ D ν k₀ N ω k hk₀ hkN ij
  exact sourceRetainedDyadic_proved κ hκ hκ8 h hh hf (closedBall z₀ 1) (γ ω '' Icc 0 T)
    (isCompact_closedBall _ _) (isCompact_Icc.image (a.trace_continuous ω)).isClosed
    μ ⟨b,hb.le⟩ hb hmass hK (fun N => (2:ℝ)^(-(N:ℝ))) source_dyadic_tendsto hcarrier D hD k₀ htest
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourceActualRetainedLowerTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∃ (T : ℝ≥0) (E : Set a.samples), 0 < T ∧ MeasurableSet E ∧
    0 < (P.comap Subtype.val) E ∧
    ∀ ω ∈ E, 0 < hausdorffGauge h (γ ω '' Set.Icc 0 T)
theorem sourceActualRetainedLower_proved : SourceActualRetainedLowerTarget := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz₀ h hh hf
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  obtain ⟨T,D,b,p,k₀,hT,hD,hb,hp,hlim⟩ := a.source_actual_retained_experiment hκ hκ8 z₀ hz₀
  let ν := a.sourceFiniteGreenKernel z₀ T
  let (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hk hκ8 z₀ hz₀ T N
  let E : Set a.samples := {ω | ∃ᶠ N in atTop, ENNReal.ofReal b ≤
    retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)}
  have hE : MeasurableSet E := by
    have heq : E = ⋂ n : ℕ, ⋃ N ≥ n,
        {ω | ENNReal.ofReal b ≤ retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)} := by
      ext ω
      simp [E,frequently_atTop]
    rw [heq]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun N => MeasurableSet.iUnion
      (fun _ => measurableSet_le measurable_const (retainedMeasure_measurable κ D ν k₀ N measurableSet_closedBall))))
  refine ⟨T,E,hT,hE,(ENNReal.ofReal_pos.mpr hp).trans_le hlim,?_⟩
  intro ω hω
  exact a.source_actual_retained_pathwise hk hκ8 z₀ hz₀ T D b (zero_lt_one.trans_le hD) hb
    k₀ h hh hf ω hω
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_gauge_lipschitz_image_le (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {K : ℝ≥0} {f : ℂ → ℂ} {S : Set ℂ} (hLip : LipschitzOnWith K f S) :
    hausdorffGauge h (f '' S) ≤
      ENNReal.ofReal ((max (K : ℝ) 1)^dimension κ)*hausdorffGauge h S := by
  let L : ℝ≥0 := max K 1
  have hL : 1 ≤ (L : ℝ) := le_max_right _ _
  have hLp : 0 < (L : ℝ) := zero_lt_one.trans_le hL
  have hLC : LipschitzOnWith L f S := hLip.weaken (le_max_left _ _)
  have himg (t : Set ℂ) : ediam (f '' (t ∩ S)) ≤ (L:ℝ≥0∞)*ediam t := by
    simpa only [NNReal.coe_one,ENNReal.rpow_one] using hLC.holderOnWith.ediam_image_inter_le t
  obtain ⟨a,ha,hscale⟩ := source_gauge_bounded_scaling κ hκ hκ8 h hh hf (L:ℝ) hL
  let C : ℝ≥0∞ := ENNReal.ofReal ((L:ℝ)^dimension κ)
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hLp _)).ne'
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  change hausdorffGauge h (f '' S) ≤ C*hausdorffGauge h S
  simp only [hausdorffGauge,Measure.mkMetric_apply,ENNReal.mul_iSup,
    ENNReal.mul_iInf_of_ne hC0 hCt,←ENNReal.tsum_mul_left]
  refine iSup_le fun R => iSup_le fun hR => ?_
  have ht : Tendsto (fun d : ℝ≥0∞ => (L:ℝ≥0∞)*d) (𝓝 0) (𝓝 0) := by
    simpa using (ENNReal.continuous_const_mul (a := (L:ℝ≥0∞)) ENNReal.coe_ne_top).tendsto 0
  obtain ⟨δ,hδ,Hδ⟩ := ENNReal.nhds_zero_basis_Iic.eventually_iff.mp
    (ht.eventually (gt_mem_nhds hR))
  let ε := min δ (ENNReal.ofReal a)
  have hε : 0 < ε := lt_min hδ (ENNReal.ofReal_pos.mpr ha)
  have hεa : ε ≤ ENNReal.ofReal a := min_le_right _ _
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hεa
  refine le_iSup₂_of_le ε hε <| iInf₂_mono' fun t hSt =>
    ⟨fun n => f '' (t n ∩ S), ?_, iInf_mono' fun htε => ⟨?_,?_⟩⟩
  · grw [←image_iUnion,←iUnion_inter,←hSt,inter_self]
  · intro n
    exact (himg (t n)).trans (Hδ ((htε n).trans (min_le_left _ _))).le
  · apply ENNReal.tsum_le_tsum
    intro n
    simp only [iSup_le_iff,image_nonempty]
    intro hn
    simp only [Nonempty.mono ((t n).inter_subset_left) hn,ciSup_pos]
    have hd : ediam (t n) ≠ ⊤ := ne_top_of_le_ne_top hεt (htε n)
    have hda : (ediam (t n)).toReal ≤ a := by
      simpa only [ENNReal.toReal_ofReal ha.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top ((htε n).trans hεa)
    have hprod : (L:ℝ≥0∞)*ediam (t n) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hd
    have him := ENNReal.toReal_mono hprod (himg (t n))
    rw [ENNReal.toReal_mul,ENNReal.coe_toReal] at him
    change ENNReal.ofReal (h (ediam (f '' (t n ∩ S))).toReal) ≤
      ENNReal.ofReal ((L:ℝ)^dimension κ)*ENNReal.ofReal (h (ediam (t n)).toReal)
    rw [←ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hLp) _)]
    apply ENNReal.ofReal_le_ofReal
    exact (hh.monotoneOn ENNReal.toReal_nonneg (mul_nonneg hLp.le ENNReal.toReal_nonneg) him).trans
      (hscale _ ENNReal.toReal_nonneg hda)

lemma source_gauge_lipschitz_null (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {K : ℝ≥0} {f : ℂ → ℂ} {S : Set ℂ} (hLip : LipschitzOnWith K f S)
    (hS : hausdorffGauge h S = 0) : hausdorffGauge h (f '' S) = 0 := by
  have hb : hausdorffGauge h (f '' S) ≤ 0 := by
    simpa only [hS,mul_zero] using source_gauge_lipschitz_image_le κ hκ hκ8 h hh hf hLip
  exact le_antisymm hb zero_le
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_gauge_holomorphic_compact_null (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {f : ℂ → ℂ} {D K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K)
    (hKD : K ⊆ D) (hd : DifferentiableOn ℂ f D) (hz : hausdorffGauge h K = 0) :
    hausdorffGauge h (f '' K) = 0 := by
  classical
  have hlocal (x : K) : ∃ L : ℝ≥0, ∃ V : Set ℂ, V ∈ 𝓝 (x:ℂ) ∧ LipschitzOnWith L f V :=
    (hd.analyticAt (hD.mem_nhds (hKD x.property))).contDiffAt.exists_lipschitzOnWith
  choose L V hV hLip using hlocal
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover (fun x : K => interior (V x))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr
      ⟨⟨x,hx⟩,mem_interior_iff_mem_nhds.mpr (hV ⟨x,hx⟩)⟩)
  apply measure_mono_null (t := ⋃ i : I, f '' (K ∩ V i.val))
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hI hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,⟨x,⟨hx,interior_subset hxi⟩,rfl⟩⟩
  · apply measure_iUnion_null
    intro i
    exact source_gauge_lipschitz_null κ hκ hκ8 h hh hf
      ((hLip i.val).mono inter_subset_right) (measure_mono_null inter_subset_left hz)

lemma source_inverse_chart_gauge_positive (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (U : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U η G F) (s : ℝ≥0)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (hpos : 0 < hausdorffGauge h K) :
    0 < hausdorffGauge h (F s '' K) := by
  have hGc : DifferentiableOn ℂ (G s) (survivingDomain η s) := hw.2.2.2.1 s
  have hFc : ContinuousOn (F s) upperHalfPlane := (hw.2.2.2.2.1 s).continuousOn
  have hFK : IsCompact (F s '' K) := hK.image_of_continuousOn (hFc.mono hKH)
  have hFD : F s '' K ⊆ survivingDomain η s := by
    rintro _ ⟨z,hz,rfl⟩
    exact hw.2.2.2.2.2.2.1 s (hKH hz)
  have hId : G s '' (F s '' K) = K := by
    ext z
    constructor
    · rintro ⟨_,⟨w,hwK,rfl⟩,rfl⟩
      simpa only [hw.2.2.2.2.2.2.2.2.1 s w (hKH hwK)] using hwK
    · intro hz
      exact ⟨F s z,⟨z,hz,rfl⟩,hw.2.2.2.2.2.2.2.2.1 s z (hKH hz)⟩
  by_contra hn
  have hnull : hausdorffGauge h (F s '' K) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hhnull := source_gauge_holomorphic_compact_null κ hκ hκ8 h hh hf
    (isOpen_survivingDomain hw.1 s) hFK hFD hGc hnull
  rw [hId] at hhnull
  exact (ne_of_gt hpos) hhnull
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

theorem source_retained_compact_interior_lower_bound
    {h : ℝ → ℝ} (hh : IsGauge h) {K E : Set ℂ}
    (hK : IsCompact K) (hE : IsClosed E)
    (μ : ℕ → FiniteMeasure ℂ) (a C : ℝ≥0) (ha : 0 < a) (hC : 0 < C)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmass : ∀ n, a ≤ (μ n).mass)
    (hKsupport : ∀ n, μ n Kᶜ = 0)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcarrier : ∀ n, (μ n : Measure ℂ) (Metric.cthickening (e n) E)ᶜ = 0)
    (hball : ∀ x r, 0 < r → r < ρ →
      ∀ᶠ n in atTop, (μ n : Measure ℂ) (Metric.ball x r) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (h r)) :
    0 < hausdorffGauge h (K ∩ E) := by
  have hmpos (n : ℕ) : 0 < (μ n).mass := ha.trans_le (hmass n)
  have hmne (n : ℕ) : μ n ≠ 0 := (μ n).mass_nonzero_iff.mp (hmpos n).ne'
  let νs : ℕ → ProbabilityMeasure ℂ := fun n => (μ n).normalize
  have hνK (n : ℕ) : νs n ∈ {ν : ProbabilityMeasure ℂ | ν Kᶜ = 0} := by
    change (μ n).normalize Kᶜ = 0
    rw [(μ n).normalize_eq_of_nonzero (hmne n), hKsupport n, mul_zero]
  obtain ⟨ν, hνK, φ, hφ, hlim⟩ :=
    (normalized_supported_probability_compact hK).tendsto_subseq hνK
  have hνcarrier (n : ℕ) :
      ((νs ∘ φ) n : Measure ℂ) (Metric.cthickening ((e ∘ φ) n) E)ᶜ = 0 := by
    change ((μ (φ n)).normalize : Measure ℂ) (Metric.cthickening (e (φ n)) E)ᶜ = 0
    rw [(μ (φ n)).toMeasure_normalize_eq_of_nonzero (hmne (φ n)),
      Measure.coe_nnreal_smul_apply, hcarrier (φ n), mul_zero]
  have hνE : (ν : Measure ℂ) E = 1 :=
    (prob_compl_eq_zero_iff hE.measurableSet).mp
      (probability_limit_shrinking_carriers hlim hE (e ∘ φ)
        (he.comp hφ.tendsto_atTop) hνcarrier)
  have hνKE : (ν : Measure ℂ) (K ∩ E) = 1 := by
    apply (prob_compl_eq_zero_iff (hK.isClosed.inter hE).measurableSet).mp
    rw [compl_inter]
    apply measure_union_null
    · exact (ProbabilityMeasure.null_iff_toMeasure_null _ _).mp hνK
    · exact (prob_compl_eq_zero_iff hE.measurableSet).mpr hνE
  have hνball (x : ℂ) (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) :
      (ν : Measure ℂ) (Metric.ball x r) ≤ (↑(C / a) : ℝ≥0∞) * ENNReal.ofReal (h r) := by
    apply probability_limit_ball_bound hlim
    filter_upwards [hφ.tendsto_atTop.eventually (hball x r hr hrρ)] with n hn
    change ((μ (φ n)).normalize : Measure ℂ) (Metric.ball x r) ≤ _
    rw [(μ (φ n)).toMeasure_normalize_eq_of_nonzero (hmne (φ n)),
      Measure.coe_nnreal_smul_apply]
    have hfactor : (↑((μ (φ n)).mass⁻¹) : ℝ≥0∞) ≤ (↑(a⁻¹) : ℝ≥0∞) := by
      rw [ENNReal.coe_inv (hmpos (φ n)).ne', ENNReal.coe_inv ha.ne']
      exact ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr (hmass (φ n)))
    calc
      (↑((μ (φ n)).mass⁻¹) : ℝ≥0∞) * (μ (φ n) : Measure ℂ) (Metric.ball x r)
          ≤ (↑(a⁻¹) : ℝ≥0∞) * ((C : ℝ≥0∞) * ENNReal.ofReal (h r)) :=
        mul_le_mul' hfactor hn
      _ = (↑(C / a) : ℝ≥0∞) * ENNReal.ofReal (h r) := by
        rw [div_eq_mul_inv, ENNReal.coe_mul]
        ac_rfl
  have hdom := gauge_mass_distribution hh (ν : Measure ℂ) (C / a)
    (div_pos hC ha) ρ hρ hνball
  by_contra hn
  have hz : hausdorffGauge h (K ∩ E) = 0 := le_antisymm (le_of_not_gt hn) bot_le
  have hbound := Measure.le_iff'.mp hdom (K ∩ E)
  simp only [hνKE, Measure.smul_apply, hz, smul_eq_mul, mul_zero, not_le_of_gt zero_lt_one]
    at hbound

 
theorem source_retained_compact_interior_lower_bound_of_frequently
    {h : ℝ → ℝ} (hh : IsGauge h) {K E : Set ℂ}
    (hK : IsCompact K) (hE : IsClosed E)
    (μ : ℕ → FiniteMeasure ℂ) (a C : ℝ≥0) (ha : 0 < a) (hC : 0 < C)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmass : ∃ᶠ n in atTop, a ≤ (μ n).mass)
    (hKsupport : ∀ n, μ n Kᶜ = 0)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hcarrier : ∀ n, (μ n : Measure ℂ) (Metric.cthickening (e n) E)ᶜ = 0)
    (hball : ∀ x r, 0 < r → r < ρ →
      ∀ᶠ n in atTop, (μ n : Measure ℂ) (Metric.ball x r) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (h r)) :
    0 < hausdorffGauge h (K ∩ E) := by

  obtain ⟨φ, hφ, hm⟩ := Filter.subseq_forall_of_frequently (p := fun n : ℕ => a ≤ (μ n).mass)
    (x := id) tendsto_id hmass
  apply source_retained_compact_interior_lower_bound hh hK hE (μ ∘ φ) a C ha hC ρ hρ hm
    (fun n => hKsupport (φ n)) (e ∘ φ) (he.comp hφ) (fun n => hcarrier (φ n))
  intro x r hr hrρ
  exact hφ.eventually (hball x r hr hrρ)

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def SourceRetainedDyadicInteriorTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∀ K E : Set ℂ, IsCompact K → IsClosed E →
  ∀ μ : ℕ → FiniteMeasure ℂ, ∀ a : ℝ≥0, 0 < a →
  (∃ᶠ N in atTop, a ≤ (μ N).mass) →
  (∀ N, μ N Kᶜ = 0) →
  ∀ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) →
  (∀ N, (μ N : Measure ℂ) (Metric.cthickening (e N) E)ᶜ = 0) →
  ∀ D : ℝ, 0 < D → ∀ k₀ : ℕ,
  (∀ N k, k₀ ≤ k → k ≤ N → ∀ ij : ℤ × ℤ,
    μ N (retainedDyadicSquare k ij) ≤ ENNReal.ofReal (retainedThreshold κ D k)) →
  0 < hausdorffGauge h (K ∩ E)
theorem sourceRetainedDyadicInterior_proved : SourceRetainedDyadicInteriorTarget := by
  intro κ hκ hκ8 h hh hf K E hK hE μ a ha hmass hKsupport e he hcarrier D hD k₀ htest
  obtain ⟨b, hb, hscale⟩ := source_gauge_bounded_scaling κ hκ hκ8 h hh hf 2 (by norm_num)
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp
    (retained_threshold_gauge_eventually κ hκ8 h hf D hD.le)
  let J := max k₀ k₁
  let ρ : ℝ := min 1 (min b ((1/2:ℝ)^J/2))
  have hρ : 0 < ρ := lt_min (by norm_num) (lt_min hb (by positivity))
  let C : ℝ≥0 := ⟨9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ, by positivity⟩
  have hC : 0 < C := by change 0 < 9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ; positivity
  apply source_retained_compact_interior_lower_bound_of_frequently hh hK hE μ a C ha hC ρ hρ
    hmass hKsupport e he hcarrier
  intro x r hr hrρ
  have hr1 : r ≤ 1 := hrρ.le.trans (min_le_left _ _)
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have hside : (1/2:ℝ)^k < 2*r := by rw [pow_succ] at hklo; linarith
  have hrJ : 2*r < (1/2:ℝ)^J := by
    have hv : r < (1/2:ℝ)^J/2 := hrρ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hJk : J ≤ k := (pow_lt_pow_iff_right_of_lt_one₀
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)).mp (hside.trans hrJ) |>.le
  have hbound : retainedThreshold κ D k ≤
      D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ * h r := by
    have hmono : h ((1/2:ℝ)^k) ≤ h (2*r) :=
      hh.monotoneOn (show 0 ≤ (1/2:ℝ)^k by positivity)
        (show 0 ≤ 2*r by positivity) hside.le
    have hrb : r ≤ b := hrρ.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    calc
      retainedThreshold κ D k ≤ D * (2:ℝ)^(codimension κ/2) * h ((1/2:ℝ)^k) :=
        hk₁ k ((le_max_right _ _).trans hJk)
      _ ≤ D * (2:ℝ)^(codimension κ/2) * ((2:ℝ)^dimension κ * h r) :=
        mul_le_mul_of_nonneg_left (hmono.trans (hscale r hr.le hrb)) (by positivity)
      _ = _ := by ring
  filter_upwards [eventually_ge_atTop k] with N hN
  calc
    (μ N : Measure ℂ) (Metric.ball x r) ≤ 9 * ENNReal.ofReal (retainedThreshold κ D k) :=
      retained_dyadic_ball_bound (μ N) k _ (by
        simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
          htest N k ((le_max_left _ _).trans hJk) hN) x r hkhi
    _ = ENNReal.ofReal (9 * retainedThreshold κ D k) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤9)]
      norm_num
    _ ≤ ENNReal.ofReal ((C:ℝ)*h r) := by
      apply ENNReal.ofReal_le_ofReal
      change 9 * retainedThreshold κ D k ≤
        (9 * D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ) * h r
      calc
        9 * retainedThreshold κ D k ≤ 9 * (D * (2:ℝ)^(codimension κ/2) * (2:ℝ)^dimension κ * h r) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ = _ := by ring
    _ = (C:ℝ≥0∞) * ENNReal.ofReal (h r) := by
      rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
lemma source_actual_retained_interior_pathwise (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz₀ : 2 < z₀.im) (T : ℝ≥0) (D b : ℝ) (hD : 0 < D) (hb : 0 < b) (k₀ : ℕ)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (ω : a.samples) (hω : ∃ᶠ N in atTop, ENNReal.ofReal b ≤
      retainedMeasure κ D (a.sourceFiniteGreenKernel z₀ T) k₀ N ω (closedBall z₀ 1)) :
    0 < hausdorffGauge h (closedBall z₀ 1 ∩ (γ ω '' Icc 0 T)) := by
  let ν := a.sourceFiniteGreenKernel z₀ T
  let (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hκ hκ8 z₀ hz₀ T N
  let μ (N : ℕ) : FiniteMeasure ℂ := ⟨retainedMeasure κ D ν k₀ N ω, by
    dsimp [retainedMeasure]; infer_instance⟩
  have hmass : ∃ᶠ N in atTop, (⟨b,hb.le⟩ : ℝ≥0) ≤ (μ N).mass := by
    apply hω.mono
    intro N hN
    have hm : ENNReal.ofReal b ≤ (μ N : Measure ℂ) univ :=
      hN.trans (measure_mono (subset_univ _))
    change b ≤ ((μ N).mass : ℝ)
    have ht := ENNReal.toReal_mono (measure_ne_top (μ N : Measure ℂ) univ) hm
    simpa only [ENNReal.toReal_ofReal hb.le, ← FiniteMeasure.ennreal_mass,
      ENNReal.coe_toReal] using ht
  have hK (N : ℕ) : μ N (closedBall z₀ 1)ᶜ = 0 := by
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact retainedMeasure_zero_of_zero κ D ν k₀ N ω (a.sourceFiniteGreenKernel_supported z₀ T N ω)
  have hcarrier (N : ℕ) : (μ N : Measure ℂ) (cthickening ((2:ℝ)^(-(N:ℝ))) (γ ω '' Icc 0 T))ᶜ = 0 :=
    retainedMeasure_zero_of_zero κ D ν k₀ N ω (a.sourceFiniteGreenKernel_carrier z₀ T N ω)
  have htest (N k : ℕ) (hk₀ : k₀ ≤ k) (hkN : k ≤ N) (ij : ℤ × ℤ) :
      (μ N (retainedDyadicSquare k ij) : ℝ≥0∞) ≤ ENNReal.ofReal (retainedThreshold κ D k) := by
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact retainedMeasure_square_bound κ D ν k₀ N ω k hk₀ hkN ij
  exact sourceRetainedDyadicInterior_proved κ hκ hκ8 h hh hf (closedBall z₀ 1) (γ ω '' Icc 0 T)
    (isCompact_closedBall _ _) (isCompact_Icc.image (a.trace_continuous ω)).isClosed
    μ ⟨b,hb.le⟩ hb hmass hK (fun N => (2:ℝ)^(-(N:ℝ))) source_dyadic_tendsto hcarrier D hD k₀ htest
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourceInteriorRetainedTransferTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∃ (T : ℝ≥0) (E : Set a.samples), 0 < T ∧ MeasurableSet E ∧
    0 < (P.comap Subtype.val) E ∧ ∀ ω ∈ E,
      0 < hausdorffGauge h (Metric.closedBall z₀ 1 ∩ (γ ω '' Set.Icc 0 T)) ∧
      ∀ (U : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
        IsCapacityTwoWitness U η G F → ∀ s : ℝ≥0,
          0 < hausdorffGauge h (F s '' (Metric.closedBall z₀ 1 ∩ (γ ω '' Set.Icc 0 T)))

theorem sourceInteriorRetainedTransfer_proved : SourceInteriorRetainedTransferTarget := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz₀ h hh hf
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  obtain ⟨T,D,b,p,k₀,hT,hD,hb,hp,hlim⟩ := a.source_actual_retained_experiment hκ hκ8 z₀ hz₀
  let ν := a.sourceFiniteGreenKernel z₀ T
  let (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hk hκ8 z₀ hz₀ T N
  let E : Set a.samples := {ω | ∃ᶠ N in atTop, ENNReal.ofReal b ≤
    retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)}
  have hE : MeasurableSet E := by
    have heq : E = ⋂ n : ℕ, ⋃ N ≥ n,
        {ω | ENNReal.ofReal b ≤ retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)} := by
      ext ω
      simp [E,frequently_atTop]
    rw [heq]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun N => MeasurableSet.iUnion
      (fun _ => measurableSet_le measurable_const (retainedMeasure_measurable κ D ν k₀ N measurableSet_closedBall))))
  refine ⟨T,E,hT,hE,(ENNReal.ofReal_pos.mpr hp).trans_le hlim,?_⟩
  intro ω hω
  have hpos := a.source_actual_retained_interior_pathwise hk hκ8 z₀ hz₀ T D b (zero_lt_one.trans_le hD) hb
    k₀ h hh hf ω hω
  refine ⟨hpos,?_⟩
  intro U η G F hw s
  exact source_inverse_chart_gauge_positive κ hk hκ8 h hh hf U η G F hw s
    ((isCompact_closedBall z₀ 1).inter_right (isCompact_Icc.image (a.trace_continuous ω)).isClosed)
    (fun z hz => zero_lt_one.trans (source_unit_ball_height hz₀ hz.1)) hpos
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance actualRetainedKernelDriverMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance actualRetainedKernelTraceMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance actualRetainedKernelDriverBorelSpace : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance actualRetainedKernelTraceBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_brownian_continuous_law_unique
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B B' : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hc' : ∀ ω, Continuous (fun t => B' t ω)) :
    P.map (sourceDriverPath B hc) = P.map (sourceDriverPath B' hc') := by
  have hL : IsProjectiveLimit (P.map (fun ω t => B t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (Measurable.of_eval hm)]
    exact (hB.hasLaw I).map_eq
  have hR : IsProjectiveLimit (P.map (fun ω t => B' t ω)) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map (Finset.measurable_restrict I) (Measurable.of_eval hm')]
    exact (hB'.hasLaw I).map_eq
  apply source_path_evaluation_embedding.map_injective
  have he := congrArg (Measure.map (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n))) (hL.unique hR)
  have hem : Measurable (fun p : ℝ≥0 → ℝ => fun n => p (denseSeq ℝ≥0 n)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [Measure.map_map source_path_evaluation_embedding.measurable (source_path_measurable _ hm),
    Measure.map_map source_path_evaluation_embedding.measurable (source_path_measurable _ hm')]
  rw [Measure.map_map hem (Measurable.of_eval hm),
    Measure.map_map hem (Measurable.of_eval hm')] at he
  exact he
 

def SourceTraceLawUniqueTarget : Prop :=
  ∀ {Ω : Type*} [_m : MeasurableSpace Ω] {P : Measure Ω} (κ : ℝ), 0 < κ → κ < 8 →
  ∀ (B B' : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → IsBrownianReal B' P →
  ∀ (_hm : ∀ t, Measurable (B t)) (_hm' : ∀ t, Measurable (B' t))
    (_hc : ∀ ω, Continuous (fun t => B t ω)) (_hc' : ∀ ω, Continuous (fun t => B' t ω))
    (γ η : Ω → ℝ≥0 → ℂ) (G F G' F' : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hw' : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B' t ω) (η ω) (G' ω) (F' ω)),
    P.map (sourceTracePath γ (fun ω => (hw ω).1)) =
      P.map (sourceTracePath η (fun ω => (hw' ω).1))
theorem sourceTraceLawUnique_proved : SourceTraceLawUniqueTarget := by
  intro Ω m P κ hκ hκ8 B B' hB hB' hm hm' hc hc' γ η G F G' F' hw hw'
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let bp := sourceDriverPath B hc
  let rp := sourceDriverPath B' hc'
  let gp := sourceTracePath γ (fun ω => (hw ω).1)
  let ep := sourceTracePath η (fun ω => (hw' ω).1)
  have hbm : Measurable bp := source_path_measurable bp hm
  have hrm : Measurable rp := source_path_measurable rp hm'
  have hγa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => gp ω t) := by
    apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω)
      ?_ (fun ω => continuous_const.mul (hc ω)) γ G F hw
    intro t
    exact measurable_const.mul
      ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable
  obtain ⟨Φ,hΦm,hΦ⟩ := source_trace_factor B hm hc gp hγa
  have hΦe (ω : Ω) : Φ (bp ω) = gp ω := (congrFun hΦ ω).symm
  have hlaw : P.map bp = P.map rp := source_brownian_continuous_law_unique B B' hB hB' hm hm' hc hc'
  choose Q hQm hQ0 hQd using fun (t : ℝ≥0) (n : ℕ) =>
    source_canonical_reverse_flow κ t (a := 1 / ((n : ℝ) + 1)) (by positivity)
  let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hy : Tendsto a atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ha⟩
  have hQorig (ω : Ω) (t : ℝ≥0) (n : ℕ) :
      Q t n t (bp ω) = F ω t ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) := by
    apply (hw ω).reverse_flow_identifies t
      ((Real.sqrt κ * B t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
      (fun s => Q t n s (bp ω)) (hQ0 t n (bp ω))
    intro s hs
    exact (hQd t n (bp ω) s hs.1).mono Icc_subset_Ici_self
  have hQnew (ω : Ω) (t : ℝ≥0) (n : ℕ) :
      Q t n t (rp ω) = F' ω t ((Real.sqrt κ * B' t ω : ℝ) + (a n : ℂ) * I) := by
    apply (hw' ω).reverse_flow_identifies t
      ((Real.sqrt κ * B' t ω : ℝ) + (a n : ℂ) * I) (ha n) (by simp)
      (fun s => Q t n s (rp ω)) (hQ0 t n (rp ω))
    intro s hs
    exact (hQd t n (rp ω) s hs.1).mono Icc_subset_Ici_self
  have hQlimit (ω : Ω) (t : ℝ≥0) :
      Tendsto (fun n => Q t n t (bp ω)) atTop (𝓝 (Φ (bp ω) t)) := by
    have ht := ((hw ω).2.2.2.2.2.2.2.2.2.2.2.2 t).comp hy
    simpa only [hQorig,hΦe,gp,sourceTracePath,ContinuousMap.coe_mk,Function.comp_def] using ht
  have hset (t : ℝ≥0) : MeasurableSet
      {p : C(ℝ≥0,ℝ) | Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 (0:ℂ)) (fun n => (hQm t n t).sub
      ((continuous_eval_const t).measurable.comp hΦm))
  have hQR (t : ℝ≥0) : ∀ᵐ ω ∂P, Tendsto (fun n => Q t n t (rp ω)) atTop (𝓝 (Φ (rp ω) t)) := by
    have ho : ∀ᵐ p ∂P.map bp, Tendsto (fun n => Q t n t p - Φ p t) atTop (𝓝 0) := by
      apply (ae_map_iff hbm.aemeasurable (hset t)).2
      exact Eventually.of_forall (fun ω => tendsto_sub_nhds_zero_iff.mpr (hQlimit ω t))
    rw [hlaw] at ho
    filter_upwards [(ae_map_iff hrm.aemeasurable (hset t)).1 ho] with ω hω
    exact tendsto_sub_nhds_zero_iff.mp hω
  have hEQ : ∀ᵐ ω ∂P, Φ (rp ω) = ep ω := by
    filter_upwards [ae_all_iff.mpr (fun j : ℕ => hQR (denseSeq ℝ≥0 j))] with ω hω
    apply DFunLike.coe_injective
    apply (denseRange_denseSeq ℝ≥0).equalizer (Φ (rp ω)).continuous (ep ω).continuous
    funext j
    have ht := ((hw' ω).2.2.2.2.2.2.2.2.2.2.2.2 (denseSeq ℝ≥0 j)).comp hy
    have hn := hω j
    simp only [hQnew] at hn
    exact tendsto_nhds_unique hn ht
  have he := congrArg (Measure.map Φ) hlaw
  rw [Measure.map_map hΦm hbm,Measure.map_map hΦm hrm] at he
  have hcomp : Φ ∘ bp = gp := hΦ.symm
  rw [hcomp] at he
  exact he.trans (Measure.map_congr hEQ)
end
end SLEExactGauge
end

end OAI
