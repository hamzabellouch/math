import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierSpatialBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierTruncationBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators
open CoulombAnalysis CoulombPDE CoulombAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma deterministicBound_integrable_section {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u) (x : TFSpace) :
    Integrable (fun sample => u sample x) P := by
  obtain ⟨C,hC⟩ := hb {x} (isCompact_singleton)
  exact Integrable.of_bound (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
    (Eventually.of_forall fun sample => hC sample x (mem_singleton x))

lemma deterministicBound_integrable_test {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    {φ : TFSpace → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun p : Ω × TFSpace => u p.1 p.2*φ p.2) (P.prod volume) := by
  obtain ⟨C,hC⟩ := hb (tsupport φ) hc.isCompact
  have hi : Integrable (fun p : Ω × TFSpace => C*‖φ p.2‖) (P.prod volume) :=
    ((hφ.integrable_of_hasCompactSupport hc (μ := volume)).norm.const_mul C).comp_snd P
  apply hi.mono' (hu.mul (hφ.measurable.comp measurable_snd)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖u p.1 p.2*φ p.2‖ ≤ C*‖φ p.2‖
    rw [norm_mul]
    by_cases hp : φ p.2 = 0
    · simp only [hp,norm_zero,mul_zero,le_refl]
    · exact mul_le_mul_of_nonneg_right (hC p.1 p.2 (subset_tsupport φ hp)) (norm_nonneg _)

lemma average_measurable {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) : Measurable (fun x => ∫ sample, u sample x ∂P) := by
  have hm : StronglyMeasurable (Function.uncurry fun x sample => u sample x) :=
    (hu.comp measurable_swap).stronglyMeasurable
  exact hm.integral_prod_right.measurable

lemma average_deterministic_bound {u : Ω → TFSpace → ℝ}
    (hb : DeterministicLocalBound u) :
    DeterministicLocalBound (fun _ : Unit => fun x => ∫ sample, u sample x ∂P) := by
  intro K hK
  obtain ⟨C,hC⟩ := hb K hK
  refine ⟨C,fun _ x hx => ?_⟩
  calc
    _ ≤ ∫ _ : Ω, C ∂P := norm_integral_le_of_norm_le (integrable_const C)
      (Eventually.of_forall fun sample => hC sample x hx)
    _ = C := by simp

lemma average_continuous {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hc : ∀ᵐ sample ∂P, Continuous (u sample)) : Continuous (fun x => ∫ sample, u sample x ∂P) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨C,hC⟩ := hb (closedBall x 1) (isCompact_closedBall x 1)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => C)
  · exact Eventually.of_forall fun y =>
      (hu.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with y hy
    exact Eventually.of_forall fun sample => hC sample y (ball_subset_closedBall hy)
  · exact integrable_const C
  · exact hc.mono fun _ h => h.continuousAt

theorem weak_lower_average {U : Set TFSpace} {u h : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hh : Measurable (Function.uncurry h)) (hhb : DeterministicLocalBound h)
    (hw : ∀ᵐ sample ∂P, WeakLaplacianLowerOn U (u sample) (h sample)) :
    WeakLaplacianLowerOn U (fun x => ∫ sample, u sample x ∂P) (fun x => ∫ sample, h sample x ∂P) := by
  intro φ hφ hc hs hn
  have h1 := deterministicBound_integrable_test (P := P) hh hhb hφ.continuous hc
  have h2 := deterministicBound_integrable_test (P := P) hu hb
    (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)
  calc
    (∫ x, (∫ sample, h sample x ∂P)*φ x) = ∫ sample, (∫ x, h sample x*φ x) ∂P := by
      simp_rw [←integral_mul_const]
      exact (integral_integral_swap (f := fun sample x => h sample x*φ x) h1).symm
    _ ≤ ∫ sample, (∫ x, u sample x*Δ φ x) ∂P :=
      integral_mono_ae h1.integral_prod_left h2.integral_prod_left
        (hw.mono fun sample hω => hω φ hφ hc hs hn)
    _ = ∫ x, (∫ sample, u sample x ∂P)*Δ φ x := by
      rw [integral_integral_swap (f := fun sample x => u sample x*Δ φ x) h2]
      simp_rw [integral_mul_const]

end Average

theorem conditional_all_properties {Ω D : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace D]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → D} (hX : Measurable X)
    {p : Ω → Prop} (hp : ∀ᵐ sample ∂P, p sample) :
    ∀ᵐ d ∂P.map X, ∀ᵐ sample ∂condDistrib id X P d, p sample := by
  apply Measure.ae_ae_of_ae_comp
  rw [condDistrib_comp_map hX.aemeasurable measurable_id.aemeasurable,Measure.map_id]
  exact hp

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

open CoulombAnalysis CoulombPDE CoulombAtom

lemma DeterministicLocalBound.add {Ω : Type*} {u v : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) (hv : DeterministicLocalBound v) :
    DeterministicLocalBound (fun sample x => u sample x+v sample x) := by
  intro K hK
  obtain ⟨A,hA⟩ := hu K hK
  obtain ⟨B,hB⟩ := hv K hK
  exact ⟨A+B,fun sample x hx => (norm_add_le _ _).trans (add_le_add (hA sample x hx) (hB sample x hx))⟩

lemma DeterministicLocalBound.spatial_comp {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) {F : TFSpace → ℝ → ℝ}
    (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2)) :
    DeterministicLocalBound (fun sample x => F x (u sample x)) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  obtain ⟨D,_,hD⟩ := ((hK.prod (isCompact_closedBall (0:ℝ) C)).image hF).isBounded.exists_pos_norm_lt
  refine ⟨D,fun sample x hx => ?_⟩
  exact (hD _ ⟨(x,u sample x),⟨hx,by simpa only [mem_closedBall,dist_zero_right] using hC sample x hx⟩,rfl⟩).le

lemma DeterministicLocalBound.bounded_mul {Ω : Type*} {u : Ω → TFSpace → ℝ}
    (hu : DeterministicLocalBound u) {χ : TFSpace → ℝ} (hχ : ∀ x, ‖χ x‖ ≤ 1) :
    DeterministicLocalBound (fun sample x => χ x*u sample x) := by
  intro K hK
  obtain ⟨C,hC⟩ := hu K hK
  refine ⟨C,fun sample x hx => ?_⟩
  calc
    ‖χ x*u sample x‖ = ‖χ x‖*‖u sample x‖ := norm_mul _ _
    _ ≤ 1*‖u sample x‖ := mul_le_mul_of_nonneg_right (hχ x) (norm_nonneg _)
    _ ≤ C := by simpa only [one_mul] using hC sample x hx

lemma deterministicBound_locallyIntegrable {u : TFSpace → ℝ}
    (hu : Measurable u) (hb : DeterministicLocalBound (fun _ : Unit => u)) :
    LocallyIntegrable u := by
  intro x
  obtain ⟨C,hC⟩ := hb (closedBall x 1) (isCompact_closedBall x 1)
  refine ⟨closedBall x 1,closedBall_mem_nhds x (by norm_num : (0:ℝ)<1),?_⟩
  apply (integrableOn_const (C := C) (isCompact_closedBall x 1).measure_lt_top.ne).mono'
    hu.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
  exact hC () y hy

lemma average_locallyIntegrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u) :
    LocallyIntegrable (fun x => ∫ sample, u sample x ∂P) :=
  deterministicBound_locallyIntegrable (average_measurable hu) (average_deterministic_bound hb)

theorem weak_spatial_average {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U : Set TFSpace} {u g : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hub : DeterministicLocalBound u)
    (huc : ∀ᵐ sample ∂P, Continuous (u sample))
    (hg : Measurable (Function.uncurry g)) (hgb : DeterministicLocalBound g)
    {χ : TFSpace → ℝ} (hχ : Measurable χ) (hχb : ∀ x, ‖χ x‖ ≤ 1) (hχn : ∀ x, 0 ≤ χ x)
    {F : TFSpace → ℝ → ℝ} (hF : Continuous (fun p : TFSpace × ℝ => F p.1 p.2))
    (hFc : ∀ x, ConvexOn ℝ univ (F x))
    (hw : ∀ᵐ sample ∂P, WeakLaplacianLowerOn U (u sample) (fun x => g sample x+χ x*F x (u sample x))) :
    WeakLaplacianLowerOn U (fun x => ∫ sample, u sample x ∂P)
      (fun x => (∫ sample, g sample x ∂P)+χ x*F x (∫ sample, u sample x ∂P)) := by
  have hfm : Measurable (Function.uncurry fun sample x => F x (u sample x)) :=
    hF.measurable.comp (measurable_snd.prodMk hu)
  have hfb := hub.spatial_comp hF
  have hsm : Measurable (Function.uncurry fun sample x => g sample x+χ x*F x (u sample x)) :=
    hg.add ((hχ.comp measurable_snd).mul hfm)
  have hsb := hgb.add (hfb.bounded_mul hχb)
  have hsl := average_locallyIntegrable (P := P) hsm hsb
  have hgl := average_locallyIntegrable (P := P) hg hgb
  have huc' := average_continuous hu hub huc
  have htl := spatial_source_locallyIntegrable hgl hχ hχb hF huc'
  apply (weak_lower_average hu hub hsm hsb hw).source_mono hsl htl
  intro x _
  have hiu := deterministicBound_integrable_section (P := P) hu hub x
  have hig := deterministicBound_integrable_section (P := P) hg hgb x
  have hif := deterministicBound_integrable_section (P := P) hfm hfb x
  have hj := (hFc x).map_integral_le
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) hiu hif
  rw [integral_add hig (hif.const_mul (χ x)),integral_const_mul]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hj (hχn x)) _

end CoulombBarrier

end

end OAI
