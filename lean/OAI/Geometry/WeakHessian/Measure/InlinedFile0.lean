import Mathlib
import OAI.Geometry.WeakHessian.Model

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

variable {m ν : Measure X}

omit [BorelSpace X]

lemma IsTestPlan.of_measure_le_smul {π : Measure (Curve X)}
    (hπ : IsTestPlan m π) {C : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) :
    IsTestPlan ν π := by
  obtain ⟨hp, ⟨D, hD⟩, hac, he⟩ := hπ
  refine ⟨hp, ⟨D*C, fun t => ?_⟩, hac, he⟩
  calc
    Measure.map (fun γ : Curve X => γ t) π ≤ (D : ℝ≥0∞) • m := hD t
    _ ≤ (D : ℝ≥0∞) • ((C : ℝ≥0∞) • ν) :=
      by gcongr
    _ = ((D*C : ℝ≥0) : ℝ≥0∞) • ν := by rw [smul_smul, ENNReal.coe_mul]

lemma isTestPlan_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (π : Measure (Curve X)) : IsTestPlan m π ↔ IsTestPlan ν π :=
  ⟨fun h => h.of_measure_le_smul hm, fun h => h.of_measure_le_smul hν⟩

lemma LocallyL2.of_measure_le_smul {f : X → ℝ} (hf : LocallyL2 m f)
    {C : ℝ≥0} (hν : ν ≤ (C : ℝ≥0∞) • m) : LocallyL2 ν f := by
  intro o R hR
  exact MemLp.of_measure_le_smul (c := (C : ℝ≥0∞)) ENNReal.coe_ne_top
    (by simpa only [Measure.restrict_smul] using
      Measure.restrict_mono_measure hν (Metric.ball o R)) (hf o R hR)

lemma locallyL2_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f : X → ℝ) : LocallyL2 m f ↔ LocallyL2 ν f :=
  ⟨fun h => h.of_measure_le_smul hν, fun h => h.of_measure_le_smul hm⟩

lemma IsLocalWeakUpperGradient.of_measure_le_smul {D : ℝ≥0}
    (hν : ν ≤ (D : ℝ≥0∞) • m)
    {f W : X → ℝ} (hw : IsLocalWeakUpperGradient m f W) :
    IsLocalWeakUpperGradient ν f W := by
  refine ⟨hw.1.of_measure_le_smul hν,
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le hw.2.1, ?_⟩
  intro π hπ hb
  exact hw.2.2 π (hπ.of_measure_le_smul hν) hb

lemma localWeakUpperGradient_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f W : X → ℝ) : IsLocalWeakUpperGradient m f W ↔
      IsLocalWeakUpperGradient ν f W :=
  ⟨fun h => h.of_measure_le_smul hν, fun h => h.of_measure_le_smul hm⟩

lemma IsMinimalLocalWeakUpperGradient.change_measure {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    {f W : X → ℝ} (hw : IsMinimalLocalWeakUpperGradient m f W) :
    IsMinimalLocalWeakUpperGradient ν f W := by
  refine ⟨hw.1.of_measure_le_smul hν, ?_⟩
  intro W' hw'
  exact (Measure.absolutelyContinuous_of_le_smul hν).ae_le
    (hw.2 W' (hw'.of_measure_le_smul hm))

lemma minimalLocalWeakUpperGradient_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f W : X → ℝ) : IsMinimalLocalWeakUpperGradient m f W ↔
      IsMinimalLocalWeakUpperGradient ν f W :=
  ⟨fun h => h.change_measure hm hν, fun h => h.change_measure hν hm⟩

lemma weakGradient_isMinimal {f : X → ℝ}
    (hf : ∃ W, IsMinimalLocalWeakUpperGradient m f W) :
    IsMinimalLocalWeakUpperGradient m f (weakGradient m f) := by
  simpa only [weakGradient, dite_eq_left hf] using Classical.choose_spec hf

theorem weakGradient_eq_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f : X → ℝ) : weakGradient m f =ᵐ[m] weakGradient ν f := by
  by_cases hf : ∃ W, IsMinimalLocalWeakUpperGradient m f W
  · have hfν : ∃ W, IsMinimalLocalWeakUpperGradient ν f W := by
      obtain ⟨W, hW⟩ := hf
      exact ⟨W, hW.change_measure hm hν⟩
    have hwm := weakGradient_isMinimal hf
    have hwν := (weakGradient_isMinimal hfν).change_measure hν hm
    filter_upwards [hwm.2 _ hwν.1, hwν.2 _ hwm.1] with x h₁ h₂
    exact le_antisymm h₁ h₂
  · have hfν : ¬ ∃ W, IsMinimalLocalWeakUpperGradient ν f W := by
      rintro ⟨W, hW⟩
      exact hf ⟨W, hW.change_measure hν hm⟩
    simp only [weakGradient, dite_eq_right hf, dite_eq_right hfν, Filter.EventuallyEq.refl]

theorem gamma_eq_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f g : X → ℝ) : gamma m f g =ᵐ[m] gamma ν f g := by
  filter_upwards [weakGradient_eq_of_comparable hm hν (fun x => f x + g x),
    weakGradient_eq_of_comparable hm hν (fun x => f x - g x)] with x hp hn
  simp only [gamma, hp, hn]

lemma localSobolev_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f : X → ℝ) : LocalSobolev m f ↔ LocalSobolev ν f := by
  simp only [LocalSobolev, locallyL2_iff_of_comparable hm hν,
    minimalLocalWeakUpperGradient_iff_of_comparable hm hν]

theorem sobolev_iff_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f : X → ℝ) : Sobolev m f ↔ Sobolev ν f := by
  have transfer : ∀ {μ₁ μ₂ : Measure X} {C₁ C₂ : ℝ≥0},
      μ₁ ≤ (C₁ : ℝ≥0∞) • μ₂ → μ₂ ≤ (C₂ : ℝ≥0∞) • μ₁ →
      Sobolev μ₁ f → Sobolev μ₂ f := by
    intro μ₁ μ₂ C₁ C₂ h₁ h₂ hf
    refine ⟨MemLp.of_measure_le_smul ENNReal.coe_ne_top h₂ hf.1,
      (localSobolev_iff_of_comparable h₁ h₂ f).mp hf.2.1, ?_⟩
    exact MemLp.ae_eq (weakGradient_eq_of_comparable h₂ h₁ f).symm
      (MemLp.of_measure_le_smul ENNReal.coe_ne_top h₂ hf.2.2)
  exact ⟨transfer hm hν, transfer hν hm⟩

def exponentialMeasure (m : Measure X) (V : X → ℝ) : Measure X :=
  m.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))

omit [MetricSpace X] in
lemma exponentialMeasure_le {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, V x ≤ B) :
    exponentialMeasure m V ≤ ENNReal.ofReal (Real.exp B) • m := by
  rw [← withDensity_const]
  exact withDensity_mono (ae_of_all m fun x =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hV x)))

omit [MetricSpace X] in
lemma measure_le_exponentialMeasure {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, -B ≤ V x) :
    m ≤ ENNReal.ofReal (Real.exp B) • exponentialMeasure m V := by
  calc
    m = m.withDensity (fun _ => 1) := withDensity_one.symm
    _ ≤ m.withDensity (ENNReal.ofReal (Real.exp B) •
        (fun x => ENNReal.ofReal (Real.exp (V x)))) := by
      apply withDensity_mono
      filter_upwards with x
      change 1 ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (Real.exp (V x))
      rw [← ENNReal.ofReal_mul (Real.exp_pos B).le, ← Real.exp_add]
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.one_le_exp_iff.mpr (by linarith [hV x]))
    _ = ENNReal.ofReal (Real.exp B) • exponentialMeasure m V :=
      withDensity_smul' _ _ ENNReal.ofReal_ne_top

omit [MetricSpace X] in
lemma exponentialMeasure_comparable {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) :
    m ≤ ENNReal.ofReal (Real.exp B) • exponentialMeasure m V ∧
      exponentialMeasure m V ≤ ENNReal.ofReal (Real.exp B) • m := by
  exact ⟨measure_le_exponentialMeasure fun x => (abs_le.mp (hV x)).1,
    exponentialMeasure_le fun x => (abs_le.mp (hV x)).2⟩

theorem weakGradient_exponentialMeasure {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) (f : X → ℝ) :
    weakGradient m f =ᵐ[m] weakGradient (exponentialMeasure m V) f := by
  obtain ⟨hm, hν⟩ := exponentialMeasure_comparable (m := m) hV
  exact weakGradient_eq_of_comparable (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν f

theorem gamma_exponentialMeasure {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) (f g : X → ℝ) :
    gamma m f g =ᵐ[m] gamma (exponentialMeasure m V) f g := by
  obtain ⟨hm, hν⟩ := exponentialMeasure_comparable (m := m) hV
  exact gamma_eq_of_comparable (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν f g

theorem sobolev_exponentialMeasure_iff {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) (f : X → ℝ) :
    Sobolev m f ↔ Sobolev (exponentialMeasure m V) f := by
  obtain ⟨hm, hν⟩ := exponentialMeasure_comparable (m := m) hV
  exact sobolev_iff_of_comparable (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν f

omit [MeasurableSpace X] [BorelSpace X] in

lemma absolutelyContinuous_of_dist_le {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ → X} {g : ℝ → Y} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ s ∈ Set.uIcc a b, ∀ t ∈ Set.uIcc a b,
      dist (f s) (f t) ≤ dist (g s) (g t)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hsmall => lt_of_le_of_lt ?_ (hbound E hE hsmall)⟩
  refine Finset.sum_le_sum fun i hi => ?_
  exact hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

omit [MeasurableSpace X] [BorelSpace X] in

lemma lipschitz_comp_absolutelyContinuous {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  change Tendsto _ _ (𝓝 0) at hf ⊢
  have hlim := hf.const_mul (L : ℝ)
  simp only [mul_zero] at hlim
  refine squeeze_zero (fun E => Finset.sum_nonneg fun i _ => dist_nonneg)
    (fun E => ?_) hlim
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hg.dist_le_mul _ _

lemma lintegral_lt_top_of_square {a : ℝ → ℝ≥0∞} (_ha : Measurable a)
    (hfinite : (∫⁻ t in Set.Icc (0 : ℝ) 1, (a t) ^ 2) < ∞) :
    (∫⁻ t in Set.Icc (0 : ℝ) 1, a t) < ∞ := by
  have hpoint : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ 2 := by
    intro x
    by_cases hx : x ≤ 1
    · exact hx.trans (le_add_right le_rfl)
    · have hx' : 1 ≤ x := le_of_not_ge hx
      calc
        x = x * 1 := (mul_one x).symm
        _ ≤ x * x := by gcongr
        _ ≤ 1 + x ^ 2 := by rw [pow_two]; exact le_add_left le_rfl
  calc
    (∫⁻ t in Set.Icc (0 : ℝ) 1, a t) ≤
        ∫⁻ t in Set.Icc (0 : ℝ) 1, 1 + (a t) ^ 2 :=
      lintegral_mono fun t => hpoint (a t)
    _ = (∫⁻ _t in Set.Icc (0 : ℝ) 1, (1 : ℝ≥0∞)) +
        ∫⁻ t in Set.Icc (0 : ℝ) 1, (a t) ^ 2 :=
      lintegral_add_left measurable_const _
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨by simp, hfinite⟩

omit [MeasurableSpace X] [BorelSpace X] in

lemma IsAC2.absolutelyContinuous {γ : Curve X} (hγ : IsAC2 γ) :
    AbsolutelyContinuousOnInterval (evalReal γ) 0 1 := by
  obtain ⟨a, ha, hfinite, hinc⟩ := hγ
  have hfin : (∫⁻ t in Set.Icc (0 : ℝ) 1, a t) < ∞ :=
    lintegral_lt_top_of_square ha hfinite
  have hane : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), a t ≠ ∞ :=
    (ae_lt_top ha hfin.ne).mono fun _ h => h.ne
  have hai : IntegrableOn (fun t => (a t).toReal) (Set.Icc (0 : ℝ) 1) :=
    (integrable_toReal_iff ha.aemeasurable hane).mpr hfin.ne
  have haint : IntervalIntegrable (fun t => (a t).toReal) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hai
  let A : ℝ → ℝ := fun t => ∫ r in (0 : ℝ)..t, (a r).toReal
  have hA : AbsolutelyContinuousOnInterval A 0 1 :=
    haint.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have heval (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      evalReal γ t = γ ⟨t, ht⟩ := by
    change γ (clampTime t) = γ ⟨t, ht⟩
    apply congrArg γ
    apply Subtype.ext
    simp only [clampTime, max_eq_right ht.1, min_eq_right ht.2]
  have hdom (s t : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
      (ht : t ∈ Set.Icc (0 : ℝ) 1) (hst : s ≤ t) :
      dist (evalReal γ s) (evalReal γ t) ≤ dist (A s) (A t) := by
    have hstsub : Set.Icc s t ⊆ Set.Icc (0 : ℝ) 1 :=
      fun r hr => ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    have hstfin : (∫⁻ r in Set.Icc s t, a r) ≠ ∞ :=
      ne_top_of_le_ne_top hfin.ne (lintegral_mono_set hstsub)
    have hstreal : (∫⁻ r in Set.Icc s t, a r).toReal = ∫ r in s..t, (a r).toReal := by
      rw [← integral_toReal ha.aemeasurable (ae_lt_top ha hstfin),
        integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hst]
    have hDs : IntervalIntegrable (fun r => (a r).toReal) volume 0 s :=
      haint.mono_set (by simpa only [Set.uIcc_of_le hs.1, Set.uIcc_of_le zero_le_one]
        using (show Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) 1 from
          fun r hr => ⟨hr.1, hr.2.trans hs.2⟩))
    have hDt : IntervalIntegrable (fun r => (a r).toReal) volume 0 t :=
      haint.mono_set (by simpa only [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]
        using (show Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 1 from
          fun r hr => ⟨hr.1, hr.2.trans ht.2⟩))
    have hprim : A t - A s = ∫ r in s..t, (a r).toReal :=
      intervalIntegral.integral_interval_sub_left hDt hDs
    rw [heval s hs, heval t ht]
    calc
      dist (γ ⟨s, hs⟩) (γ ⟨t, ht⟩) ≤ (∫⁻ r in Set.Icc s t, a r).toReal := by
        simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
          ENNReal.toReal_mono hstfin (hinc ⟨s, hs⟩ ⟨t, ht⟩ hst)
      _ = A t - A s := hstreal.trans hprim.symm
      _ ≤ dist (A s) (A t) := by rw [dist_comm, Real.dist_eq]; exact le_abs_self _
  apply absolutelyContinuous_of_dist_le hA
  intro s hs t ht
  rw [Set.uIcc_of_le zero_le_one] at hs ht
  rcases le_total s t with hst | hts
  · exact hdom s t hs ht hst
  · simpa only [dist_comm] using hdom t s ht hs hts

omit [MeasurableSpace X] [BorelSpace X] in

lemma deriv_comp_le_metricSpeed {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) {t : ℝ}
    (hd : DifferentiableAt ℝ (fun s => f (evalReal γ s)) t) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      (L : ℝ≥0∞) * metricSpeed γ t := by
  have hlim : Tendsto
      (fun s => ENNReal.ofReal (|f (evalReal γ s) - f (evalReal γ t)| / |s-t|))
      (𝓝[≠] t) (𝓝 (ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t|)) := by
    simpa only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv,
      Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using
      ENNReal.tendsto_ofReal (hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt).norm
  calc
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| =
        limsup (fun s => ENNReal.ofReal
          (|f (evalReal γ s) - f (evalReal γ t)| / |s-t|)) (𝓝[≠] t) := hlim.limsup_eq.symm
    _ ≤ limsup (fun s => (L : ℝ≥0∞) * ENNReal.ofReal
        (dist (evalReal γ s) (evalReal γ t) / |s-t|)) (𝓝[≠] t) := by
      refine limsup_le_limsup ?_
      filter_upwards with s
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L.coe_nonneg,
        ← mul_div_assoc]
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      simpa only [Real.dist_eq] using hf.dist_le_mul (evalReal γ s) (evalReal γ t)
    _ = (L : ℝ≥0∞) * metricSpeed γ t :=
      ENNReal.limsup_const_mul_of_ne_top ENNReal.coe_ne_top

omit [MeasurableSpace X] [BorelSpace X] in
lemma deriv_comp_le_metricSpeed_all {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      (L : ℝ≥0∞) * metricSpeed γ t := by
  by_cases hd : DifferentiableAt ℝ (fun s => f (evalReal γ s)) t
  · exact deriv_comp_le_metricSpeed hf γ hd
  · simp only [deriv_zero_of_not_differentiableAt hd, abs_zero, ENNReal.ofReal_zero]
    exact bot_le

omit [MeasurableSpace X] [BorelSpace X] in

lemma lipschitz_endpoint_bound {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {γ : Curve X} (hγ : IsAC2 γ) :
    ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ≤
      ∫⁻ t in Set.Icc (0 : ℝ) 1, (L : ℝ≥0∞) * metricSpeed γ t := by
  have hac := lipschitz_comp_absolutelyContinuous hf hγ.absolutelyContinuous
  calc
    ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
        ‖∫ t in Set.Icc (0 : ℝ) 1, deriv (fun s => f (evalReal γ s)) t‖ₑ := by
      rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one, hac.integral_deriv_eq_sub]
      simp [evalReal, clampTime, timeOne, timeZero]
      rfl
    _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun s => f (evalReal γ s)) t‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, (L : ℝ≥0∞) * metricSpeed γ t := by
      apply lintegral_mono
      intro t
      simpa only [← ofReal_norm, Real.norm_eq_abs]
        using deriv_comp_le_metricSpeed_all hf γ t

lemma lipschitz_isLocalWeakUpperGradient (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    IsLocalWeakUpperGradient m f (fun _ => (L : ℝ)) := by
  refine ⟨?_, ae_of_all m fun _ => L.coe_nonneg, ?_⟩
  · intro o R _hR
    let _ : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        hfinite (Metric.ball o R) Metric.isBounded_ball⟩
    exact memLp_const _
  · intro π hπ _hb
    apply lintegral_mono_ae
    filter_upwards [hπ.2.2.1] with γ hγ
    simpa only [ENNReal.ofReal_coe_nnreal] using lipschitz_endpoint_bound hf hγ

lemma weakGradient_le_lipschitz (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∀ᵐ x ∂m, weakGradient m f x ≤ (L : ℝ) := by
  by_cases h : ∃ D, IsMinimalLocalWeakUpperGradient m f D
  · exact (weakGradient_isMinimal h).2 _ (lipschitz_isLocalWeakUpperGradient hfinite hf)
  · simp only [weakGradient, dite_eq_right h, Pi.zero_apply]
    exact ae_of_all m fun _ => L.coe_nonneg

lemma LocallyL2.const_mul {f : X → ℝ} (hf : LocallyL2 m f) (c : ℝ) :
    LocallyL2 m (fun x => c * f x) :=
  fun o R hR => (hf o R hR).const_mul c

lemma isLocalWeakUpperGradient_const (c : ℝ) :
    IsLocalWeakUpperGradient m (fun _ => c) (fun _ => 0) := by
  refine ⟨fun _ _ _ => ?_, ae_of_all m fun _ => le_rfl, ?_⟩
  · exact MemLp.zero
  · intro π _hπ _hb
    simp only [sub_self, abs_zero, ENNReal.ofReal_zero, lintegral_zero]
    exact bot_le

lemma isMinimalLocalWeakUpperGradient_const (c : ℝ) :
    IsMinimalLocalWeakUpperGradient m (fun _ => c) (fun _ => 0) :=
  ⟨isLocalWeakUpperGradient_const c, fun _ hD => hD.2.1⟩

lemma IsMinimalLocalWeakUpperGradient.ae_eq {f D D' : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D)
    (hD' : IsMinimalLocalWeakUpperGradient m f D') : D =ᵐ[m] D' := by
  filter_upwards [hD.2 _ hD'.1, hD'.2 _ hD.1] with x hx hx'
  exact le_antisymm hx hx'

lemma weakGradient_ae_eq_of_isMinimal {f D : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) : weakGradient m f =ᵐ[m] D :=
  (weakGradient_isMinimal ⟨D, hD⟩).ae_eq hD

lemma weakGradient_const (c : ℝ) :
    weakGradient m (fun _ => c) =ᵐ[m] (fun _ => 0) :=
  weakGradient_ae_eq_of_isMinimal (isMinimalLocalWeakUpperGradient_const c)

lemma weakGradient_nonneg (f : X → ℝ) : ∀ᵐ x ∂m, 0 ≤ weakGradient m f x := by
  by_cases h : ∃ D, IsMinimalLocalWeakUpperGradient m f D
  · exact (weakGradient_isMinimal h).1.2.1
  · simp only [weakGradient, dite_eq_right h, Pi.zero_apply, le_refl, eventually_true]

lemma IsLocalWeakUpperGradient.const_mul {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (c : ℝ) :
    IsLocalWeakUpperGradient m (fun x => c * f x) (fun x => |c| * D x) := by
  refine ⟨hD.1.const_mul |c|, ?_, ?_⟩
  · filter_upwards [hD.2.1] with x hx
    exact mul_nonneg (abs_nonneg c) hx
  · intro π hπ hb
    calc
      (∫⁻ γ : Curve X, ENNReal.ofReal |c * f (γ timeOne) - c * f (γ timeZero)| ∂π) =
          ENNReal.ofReal |c| * ∫⁻ γ : Curve X,
            ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| ∂π := by
        simp_rw [← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal |c| * ∫⁻ γ : Curve X, ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π := by
        gcongr 1
        exact hD.2.2 π hπ hb
      _ = ∫⁻ γ : Curve X, ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (|c| * D (evalReal γ t)) * metricSpeed γ t ∂volume ∂π := by
        simp_rw [ENNReal.ofReal_mul (abs_nonneg c), mul_assoc,
          lintegral_const_mul' (ENNReal.ofReal |c|) _ ENNReal.ofReal_ne_top]

lemma IsMinimalLocalWeakUpperGradient.const_mul {f D : X → ℝ}
    (hD : IsMinimalLocalWeakUpperGradient m f D) {c : ℝ} (hc : c ≠ 0) :
    IsMinimalLocalWeakUpperGradient m (fun x => c * f x) (fun x => |c| * D x) := by
  refine ⟨hD.1.const_mul c, ?_⟩
  intro D' hD'
  have hinv := hD'.const_mul c⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at hinv
  filter_upwards [hD.2 _ hinv] with x hx
  calc
    |c| * D x ≤ |c| * (|c⁻¹| * D' x) :=
      mul_le_mul_of_nonneg_left hx (abs_nonneg c)
    _ = D' x := by rw [abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul]

lemma weakGradient_const_mul (c : ℝ) (f : X → ℝ) :
    weakGradient m (fun x => c * f x) =ᵐ[m] (fun x => |c| * weakGradient m f x) := by
  by_cases hc : c = 0
  · subst c
    simpa only [zero_mul, abs_zero] using (weakGradient_const (m := m) 0)
  by_cases hf : ∃ D, IsMinimalLocalWeakUpperGradient m f D
  · exact weakGradient_ae_eq_of_isMinimal ((weakGradient_isMinimal hf).const_mul hc)
  · have hcf : ¬ ∃ D, IsMinimalLocalWeakUpperGradient m (fun x => c * f x) D := by
      rintro ⟨D, hD⟩
      have hinv := hD.const_mul (inv_ne_zero hc)
      simp only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] at hinv
      exact hf ⟨_, hinv⟩
    simp only [weakGradient, dite_eq_right hcf, dite_eq_right hf, Pi.zero_apply, mul_zero]
    exact Filter.EventuallyEq.rfl

lemma gamma_self (f : X → ℝ) :
    gamma m f f =ᵐ[m] (fun x => (weakGradient m f x) ^ 2) := by
  have hsum : (fun x => f x + f x) = (fun x => 2 * f x) := by funext x; ring
  have hdiff : (fun x => f x - f x) = (fun _ => (0 : ℝ)) := by funext x; simp
  filter_upwards [weakGradient_const_mul (m := m) 2 f, weakGradient_const (m := m) 0]
    with x hx hz
  simp only [gamma, hsum, hdiff, hx, hz]
  norm_num
  ring

lemma IsLaplacian.energy_identity {u L : X → ℝ} (hL : IsLaplacian m u L) :
    (∫ x, (weakGradient m u x) ^ 2 ∂m) = -(∫ x, L x * u x ∂m) := by
  rw [← integral_congr_ae (gamma_self (m := m) u)]
  exact hL.2.2 u hL.1

lemma IsLaplacian.energy_le_graph_sq {u L : X → ℝ} (hL : IsLaplacian m u L) :
    (∫ x, (weakGradient m u x) ^ 2 ∂m) ≤
      ((∫ x, (u x) ^ 2 ∂m) + ∫ x, (L x) ^ 2 ∂m) / 2 := by
  have huSq := hL.1.1.integrable_sq
  have hLSq := hL.2.1.integrable_sq
  have hmul : Integrable (fun x => L x * u x) m := hL.2.1.integrable_mul hL.1.1
  calc
    (∫ x, (weakGradient m u x) ^ 2 ∂m) = ∫ x, -(L x * u x) ∂m := by
      rw [hL.energy_identity, integral_neg]
    _ ≤ ∫ x, ((u x) ^ 2 + (L x) ^ 2) / 2 ∂m := by
      apply integral_mono hmul.neg ((huSq.add hLSq).div_const 2)
      intro x
      change -(L x * u x) ≤ ((u x) ^ 2 + (L x) ^ 2) / 2
      nlinarith [sq_nonneg (u x + L x)]
    _ = ((∫ x, (u x) ^ 2 ∂m) + ∫ x, (L x) ^ 2 ∂m) / 2 := by
      rw [integral_div, integral_add huSq hLSq]

end WeakHessian

end
end InlinedFile0

end OAI
