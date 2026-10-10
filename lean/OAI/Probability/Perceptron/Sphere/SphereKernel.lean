import Mathlib
import OAI.Probability.Perceptron.Variational.TripleIndex

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem joint_gg_crossed_regions_null (μ : Measure PairedOverlapArray) [IsProbabilityMeasure μ]
    (hGG : JointGhirlandaGuerra μ)
    (hNo : ∀ᵐ Q ∂μ, ¬ ((Q 0 1).1 < (Q 0 2).1 ∧ (Q 0 2).2 < (Q 0 1).2))
    (s t : Set (ℝ × ℝ)) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : ∀ u ∈ s, ∀ v ∈ t, u.1 < v.1 ∧ v.2 < u.2) :
    μ {Q | Q 0 1 ∈ s} = 0 ∨ μ {Q | Q 0 1 ∈ t} = 0 := by
  let S : Set (PairedOverlapBlock 2) := {A | A 0 1 ∈ s}
  have hS : MeasurableSet S := hs.preimage
    ((measurable_pi_apply 1).comp (measurable_pi_apply 0))
  have hnull : μ (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 2 ∈ t}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hNo] with Q hQ
    rintro ⟨h₁, h₂⟩
    exact hQ (hst (Q 0 1) h₁ (Q 0 2) h₂)
  have hid := hGG 2 (by omega) 0 S hS t ht
  have hzero : μ.real (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 2 ∈ t}) = 0 := by
    simp only [measureReal_def, hnull, ENNReal.toReal_zero]
  have hsum : 0 ≤ ∑ j ∈ (Finset.univ.erase (0 : Fin 2)),
      μ.real (pairedBlock 2 ⁻¹' S ∩ {Q | Q 0 j ∈ t}) :=
    Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hprod : μ.real {Q | Q 0 1 ∈ s} * μ.real {Q | Q 0 1 ∈ t} = 0 := by
    change μ.real (pairedBlock 2 ⁻¹' S) * μ.real {Q | Q 0 1 ∈ t} = 0
    simp only [Fin.val_zero, Nat.cast_ofNat] at hid
    rw [hzero] at hid
    have h₁ := measureReal_nonneg (μ := μ) (s := pairedBlock 2 ⁻¹' S)
    have h₂ := measureReal_nonneg (μ := μ) (s := {Q | Q 0 1 ∈ t})
    nlinarith [mul_nonneg h₁ h₂]
  rcases mul_eq_zero.mp hprod with h | h
  · left
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)
  · right
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)

theorem weighted_kernel_homogeneous_eq_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] {D : X → ℝ} {K : X → X → ℝ} {B : ℝ}
    (hB : B < 1) (hD : ∀ᵐ r ∂μ, 0 < D r)
    (hK : ∀ r, Integrable (K r) μ) (hKpos : ∀ᵐ r ∂μ, ∀ᵐ s ∂μ, 0 ≤ K r s)
    (hrow : ∀ᵐ r ∂μ, (∫ s, K r s ∂μ) ≤ B * D r)
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hbounded : ∃ M : ℝ, ∀ᵐ r ∂μ, |f r| ≤ M)
    (heq : ∀ᵐ r ∂μ, f r * D r = ∫ s, K r s * f s ∂μ) :
    f =ᵐ[μ] 0 := by
  let C : ℝ := essSup (fun r => |f r|) μ
  obtain ⟨M, hM⟩ := hbounded
  have hb : IsBoundedUnder (· ≤ ·) (ae μ) (fun r => |f r|) :=
    isBoundedUnder_of_eventually_le hM
  have hcob : IsCoboundedUnder (· ≤ ·) (ae μ) (fun r => |f r|) :=
    isCoboundedUnder_le_of_le (ae μ) (fun r => abs_nonneg (f r))
  have hfC : ∀ᵐ r ∂μ, |f r| ≤ C := ae_le_essSup hb
  have hC : 0 ≤ C := by
    obtain ⟨r, hr⟩ := hfC.exists
    exact (abs_nonneg (f r)).trans hr
  have hsmall : ∀ᵐ r ∂μ, |f r| ≤ B * C := by
    filter_upwards [hD, hKpos, hrow, heq] with r hrD hrK hrrow hreq
    have hbound : ∀ᵐ s ∂μ, ‖K r s * f s‖ ≤ K r s * C := by
      filter_upwards [hrK, hfC] with s hsK hsC
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsK]
      exact mul_le_mul_of_nonneg_left hsC hsK
    have hi : Integrable (fun s => K r s * f s) μ :=
      ((hK r).mul_const C).mono' ((hK r).aestronglyMeasurable.mul hf) hbound
    have hh : |f r| * D r ≤ B * D r * C := by
      calc
        |f r| * D r = |f r * D r| := by rw [abs_mul, abs_of_pos hrD]
        _ = |∫ s, K r s * f s ∂μ| := by rw [hreq]
        _ ≤ ∫ s, ‖K r s * f s‖ ∂μ := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (fun s => K r s * f s) (μ := μ))
        _ ≤ ∫ s, K r s * C ∂μ :=
          integral_mono_ae hi.norm ((hK r).mul_const C) hbound
        _ = (∫ s, K r s ∂μ) * C := integral_mul_const C (K r)
        _ ≤ B * D r * C := mul_le_mul_of_nonneg_right hrrow hC
    nlinarith
  have hCC : C ≤ B * C := essSup_le_of_ae_le (B * C) hsmall hcob
  have hC0 : C = 0 := by nlinarith
  filter_upwards [hfC] with r hr
  exact abs_eq_zero.mp (le_antisymm (by simpa only [hC0] using hr) (abs_nonneg _))

def sphereKernel (r s : Time) : ℝ := min (r : ℝ) (s : ℝ) - (r : ℝ) * (s : ℝ)

def sphereTail (μ : Measure Time) (r : Time) : ℝ :=
  ∫ s, 1 - max (r : ℝ) (s : ℝ) ∂μ

lemma sphereKernel_nonneg (r s : Time) : 0 ≤ sphereKernel r s := by
  unfold sphereKernel
  rcases le_total (r : ℝ) (s : ℝ) with h | h
  · rw [min_eq_left h]
    nlinarith [r.property.1, s.property.2]
  · rw [min_eq_right h]
    nlinarith [s.property.1, r.property.2]

lemma sphereKernel_le_weight (r s : Time) :
    sphereKernel r s ≤ (r : ℝ) * (1 - max (r : ℝ) (s : ℝ)) := by
  unfold sphereKernel
  rcases le_total (r : ℝ) (s : ℝ) with h | h
  · rw [min_eq_left h, max_eq_right h]
    ring_nf
    exact le_rfl
  · rw [min_eq_right h, max_eq_left h]
    nlinarith [r.property.2]

lemma sphereTail_integrable (μ : Measure Time) [IsFiniteMeasure μ] (r : Time) :
    Integrable (fun s : Time => 1 - max (r : ℝ) (s : ℝ)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    have := r.property.2
    have := s.property.2
    simp only [sub_nonneg, max_le_iff]
    exact ⟨‹_›, ‹_›⟩)]
  have h := r.property.1
  have hh : (r : ℝ) ≤ max (r : ℝ) (s : ℝ) := le_max_left _ _
  linarith

lemma sphereKernel_integrable (μ : Measure Time) [IsFiniteMeasure μ] (r : Time) :
    Integrable (sphereKernel r) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereKernel; fun_prop)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereKernel_nonneg r s)]
  have h := sphereKernel_le_weight r s
  have hmax : 0 ≤ max (r : ℝ) (s : ℝ) := r.property.1.trans (le_max_left _ _)
  nlinarith [r.property.1, r.property.2]

lemma sphereTail_lower (μ : Measure Time) [IsProbabilityMeasure μ] {B : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) {r : Time} (hr : (r : ℝ) ≤ B) :
    1 - B ≤ sphereTail μ r := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (sphereTail_integrable μ r) (by
      filter_upwards [hμ] with s hs
      exact sub_le_sub_left (max_le hr hs) 1)

lemma sphereKernel_row_bound (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} {r : Time} (hr : (r : ℝ) ≤ B) :
    (∫ s, sphereKernel r s ∂μ) ≤ B * sphereTail μ r := by
  have htail : 0 ≤ sphereTail μ r := integral_nonneg (fun s =>
    sub_nonneg.mpr (max_le r.property.2 s.property.2))
  calc
    _ ≤ ∫ s, (r : ℝ) * (1 - max (r : ℝ) (s : ℝ)) ∂μ :=
      integral_mono (sphereKernel_integrable μ r) ((sphereTail_integrable μ r).const_mul _)
        (sphereKernel_le_weight r)
    _ = (r : ℝ) * sphereTail μ r := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hr htail

theorem sphere_equation_unique (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B)
    {a b : Time → ℝ} (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (haBound : ∃ C : ℝ, ∀ᵐ r ∂μ, |a r| ≤ C)
    (hbBound : ∃ C : ℝ, ∀ᵐ r ∂μ, |b r| ≤ C)
    (haEq : ∀ᵐ r ∂μ, a r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * a s ∂μ)
    (hbEq : ∀ᵐ r ∂μ, b r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * b s ∂μ) :
    a =ᵐ[μ] b := by
  obtain ⟨A, hA⟩ := haBound
  obtain ⟨B', hB'⟩ := hbBound
  have hzero : (fun r => a r - b r) =ᵐ[μ] 0 :=
    weighted_kernel_homogeneous_eq_zero μ (D := sphereTail μ) (K := sphereKernel) hB
      (by filter_upwards [hμ] with r hr; have := sphereTail_lower μ hμ hr; linarith)
      (sphereKernel_integrable μ)
      (Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall (sphereKernel_nonneg r))
      (by filter_upwards [hμ] with r hr; exact sphereKernel_row_bound μ hr)
      (ha.sub hb)
      ⟨A + B', by
        filter_upwards [hA, hB'] with r hAr hBr
        exact (abs_sub (a r) (b r)).trans (add_le_add hAr hBr)⟩
      (by
        filter_upwards [haEq, hbEq] with r har hbr
        have hai : Integrable (fun s => sphereKernel r s * a s) μ := by
          apply ((sphereKernel_integrable μ r).mul_const A).mono'
            ((sphereKernel_integrable μ r).aestronglyMeasurable.mul ha)
          filter_upwards [hA] with s hs
          change |sphereKernel r s * _| ≤ _
          rw [abs_mul, abs_of_nonneg (sphereKernel_nonneg r s)]
          exact mul_le_mul_of_nonneg_left hs (sphereKernel_nonneg r s)
        have hbi : Integrable (fun s => sphereKernel r s * b s) μ := by
          apply ((sphereKernel_integrable μ r).mul_const B').mono'
            ((sphereKernel_integrable μ r).aestronglyMeasurable.mul hb)
          filter_upwards [hB'] with s hs
          change |sphereKernel r s * _| ≤ _
          rw [abs_mul, abs_of_nonneg (sphereKernel_nonneg r s)]
          exact mul_le_mul_of_nonneg_left hs (sphereKernel_nonneg r s)
        simp_rw [mul_sub]
        rw [integral_sub hai hbi, sub_mul, har, hbr]
        ring)
  filter_upwards [hzero] with r hr
  exact sub_eq_zero.mp hr

lemma sphereTail_nonneg (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    0 ≤ sphereTail μ r := integral_nonneg (fun s =>
      sub_nonneg.mpr (max_le r.property.2 s.property.2))

lemma sphereTail_upper (μ : Measure Time) [IsProbabilityMeasure μ] (r : Time) :
    sphereTail μ r ≤ 1 - (r : ℝ) := by
  calc
    _ ≤ ∫ _ : Time, 1 - (r : ℝ) ∂μ :=
      integral_mono (sphereTail_integrable μ r) (integrable_const _)
        (fun s => sub_le_sub_left (le_max_left _ _) 1)
    _ = _ := by simp

theorem sphere_equation_support_bound (μ : Measure Time) [IsProbabilityMeasure μ]
    {a : Time → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (haNonneg : ∀ᵐ r ∂μ, 0 ≤ a r) (haBound : ∀ᵐ r ∂μ, a r ≤ A)
    (haEq : ∀ᵐ r ∂μ, a r * sphereTail μ r = (r : ℝ) + ∫ s, sphereKernel r s * a s ∂μ) :
    ∀ᵐ r : Time ∂μ, (r : ℝ) ≤ A / (1 + A) := by
  filter_upwards [haBound, haEq] with r har heq
  have hint : 0 ≤ ∫ s, sphereKernel r s * a s ∂μ :=
    integral_nonneg_of_ae (by
      filter_upwards [haNonneg] with s hs
      exact mul_nonneg (sphereKernel_nonneg r s) hs)
  have hineq : (r : ℝ) ≤ A * (1 - (r : ℝ)) := by
    calc
      _ ≤ a r * sphereTail μ r := by linarith
      _ ≤ A * sphereTail μ r := mul_le_mul_of_nonneg_right har (sphereTail_nonneg μ r)
      _ ≤ _ := mul_le_mul_of_nonneg_left (sphereTail_upper μ r) hA
  apply (le_div_iff₀ (by linarith : 0 < 1 + A)).mpr
  nlinarith

def realTail (μ : Measure Time) (x : ℝ) : ℝ :=
  ∫ s, 1 - max x (s : ℝ) ∂μ

def realCDF (μ : Measure Time) (x : ℝ) : ℝ := μ.real {s : Time | (s : ℝ) ≤ x}

lemma continuous_time_integrable (μ : Measure Time) [IsFiniteMeasure μ]
    {f : Time → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma realTail_integrable (μ : Measure Time) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun s : Time => 1 - max x (s : ℝ)) μ :=
  continuous_time_integrable μ (by fun_prop)

lemma hasDerivWithinAt_max_right (x s : ℝ) :
    HasDerivWithinAt (fun y => max y s) (if s ≤ x then 1 else 0) (Ioi x) x := by
  split_ifs with h
  · exact (hasDerivAt_id x).hasDerivWithinAt.congr
      (fun y hy => max_eq_left (h.trans (le_of_lt hy))) (max_eq_left h)
  · have hd : HasDerivAt (fun y => max y s) 0 x := by
      apply (hasDerivAt_const x s).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds (lt_of_not_ge h)] with y hy
      exact max_eq_right (le_of_lt hy)
    exact hd.hasDerivWithinAt

lemma realTail_right_derivative (μ : Measure Time) [IsFiniteMeasure μ] (x : ℝ) :
    HasDerivWithinAt (realTail μ) (-realCDF μ x) (Ioi x) x := by
  have hlim (s : Time) :
      Tendsto (slope (fun y => 1 - max y (s : ℝ)) x) (𝓝[Ioi x] x)
        (𝓝 (-(if (s : ℝ) ≤ x then 1 else 0))) := by
    have hd := (hasDerivAt_const x (1 : ℝ)).hasDerivWithinAt.sub
      (hasDerivWithinAt_max_right x (s : ℝ))
    change HasDerivWithinAt (fun y => 1 - max y (s : ℝ))
      (0 - (if (s : ℝ) ≤ x then 1 else 0)) (Ioi x) x at hd
    have hh := hasDerivWithinAt_iff_tendsto_slope.mp hd
    simpa using hh
  have hint : (∫ s : Time, -(if (s : ℝ) ≤ x then 1 else 0) ∂μ) = -realCDF μ x := by
    rw [integral_neg]
    congr 1
    change (∫ s : Time, {s : Time | (s : ℝ) ≤ x}.indicator (fun _ => (1 : ℝ)) s ∂μ) = _
    rw [integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    simp [realCDF]
  apply hasDerivWithinAt_iff_tendsto_slope.mpr
  have hd := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun y (s : Time) => slope (fun z => 1 - max z (s : ℝ)) x y)
    (fun _ => (1 : ℝ))
    (Eventually.of_forall fun y => by unfold slope; fun_prop)
    (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      filter_upwards [] with s
      rw [slope_def_field, Real.norm_eq_abs, abs_div]
      have h := abs_max_sub_max_le_max y (s : ℝ) x (s : ℝ)
      simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (y - x))] at h
      have he : |(1 - max y (s : ℝ)) - (1 - max x (s : ℝ))| =
          |max y (s : ℝ) - max x (s : ℝ)| := by
        rw [show (1 - max y (s : ℝ)) - (1 - max x (s : ℝ)) =
          -(max y (s : ℝ) - max x (s : ℝ)) by ring, abs_neg]
      rw [he]
      exact (div_le_one (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hy)))).mpr h)
    (integrable_const _) (Eventually.of_forall hlim)
  rw [hint] at hd
  convert hd using 1
  · ext y
    rw [slope_def_field, realTail, realTail, ← integral_sub (realTail_integrable μ y)
    (realTail_integrable μ x), ← integral_div]
    simp only [slope_def_field]
  · simp

lemma abs_realTail_sub_le (μ : Measure Time) [IsProbabilityMeasure μ] (x y : ℝ) :
    |realTail μ x - realTail μ y| ≤ |x - y| := by
  rw [realTail, realTail, ← integral_sub (realTail_integrable μ x) (realTail_integrable μ y)]
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun s : Time => (1 - max x (s : ℝ)) - (1 - max y (s : ℝ)))
    (C := |x - y|) (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, show (1 - max x (s : ℝ)) - (1 - max y (s : ℝ)) =
        -(max x (s : ℝ) - max y (s : ℝ)) by ring, abs_neg]
      simpa using abs_max_sub_max_le_max x (s : ℝ) y (s : ℝ))
  simpa using hh

lemma realTail_continuous (μ : Measure Time) [IsProbabilityMeasure μ] :
    Continuous (realTail μ) := by
  have h : LipschitzWith 1 (realTail μ) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [Real.dist_eq] using abs_realTail_sub_le μ x y
  exact h.continuous

lemma realCDF_monotone (μ : Measure Time) [IsFiniteMeasure μ] :
    Monotone (realCDF μ) := by
  intro x y hxy
  exact measureReal_mono (fun _ hs => hs.trans hxy)

lemma realCDF_integrable (μ : Measure Time) [IsFiniteMeasure μ] (a b : ℝ) :
    IntervalIntegrable (realCDF μ) volume a b :=
  (realCDF_monotone μ).intervalIntegrable

lemma integral_cdf_mul (μ : Measure Time) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 ≤ r)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 r) :
    (∫ t in 0..r, realCDF μ t * f t) =
      ∫ s : Time, if (s : ℝ) ≤ r then ∫ t in (s : ℝ)..r, f t else 0 ∂μ := by
  let ν : Measure ℝ := volume.restrict (Icc 0 r)
  have hfi : Integrable f ν := (intervalIntegrable_iff_integrableOn_Icc_of_le hr).mp hf
  have hmeas : MeasurableSet {p : ℝ × Time | (p.2 : ℝ) ≤ p.1} :=
    measurableSet_le (by fun_prop) measurable_fst
  have hbase : Integrable (fun p : ℝ × Time => f p.1) (ν.prod μ) := by
    simpa using hfi.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have hswap := integral_integral_swap (μ := ν) (ν := μ)
    (f := fun t s => {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator (fun p => f p.1) (t, s))
    (hbase.indicator hmeas)
  have hleft (t : ℝ) :
      (∫ s : Time, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => f p.1) (t, s) ∂μ) = realCDF μ t * f t := by
    change (∫ s : Time, {s : Time | (s : ℝ) ≤ t}.indicator (fun _ => f t) s ∂μ) = _
    rw [integral_indicator (measurableSet_le (by fun_prop) measurable_const)]
    simp [realCDF]
  have hright (s : Time) :
      (∫ t, {p : ℝ × Time | (p.2 : ℝ) ≤ p.1}.indicator
        (fun p => f p.1) (t, s) ∂ν) =
        if (s : ℝ) ≤ r then ∫ t in (s : ℝ)..r, f t else 0 := by
    change (∫ t, (Ici (s : ℝ)).indicator f t ∂ν) = _
    rw [integral_indicator measurableSet_Ici]
    have hset : Icc 0 r ∩ Ici (s : ℝ) = Icc (s : ℝ) r := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · intro h; exact ⟨h.2, h.1.2⟩
      · intro h; exact ⟨⟨s.property.1.trans h.1, h.2⟩, h.1⟩
    dsimp only [ν]
    rw [Measure.restrict_restrict measurableSet_Ici, inter_comm, hset]
    split_ifs with hs
    · rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hs]
    · simp [Icc_eq_empty_of_lt (lt_of_not_ge hs)]
  have hl : (∫ (t : ℝ), realCDF μ t * f t ∂ν) = ∫ t in 0..r, realCDF μ t * f t := by
    dsimp only [ν]
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hr]
  simpa only [Function.uncurry_apply_pair, hleft, hright, hl] using hswap

lemma realTail_lower (μ : Measure Time) [IsProbabilityMeasure μ] {B x : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hx : x ≤ B) :
    1 - B ≤ realTail μ x := by
  calc
    _ = ∫ _ : Time, 1 - B ∂μ := by simp
    _ ≤ _ := integral_mono_ae (integrable_const _) (realTail_integrable μ x) (by
      filter_upwards [hμ] with s hs
      exact sub_le_sub_left (max_le hx hs) 1)

def cappedDensity (μ : Measure Time) (B x : ℝ) : ℝ :=
  (max (1 - B) (realTail μ x))⁻¹ ^ 2

def cappedA (μ : Measure Time) (B r : ℝ) : ℝ :=
  ∫ t in 0..r, cappedDensity μ B t

lemma cappedDensity_continuous (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) : Continuous (cappedDensity μ B) := by
  unfold cappedDensity
  apply Continuous.pow
  exact (continuous_const.max (realTail_continuous μ)).inv₀ (fun x =>
    ne_of_gt (lt_of_lt_of_le (sub_pos.mpr hB) (le_max_left _ _)))

lemma cappedA_hasDerivAt (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) (r : ℝ) :
    HasDerivAt (cappedA μ B) (cappedDensity μ B r) r := by
  have hc := cappedDensity_continuous μ hB
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma cappedA_continuous (μ : Measure Time) [IsProbabilityMeasure μ]
    {B : ℝ} (hB : B < 1) : Continuous (cappedA μ B) :=
  continuous_iff_continuousAt.mpr (fun r => (cappedA_hasDerivAt μ hB r).continuousAt)

lemma cappedDensity_eq (μ : Measure Time) [IsProbabilityMeasure μ] {B x : ℝ}
    (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hx : x ≤ B) :
    cappedDensity μ B x = (realTail μ x)⁻¹ ^ 2 := by
  rw [cappedDensity, max_eq_right (realTail_lower μ hμ hx)]

lemma realTail_inv_integral (μ : Measure Time) [IsProbabilityMeasure μ] {B r : ℝ}
    (hB : B < 1) (hμ : ∀ᵐ s : Time ∂μ, (s : ℝ) ≤ B) (hr : 0 ≤ r) (hrB : r ≤ B) :
    (realTail μ r)⁻¹ - (realTail μ 0)⁻¹ =
      ∫ t in 0..r, realCDF μ t * cappedDensity μ B t := by
  have hn (x : ℝ) (hx : x ≤ B) : realTail μ x ≠ 0 :=
    ne_of_gt ((sub_pos.mpr hB).trans_le (realTail_lower μ hμ hx))
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (f := fun x : ℝ => (realTail μ x)⁻¹) hr
  · exact (realTail_continuous μ).continuousOn.inv₀ (fun x hx => hn x (hx.2.trans hrB))
  · intro x hx
    have hd := (realTail_right_derivative μ x).inv (hn x (hx.2.le.trans hrB))
    convert! hd using 1
    simp only [cappedDensity_eq μ hμ (hx.2.le.trans hrB), neg_neg, div_eq_mul_inv, inv_pow]
  · exact (realCDF_integrable μ 0 r).mul_continuousOn
      (cappedDensity_continuous μ hB).continuousOn

end SphericalPerceptronFreeEnergy
end

end OAI
