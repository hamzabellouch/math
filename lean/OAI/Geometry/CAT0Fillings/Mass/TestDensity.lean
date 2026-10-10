import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Gradient.HilbertAtlas

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma integrable_gradient_weight (i : ℕ) {u w : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hw : Continuous w) :
    Integrable (fun z => (q.density i z * q.duNorm i u z)*w ((q.chart i).paramExtended z))
      (volume.restrict (q.chart i).domain) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn hw.continuousOn
  exact (q.integrable_gradient i hu).mul_bdd
    (hw.measurable.comp (q.chart i).measurable_paramExtended).aestronglyMeasurable
    (Eventually.of_forall fun z => hB _ (mem_univ _))

lemma chart_action_le_gradient (i : ℕ) {u b : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, LipschitzWith 1 (π j)) :
    |(q.chart i).action b (Fin.cons u π)| ≤ ∫ z,
      (q.density i z * q.duNorm i u z)*|b ((q.chart i).paramExtended z)|
      ∂volume.restrict (q.chart i).domain := by
  have hc : ∀ j : Fin (k+1), ∃ L : ℝ≥0, LipschitzWith L ((Fin.cons u π : Fin (k+1) → X → ℝ) j) :=
    by
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨K,hu⟩
      · exact ⟨1,hπ j⟩
  rw [IntegerChart.action,ite_eq_left ⟨hb,hc⟩]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono_ae ((q.chart i).integrable_action_integrand hb hc).abs
    (q.integrable_gradient_weight i hu hb.continuous.abs)
  filter_upwards [q.ae_jacobian_le_duNorm i hu π hπ,ae_restrict_mem (q.chart i).borel]
    with z hz hzi
  simp only [abs_mul,(q.chart i).scalar_eq hzi,IntegerChart.paramExtended,dite_eq_left hzi]
  calc
    _ ≤ |((q.chart i).multiplicity z : ℝ)| * |b ((q.chart i).param ⟨z,hzi⟩)| *
        (q.duNorm i u z * Real.sqrt (q.gram i z).det) := by gcongr
    _ = _ := by simp only [density]; ring

lemma action_le_gradient {u b : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, LipschitzWith 1 (π j)) :
    |T b (Fin.cons u π)| ≤ ∫ x, |b x| ∂q.gradientMeasure u := by
  have hs := q.gradient_summable hu hb.continuous.abs
  have hbnd := fun i => q.chart_action_le_gradient i hu hb π hπ
  have hsa : Summable (fun i => (q.chart i).action b (Fin.cons u π)) :=
    hs.of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using hbnd i)
  rw [q.action,q.integral_gradientMeasure hu hb.continuous.abs]
  calc
    |∑' i, (q.chart i).action b (Fin.cons u π)| ≤
        ∑' i, |(q.chart i).action b (Fin.cons u π)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsa.norm
    _ ≤ _ := hsa.abs.tsum_le_tsum hbnd hs

theorem list_action_le_gradient {N : ℕ} {u w : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) (hw : BoundedLip w)
    (b : Fin N → X → ℝ) (hb : ∀ i, BoundedLip (b i))
    (hbudget : ∀ x, ∑ i, |b i x| ≤ 1)
    (π : Fin N → Fin k → X → ℝ) (hπ : ∀ j i, LipschitzWith 1 (π j i)) :
    |∑ i, T (fun x => w x*b i x) (Fin.cons u (π i))| ≤
      ∫ x, |w x| ∂q.gradientMeasure u := by
  let := q.gradientMeasure_finite hu
  have hi i : Integrable (fun x => |w x*b i x|) (q.gradientMeasure u) :=
    (BorelCoefficients.integrable_boundedLip _ (hw.mul (hb i))).abs
  calc
    _ ≤ ∑ i, |T (fun x => w x*b i x) (Fin.cons u (π i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∫ x, |w x*b i x| ∂q.gradientMeasure u := Finset.sum_le_sum fun i _ =>
      q.action_le_gradient hu (hw.mul (hb i)) _ (hπ i)
    _ = ∫ x, ∑ i, |w x*b i x| ∂q.gradientMeasure u :=
      (integral_finsetSum _ fun i _ => hi i).symm
    _ ≤ _ := by
      apply integral_mono (integrable_finsetSum _ fun i _ => hi i)
        (BorelCoefficients.integrable_boundedLip _ hw).abs
      intro x
      simp_rw [abs_mul,←Finset.mul_sum]
      exact mul_le_of_le_one_right (abs_nonneg _) (hbudget x)

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
namespace BorelCoefficients
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma integrable_l2 (f : Lp ℝ 2 μ) : Integrable (fun x => f x) μ :=
  MemLp.integrable (by norm_num) (Lp.memLp f)

lemma integral_abs_le_l2 (f : Lp ℝ 2 μ) :
    (∫ x, |f x| ∂μ) ≤ (μ.real univ)^(1/2:ℝ)*‖f‖ := by
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1:ℝ≥0∞) ≤ 2) (Lp.aestronglyMeasurable f)
  have hfi : Integrable (fun x => f x) μ := integrable_l2 μ f
  have heq : eLpNorm (fun x => f x) 1 μ = ENNReal.ofReal (∫ x, |f x| ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm hfi.aestronglyMeasurable,ofReal_integral_eq_lintegral_ofReal hfi.abs
      (Eventually.of_forall fun _ => abs_nonneg _)]
    congr 1
    ext x
    simp only [Real.enorm_eq_ofReal_abs]
  rw [heq] at hh
  have hhfin : eLpNorm (fun x => f x) 2 μ * μ univ ^ (1 / (1:ℝ) - 1 / (2:ℝ)) ≠ ∞ := by
    apply ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have hh' := ENNReal.toReal_mono (by simpa using hhfin) hh
  simp only [ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _),
    ENNReal.toReal_mul,ENNReal.toReal_one,ENNReal.toReal_ofNat,
    one_div,inv_one] at hh'
  rw [show (1:ℝ)-2⁻¹ = 1/2 by norm_num] at hh'
  simpa only [ENNReal.toReal_rpow,Lp.norm_def,measureReal_def,mul_comm] using hh'

noncomputable def l2ToL1Linear : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 1 μ where
  toFun f := (integrable_l2 μ f).toL1 f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(integrable_l2 μ (f+g)).coeFn_toL1,
      Lp.coeFn_add f g,Lp.coeFn_add ((integrable_l2 μ f).toL1 f)
        ((integrable_l2 μ g).toL1 g),
      (integrable_l2 μ f).coeFn_toL1,
      (integrable_l2 μ g).coeFn_toL1] with x h1 h2 h3 h4 h5
    simp only [h1,h2,h3,Pi.add_apply,h4,h5]
  map_smul' r f := by
    apply Lp.ext
    filter_upwards [(integrable_l2 μ (r • f)).coeFn_toL1,
      Lp.coeFn_smul r f,Lp.coeFn_smul r ((integrable_l2 μ f).toL1 f),
      (integrable_l2 μ f).coeFn_toL1] with x h1 h2 h3 h4
    simp only [h1,h2,h3,Pi.smul_apply,h4,RingHom.id_apply]

noncomputable def l2ToL1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
  (l2ToL1Linear μ).mkContinuous ((μ.real univ)^(1/2:ℝ)) (by
    intro f
    change ‖(integrable_l2 μ f).toL1 f‖ ≤ _
    rw [norm_toL1_integral_abs]
    exact integral_abs_le_l2 μ f)

lemma l2ToL1_coe (f : Lp ℝ 2 μ) : (l2ToL1 μ f : X → ℝ) =ᵐ[μ] f :=
  (integrable_l2 μ f).coeFn_toL1

variable [MetricSpace X] [CompactSpace X] [BorelSpace X]

theorem exists_coefficient_density {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) (hμ : Controls T μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∃ ρ : X → ℝ, AEStronglyMeasurable ρ μ ∧ Integrable ρ μ ∧
      (∀ᵐ x ∂μ, |ρ x| ≤ 1) ∧
      ∀ b : X → ℝ, BoundedLip b → T b π = ∫ x, b x *ρ x ∂μ := by
  let L := (l1Action μ hT π (fun i => ⟨1,hπ i⟩)).comp (l2ToL1 μ)
  let f : Lp ℝ 2 μ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm L
  have hrepr (v : Lp ℝ 2 μ) : L v = ∫ x, f x *v x ∂μ := by
    have hh := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Lp ℝ 2 μ)
      (x := v) (y := L)
    simpa only [f,L2.inner_def,RCLike.inner_apply,conj_trivial,mul_comm] using hh.symm
  have hbound (v : Lp ℝ 2 μ) : |∫ x, f x*v x ∂μ| ≤ ∫ x, |v x| ∂μ := by
    rw [←hrepr]
    have hh := l1Action_bound μ hT hμ π (fun _ => 1) hπ (l2ToL1 μ v)
    simp only [NNReal.coe_one,Finset.prod_const_one,one_mul] at hh
    apply hh.trans_eq
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [l2ToL1_coe μ v] with x hx
    rw [hx,Real.norm_eq_abs]
  have hfi : Integrable (fun x => f x) μ := integrable_l2 μ f
  have hdom : ∀ s : Set X, MeasurableSet s → |∫ x in s, f x ∂μ| ≤ μ.real s := by
    intro s hs
    let v := indicatorConstLp 2 hs (measure_ne_top μ s) (1:ℝ)
    have hh := hbound v
    have hveq : (v : X → ℝ) =ᵐ[μ] s.indicator (fun _ => 1) :=
      indicatorConstLp_coeFn
    have hv1 : (fun x => f x*v x) =ᵐ[μ] s.indicator (fun x => f x) := by
      filter_upwards [hveq] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    have hv2 : (fun x => |v x|) =ᵐ[μ] s.indicator (fun _ => (1:ℝ)) := by
      filter_upwards [hveq] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    rw [integral_congr_ae hv1,integral_congr_ae hv2,integral_indicator hs,
      integral_indicator hs] at hh
    simpa using hh
  have hle : ∀ᵐ x ∂μ, f x ≤ 1 := by
    apply ae_le_of_forall_setIntegral_le hfi (integrable_const (1:ℝ))
    intro s hs hsf
    simpa using (le_abs_self (∫ x in s, f x ∂μ)).trans (hdom s hs)
  have hge : ∀ᵐ x ∂μ, -f x ≤ 1 := by
    apply ae_le_of_forall_setIntegral_le hfi.neg (integrable_const (1:ℝ))
    intro s hs hsf
    simp only [Pi.neg_apply,integral_neg]
    simpa using (neg_le_abs (∫ x in s, f x ∂μ)).trans (hdom s hs)
  refine ⟨f,Lp.aestronglyMeasurable f,hfi,?_,?_⟩
  · filter_upwards [hle,hge] with x hx hy
    exact abs_le.mpr ⟨by linarith,hx⟩
  · intro b hb
    let B : C(X,ℝ) := ⟨b,hb.continuous⟩
    let v := ContinuousMap.toLp 2 μ ℝ B
    have hveq : (v : X → ℝ) =ᵐ[μ] b := ContinuousMap.coeFn_toLp μ B
    have hv : l2ToL1 μ v = (integrable_boundedLip μ hb).toL1 b := by
      apply Lp.ext
      exact ((l2ToL1_coe μ v).trans hveq).trans
        (integrable_boundedLip μ hb).coeFn_toL1.symm
    have hh := hrepr v
    change l1Action μ hT π (fun i => ⟨1,hπ i⟩) (l2ToL1 μ v) = _ at hh
    rw [hv,←borelAction_of_integrable μ hT (integrable_boundedLip μ hb),
      borelAction_eq μ hT hμ ⟨hb,fun i => ⟨1,hπ i⟩⟩] at hh
    rw [hh]
    apply integral_congr_ae
    filter_upwards [hveq] with x hx
    rw [hx,mul_comm]

end BorelCoefficients
end CAT0Fillings
end

end OAI
