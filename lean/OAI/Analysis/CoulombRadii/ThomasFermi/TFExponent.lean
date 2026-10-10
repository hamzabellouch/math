import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.Gaussian

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
noncomputable abbrev TFExponent : ℝ≥0∞ := ENNReal.ofReal (5/3:ℝ)
instance : Fact (1 ≤ TFExponent) := ⟨by norm_num [TFExponent]⟩
noncomputable abbrev TFLp {α : Type*} [MeasurableSpace α] (μ : Measure α) := Lp ℝ TFExponent μ
lemma tfLp_norm {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : TFLp μ) :
    ‖f‖ = (∫ x, ‖f x‖^(5/3:ℝ) ∂μ)^(3/5:ℝ) := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num [TFExponent]) (by simp)
      (Lp.memLp f).aestronglyMeasurable]
  norm_num [TFExponent]
lemma tfLp_norm_power {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : TFLp μ) :
    ‖f‖^(5/3:ℝ) = ∫ x, ‖f x‖^(5/3:ℝ) ∂μ := by
  rw [tfLp_norm, ← Real.rpow_mul (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
  norm_num
lemma tfLp_integral_norm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (f : TFLp μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ (μ.real univ)^(2/5:ℝ)*‖f‖ := by
  have H := integral_mul_norm_le_Lp_mul_Lq coulomb_holder_exponents
    (memLp_const (p := ENNReal.ofReal (5/2:ℝ)) (1:ℝ)) (Lp.memLp f)
  simp only [norm_one, one_mul, Real.one_rpow, integral_const, smul_eq_mul] at H
  rw [tfLp_norm]
  convert H using 1; norm_num

noncomputable def tfExtend (Ω : Set Space) (f : TFLp (volume.restrict Ω)) : Space → ℝ :=
  Ω.indicator f
lemma tfExtend_measurable {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    Measurable (tfExtend Ω f) := (Lp.stronglyMeasurable f).measurable.indicator hΩ
lemma tfExtend_memLp {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    MemLp (tfExtend Ω f) TFExponent volume :=
  (memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp f)
lemma tfExtend_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f : TFLp (volume.restrict Ω)) :
    Integrable (tfExtend Ω f) :=
  (show IntegrableOn (fun x => f x) Ω volume from
    (Lp.memLp f).integrable (show 1 ≤ TFExponent by norm_num [TFExponent])).integrable_indicator hΩ
lemma tfExtend_norm_integral {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    (∫ x, ‖tfExtend Ω f x‖) = ∫ x in Ω, ‖f x‖ := by
  simp only [tfExtend, norm_indicator_eq_indicator_norm, integral_indicator hΩ]
lemma tfExtend_norm_power_integral {Ω : Set Space} (hΩ : MeasurableSet Ω) (f : TFLp (volume.restrict Ω)) :
    (∫ x, ‖tfExtend Ω f x‖^(5/3:ℝ)) = ‖f‖^(5/3:ℝ) := by
  rw [tfLp_norm_power]
  rw [← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ω <;> simp [tfExtend, hx]

noncomputable def tfCoulomb (Ω : Set Space) (f g : TFLp (volume.restrict Ω)) : ℝ :=
  ∫ p : Space × Space, tfExtend Ω f p.1 * tfExtend Ω g p.2 * coulombKernel (p.1-p.2)
lemma tfCoulomb_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f g : TFLp (volume.restrict Ω)) :
    Integrable (fun p : Space × Space => tfExtend Ω f p.1 * tfExtend Ω g p.2 * coulombKernel (p.1-p.2)) :=
  coulomb_lp_pair_integrable (tfExtend_integrable hΩ f) (tfExtend_measurable hΩ f)
    (tfExtend_integrable hΩ g) (tfExtend_measurable hΩ g) (tfExtend_memLp hΩ g)
lemma tfCoulomb_self_nonneg {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f : TFLp (volume.restrict Ω)) :
    0 ≤ tfCoulomb Ω f f :=
  coulomb_lp_form_nonneg (tfExtend_integrable hΩ f) (tfExtend_measurable hΩ f) (tfExtend_memLp hΩ f)
lemma tfExtend_convolution_bound {Ω : Set Space} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (f : TFLp (volume.restrict Ω)) (x : Space) :
    (∫ y, coulombKernel (x-y)*‖tfExtend Ω f y‖) ≤
      ((8*Real.pi)^(2/5:ℝ) + (volume.real Ω)^(2/5:ℝ))*‖f‖ := by
  have H := coulomb_lp_convolution_bound (tfExtend_integrable hΩ f) (tfExtend_measurable hΩ f)
    (tfExtend_memLp hΩ f) (by norm_num : (0:ℝ)<1) x
  rw [tfExtend_norm_power_integral hΩ, ← Real.rpow_mul (norm_nonneg f)] at H
  norm_num only [Real.one_rpow, mul_one, inv_one, one_mul, show (5/3:ℝ)*(3/5)=1 by norm_num,
    Real.rpow_one] at H
  rw [tfExtend_norm_integral hΩ] at H
  have H1 := tfLp_integral_norm_le f
  simp only [Measure.real, Measure.restrict_apply_univ] at H1
  dsimp only [Measure.real]
  nlinarith
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tf_power_strong_convex {R : ℝ} (_hR : 0 < R) :
    StrongConvexOn (Icc 0 R) ((10/9:ℝ)*R^(-(1/3:ℝ))) (fun x : ℝ => x^(5/3:ℝ)) := by
  rw [strongConvexOn_iff_convex]
  have he : (fun x : ℝ => x^(5/3:ℝ) - ((10/9:ℝ)*R^(-(1/3:ℝ)))/2*‖x‖^2) =
      (fun x : ℝ => x^(5/3:ℝ) - (5/9:ℝ)*R^(-(1/3:ℝ))*x^2) := by
    ext x
    rw [Real.norm_eq_abs, sq_abs]
    ring
  rw [he]
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 R)
    (f' := fun x => (5/3:ℝ)*x^(2/3:ℝ) - (10/9:ℝ)*R^(-(1/3:ℝ))*x)
    (f'' := fun x => (10/9:ℝ)*(x^(-(1/3:ℝ))-R^(-(1/3:ℝ))))
  · exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤5/3)).sub
      (continuous_const.mul (continuous_pow 2))).continuousOn
  · intro x hx
    have hd := (Real.hasDerivAt_rpow_const (x := x) (p := 5/3) (Or.inr (by norm_num))).sub
      (((hasDerivAt_pow 2 x).const_mul ((5/9:ℝ)*R^(-(1/3:ℝ)))))
    convert! hd.hasDerivWithinAt (s := interior (Icc (0:ℝ) R)) using 1; norm_num
    all_goals first | rfl | ring
  · intro x hx
    rw [interior_Icc] at hx
    have hd := ((Real.hasDerivAt_rpow_const (x := x) (p := 2/3) (Or.inl hx.1.ne')).const_mul (5/3:ℝ)).sub
      ((hasDerivAt_id x).const_mul ((10/9:ℝ)*R^(-(1/3:ℝ))))
    convert! hd.hasDerivWithinAt (s := interior (Icc (0:ℝ) R)) using 1; norm_num
    all_goals first | rfl | ring
  · intro x hx
    rw [interior_Icc] at hx
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hx.1 hx.2.le (by norm_num)))

lemma tf_power_midpoint_gap {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (5/36:ℝ)*(a+b+1)^(-(1/3:ℝ))*(a-b)^2 ≤
      (a^(5/3:ℝ)+b^(5/3:ℝ))/2 - ((a+b)/2)^(5/3:ℝ) := by
  have H := (tf_power_strong_convex (show 0 < a+b+1 by linarith)).2
    (show a ∈ Icc 0 (a+b+1) from ⟨ha,by linarith⟩)
    (show b ∈ Icc 0 (a+b+1) from ⟨hb,by linarith⟩)
    (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at H
  have he : (1/2:ℝ)*a+(1/2:ℝ)*b=(a+b)/2 := by ring
  rw [he] at H
  nlinarith
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma tf_power_difference_factor {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖a-b‖^(5/3:ℝ) =
      ((a+b+1)^(-(1/3:ℝ))*(a-b)^2)^(5/6:ℝ) *
        ((a+b+1)^(5/3:ℝ))^(1/6:ℝ) := by
  have hR : 0 < a+b+1 := by linarith
  rw [Real.mul_rpow (Real.rpow_nonneg hR.le _) (sq_nonneg _),
    ← Real.rpow_mul hR.le, ← Real.rpow_mul hR.le]
  have hs : ((a-b)^2)^(5/6:ℝ) = ‖a-b‖^(5/3:ℝ) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  rw [hs, mul_right_comm, ← Real.rpow_add hR]
  norm_num

lemma tf_midpoint_gap_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (a^(5/3:ℝ)+b^(5/3:ℝ))/2 - ((a+b)/2)^(5/3:ℝ) :=
  (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _))
    (sq_nonneg _)).trans (tf_power_midpoint_gap ha hb)

lemma integrable_rpow_of_memLp_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x) : Integrable (fun x => f x ^ p) μ := by
  have H := hf.integrable_norm_rpow (by simpa using hp) (by simp)
  apply H.congr
  filter_upwards [hn] with x hx
  simp [Real.norm_of_nonneg hx, ENNReal.toReal_ofReal hp.le]

lemma memLp_rpow_of_integrable_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x)
    {q : ℝ} (hq : 0 < q) : MemLp (fun x => f x ^ q) (ENNReal.ofReal (1/q)) μ := by
  have H := (memLp_one_iff_integrable.mpr hf).norm_rpow_div (ENNReal.ofReal q)
  have he : (1:ℝ≥0∞) / ENNReal.ofReal q = ENNReal.ofReal (1/q) := by
    rw [ENNReal.ofReal_div_of_pos hq, ENNReal.ofReal_one]
  rw [he] at H
  apply H.ae_eq
  filter_upwards [hn] with x hx
  simp [Real.norm_of_nonneg hx, ENNReal.toReal_ofReal hq.le]

lemma tf_integrated_midpoint_gap {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f g : α → ℝ}
    (hf : MemLp f (ENNReal.ofReal (5/3:ℝ)) μ) (hg : MemLp g (ENNReal.ofReal (5/3:ℝ)) μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, ‖f x-g x‖^(5/3:ℝ) ∂μ) ≤
      ((36/5:ℝ)*((∫ x, f x^(5/3:ℝ) ∂μ)+(∫ x, g x^(5/3:ℝ) ∂μ))/2 -
        (36/5:ℝ)*(∫ x, ((f x+g x)/2)^(5/3:ℝ) ∂μ))^(5/6:ℝ) *
      (∫ x, (f x+g x+1)^(5/3:ℝ) ∂μ)^(1/6:ℝ) := by
  let d := fun x => (f x^(5/3:ℝ)+g x^(5/3:ℝ))/2 - ((f x+g x)/2)^(5/3:ℝ)
  let u := fun x => (f x+g x+1)^(-(1/3:ℝ))*(f x-g x)^2
  let v := fun x => (f x+g x+1)^(5/3:ℝ)
  have hfi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hf hf0
  have hgi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hg hg0
  have hm : MemLp (fun x => (f x+g x)/2) (ENNReal.ofReal (5/3:ℝ)) μ := by
    simpa only [div_eq_mul_inv, Pi.add_apply] using (hf.add hg).mul_const (2:ℝ)⁻¹
  have hmi := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hm
    (by filter_upwards [hf0,hg0] with x hx hy; positivity)
  have hdi : Integrable d μ := ((hfi.add hgi).div_const 2).sub hmi
  have hd0 : ∀ᵐ x ∂μ, 0 ≤ d x := by
    filter_upwards [hf0,hg0] with x hx hy
    exact tf_midpoint_gap_nonneg hx hy
  have hu0 : ∀ᵐ x ∂μ, 0 ≤ u x := by
    filter_upwards [hf0,hg0] with x hx hy
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (sq_nonneg _)
  have hule : ∀ᵐ x ∂μ, u x ≤ (36/5:ℝ)*d x := by
    filter_upwards [hf0,hg0] with x hx hy
    have H := tf_power_midpoint_gap hx hy
    dsimp [u,d]
    nlinarith
  have hum : AEStronglyMeasurable u μ := by
    exact (((hf.aestronglyMeasurable.add hg.aestronglyMeasurable).add
      aestronglyMeasurable_const).aemeasurable.pow_const _).aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.sub hg.aestronglyMeasurable).pow 2)
  have hui : Integrable u μ := (hdi.const_mul (36/5:ℝ)).mono' hum (by
    filter_upwards [hule, hu0] with x hx hn
    simpa only [Real.norm_of_nonneg hn] using hx)
  have hvp := (hf.add hg).add (memLp_const (1:ℝ))
  have hv0 : ∀ᵐ x ∂μ, 0 ≤ v x := by
    filter_upwards [hf0,hg0] with x hx hy
    exact Real.rpow_nonneg (by linarith) _
  have hvi : Integrable v μ := integrable_rpow_of_memLp_nonneg (by norm_num : (0:ℝ)<5/3) hvp
    (by filter_upwards [hf0,hg0] with x hx hy; positivity)
  have hup := memLp_rpow_of_integrable_nonneg hui hu0 (by norm_num : (0:ℝ)<5/6)
  have hvp' := memLp_rpow_of_integrable_nonneg hvi hv0 (by norm_num : (0:ℝ)<1/6)
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (6/5:ℝ).HolderConjugate 6 by constructor <;> norm_num)
    (show ∀ᵐ x ∂μ, 0 ≤ u x^(5/6:ℝ) by filter_upwards [hu0] with x hx; positivity)
    (show ∀ᵐ x ∂μ, 0 ≤ v x^(1/6:ℝ) by filter_upwards [hv0] with x hx; positivity)
    (by convert hup using 1; norm_num) (by convert hvp' using 1; norm_num)
  have hlu : (∫ x, (u x^(5/6:ℝ))^(6/5:ℝ) ∂μ) = ∫ x, u x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hu0] with x hx
    rw [← Real.rpow_mul hx]
    norm_num
  have hlv : (∫ x, (v x^(1/6:ℝ))^(6:ℝ) ∂μ) = ∫ x, v x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv0] with x hx
    rw [← Real.rpow_mul hx]
    norm_num
  rw [hlu, hlv] at H
  have hleft : (∫ x, ‖f x-g x‖^(5/3:ℝ) ∂μ) = ∫ x, u x^(5/6:ℝ)*v x^(1/6:ℝ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf0,hg0] with x hx hy
    exact tf_power_difference_factor hx hy
  rw [hleft]
  have huint : (∫ x, u x ∂μ) ≤ (36/5:ℝ)*(∫ x, d x ∂μ) := by
    rw [← integral_const_mul]
    exact integral_mono_ae hui (hdi.const_mul _) hule
  have hdint : (36/5:ℝ)*(∫ x, d x ∂μ) =
      (36/5:ℝ)*((∫ x, f x^(5/3:ℝ) ∂μ)+(∫ x, g x^(5/3:ℝ) ∂μ))/2 -
        (36/5:ℝ)*(∫ x, ((f x+g x)/2)^(5/3:ℝ) ∂μ) := by
    dsimp [d]
    rw [integral_sub (by exact (hfi.add hgi).div_const 2) hmi, integral_div]
    rw [integral_add hfi hgi]
    ring
  rw [← hdint]
  norm_num only [show (1:ℝ)/(6/5)=5/6 by norm_num] at H
  exact H.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (integral_nonneg_of_ae hu0) huint (by norm_num : (0:ℝ)≤5/6))
    (Real.rpow_nonneg (integral_nonneg_of_ae hv0) _))
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
