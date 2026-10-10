import Mathlib
import OAI.Probability.SKValue.Equations.GradientStrip

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma gaussian_mesh_bound_linear {δ T n K V M J : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hmesh : n*δ=T) :
    2*((δ/2)^2*n*K^2*V)+4*(δ*Real.sqrt δ)^2*n^2*M+4*(δ*K*J)^2 ≤
      δ*(T/2*K^2*V+4*T^2*M+4*K^2*J^2) := by
  have hfirst : 2*((δ/2)^2*n*K^2*V)=δ*(T/2*K^2*V) := by rw [← hmesh]; ring
  have hsecond : 4*(δ*Real.sqrt δ)^2*n^2*M=δ*(4*T^2*M) := by
    rw [mul_pow, Real.sq_sqrt hδ, ← hmesh]
    ring
  have hd2 : δ^2≤δ := by nlinarith
  have hthird := mul_le_mul_of_nonneg_right hd2 (show 0≤4*K^2*J^2 by positivity)
  rw [hfirst, hsecond]
  nlinarith

noncomputable def gradientErrorConstant (T K L : ℝ) (γ : ℝ → ℝ) : ℝ :=
  T/2*K^2*gaussianSquareVariance+4*T^2*cubicEnvelopeMoment (γ T) K ((1/2+γ T)*L)+
    4*K^2*(γ T-γ 0)^2

lemma gradientMeshError_bound_linear {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) {N : ℕ} (hN : 0<N) :
    gradientMeshError T N γ u ≤ stepSize T N*gradientErrorConstant T K L γ := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hδ : 0≤ stepSize T N := div_nonneg hT.le hNr.le
  have hδ1 : stepSize T N≤1 := (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hm : (N:ℝ)*stepSize T N=T := by unfold stepSize; field_simp
  exact (gradientMeshError_bound hT hT1 h hN).trans (gaussian_mesh_bound_linear hδ hδ1 hm)

theorem gradientMeshError_tendsto_zero {T K L : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : GradientStrip T γ u K L) :
    Tendsto (fun N ↦ gradientMeshError T N γ u) atTop (𝓝 0) := by
  have hbound : ∀ᶠ N in atTop,
      gradientMeshError T N γ u≤ stepSize T N*gradientErrorConstant T K L γ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact gradientMeshError_bound_linear hT hT1 h hN
  have hlim : Tendsto (fun N ↦ stepSize T N*gradientErrorConstant T K L γ) atTop (𝓝 0) := by
    simpa only [stepSize, zero_mul] using
      (tendsto_const_div_atTop_nhds_zero_nat T).mul_const (gradientErrorConstant T K L γ)
  exact squeeze_zero' (Eventually.of_forall (fun N ↦ gradientMeshError_nonneg T N γ u)) hbound hlim

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SKValue

lemma continuous_cdf_of_nullSingleton (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hz := (cdf μ).measure_singleton x
  rw [measure_cdf μ, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hz
  have hleft : Function.leftLim (cdf μ) x = cdf μ x := by
    have hl := (monotone_cdf μ).leftLim_le (le_refl x)
    linarith
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, (cdf μ).right_continuous x⟩
  rw [← continuousWithinAt_Iio_iff_Iic]
  exact (monotone_cdf μ).continuousWithinAt_Iio_iff_leftLim_eq.mpr hleft

lemma strictMono_gaussian_cdf {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    StrictMono (cdf (gaussianReal m v)) := by
  intro x y hxy
  apply lt_of_le_of_ne ((monotone_cdf _) hxy.le)
  intro heq
  have hz : gaussianReal m v (Ioc x y) = 0 := by
    rw [← measure_cdf (gaussianReal m v), StieltjesFunction.measure_Ioc, heq, sub_self,
      ENNReal.ofReal_zero]
  have hz' := gaussianReal_absolutelyContinuous' m hv hz
  have hyx : y ≤ x := by simpa [Real.volume_Ioc, ENNReal.ofReal_eq_zero, sub_nonpos] using hz'
  exact (not_le_of_gt hxy) hyx

lemma cdf_mem_Ioo_of_strictMono (μ : Measure ℝ) (hmono : StrictMono (cdf μ)) (x : ℝ) :
    cdf μ x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact lt_of_le_of_lt (cdf_nonneg μ (x-1)) (hmono (by linarith))
  · exact lt_of_lt_of_le (hmono (show x < x+1 by linarith)) (cdf_le_one μ (x+1))

lemma exists_cdf_eq (μ : Measure ℝ) (hc : Continuous (cdf μ))
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : ∃ x, cdf μ x = r := by
  obtain ⟨a,ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const hr.1).exists
  obtain ⟨b,hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt hr.2).exists
  exact intermediate_value_univ a b hc ⟨ha.le, hb.le⟩

lemma cdf_hasLaw_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) (hmono : StrictMono (cdf μ)) :
    HasLaw (cdf μ) (volume.restrict (Ioc (0 : ℝ) 1)) μ := by
  have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  refine ⟨hc.measurable.aemeasurable, ?_⟩
  apply Measure.ext_of_Iic
  intro r
  rw [Measure.map_apply hc.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  rcases le_or_gt r 0 with hr | hr
  · have hp : (cdf μ) ⁻¹' Iic r = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_le_of_gt (lt_of_le_of_lt hr (cdf_mem_Ioo_of_strictMono μ hmono x).1)) hx
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact not_lt_of_ge (hx.1.trans hr) hx.2.1
    simp [hp,hi]
  rcases le_or_gt 1 r with hr1 | hr1
  · have hp : (cdf μ) ⁻¹' Iic r = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (cdf_le_one μ x).trans hr1
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = Ioc 0 1 :=
      inter_eq_right.mpr (fun x hx ↦ hx.2.trans hr1)
    simp [hp,hi]
  · obtain ⟨x,hx⟩ := exists_cdf_eq μ hc ⟨hr,hr1⟩
    have hp : (cdf μ) ⁻¹' Iic r = Iic x := by
      ext y
      simp only [mem_preimage, mem_Iic, ← hx, hmono.le_iff_le]
    have hi : Iic r ∩ Ioc (0 : ℝ) 1 = Ioc 0 r := by
      ext y
      constructor
      · exact fun hy ↦ ⟨hy.2.1,hy.1⟩
      · exact fun hy ↦ ⟨hy.2,hy.1,hy.2.trans hr1.le⟩
    rw [hp,hi, ← ofReal_cdf μ, hx, Real.volume_Ioc, sub_zero]

lemma standardGaussian_cdf_hasLaw_uniform :
    HasLaw (cdf (gaussianReal 0 1)) (volume.restrict (Ioc (0 : ℝ) 1)) (gaussianReal 0 1) := by
  let := nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  exact cdf_hasLaw_uniform _ (continuous_cdf_of_nullSingleton _) (strictMono_gaussian_cdf (by norm_num))

lemma measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Ioi measurable_const measurable_const)

lemma abs_real_sign_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

lemma uniform_rounding_mean {a : ℝ} (ha : |a|≤1) :
    ∫ z in Ioc (0 : ℝ) 1, Real.sign (a+2*z-1) = a := by
  let r : ℝ := (1-a)/2
  have hr0 : 0≤r := by dsimp [r]; linarith [(abs_le.mp ha).2]
  have hr1 : r≤1 := by dsimp [r]; linarith [(abs_le.mp ha).1]
  have hi : Iic r ∩ Ioc (0 : ℝ) 1 = Ioc 0 r := by
    ext z
    constructor
    · exact fun hz ↦ ⟨hz.2.1,hz.1⟩
    · exact fun hz ↦ ⟨hz.2,hz.1,hz.2.trans hr1⟩
  have heq : (fun z ↦ Real.sign (a+2*z-1)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun z ↦ 1 - 2 * (Iic r).indicator (fun _ ↦ (1 : ℝ)) z) := by
    filter_upwards [(volume.restrict (Ioc (0 : ℝ) 1)).ae_ne r] with z hz
    rcases lt_or_gt_of_ne hz with hzr | hrz
    · rw [Real.sign_of_neg (by dsimp [r] at hzr; linarith), indicator_of_mem (show z ∈ Iic r from hzr.le)]
      norm_num
    · rw [Real.sign_of_pos (by dsimp [r] at hrz; linarith), indicator_of_notMem (show z ∉ Iic r from not_le_of_gt hrz)]
      norm_num
  rw [integral_congr_ae heq,
    integral_sub (integrable_const _) (((integrable_const (1 : ℝ)).indicator measurableSet_Iic).const_mul 2),
    integral_const, integral_const_mul, integral_indicator_const _ measurableSet_Iic,
    measureReal_restrict_apply measurableSet_Iic, hi, Real.volume_real_Ioc]
  simp only [measureReal_restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_real_Ioc, sub_zero, max_eq_left hr0]
  norm_num
  dsimp [r]
  ring

lemma gaussian_rounding_mean {a : ℝ} (ha : |a|≤1) :
    ∫ z, Real.sign (a+2*cdf (gaussianReal 0 1) z-1) ∂gaussianReal 0 1 = a := by
  have hm : Measurable (fun z : ℝ ↦ Real.sign (a+2*z-1)) :=
    measurable_real_sign.comp (by fun_prop)
  have H := standardGaussian_cdf_hasLaw_uniform.integral_comp hm.aestronglyMeasurable
  exact H.trans (uniform_rounding_mean ha)

lemma product_rounding_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {U K : Ω → ℝ}
    (hU : Measurable U) (hbound : ∀ᵐ ω ∂μ, |U ω| ≤ 1) (hK : Integrable K μ) :
    ∫ p : Ω × ℝ, Real.sign (U p.1 + 2*cdf (gaussianReal 0 1) p.2-1)*K p.1
      ∂μ.prod (gaussianReal 0 1) = ∫ ω, U ω*K ω ∂μ := by
  have hm : Measurable (fun p : Ω × ℝ ↦
      Real.sign (U p.1+2*cdf (gaussianReal 0 1) p.2-1)) := by
    apply measurable_real_sign.comp
    have hc : Measurable (fun p : Ω × ℝ ↦ cdf (gaussianReal 0 1) p.2) :=
      ((monotone_cdf _).measurable).comp measurable_snd
    exact ((hU.comp measurable_fst).add (hc.const_mul 2)).sub_const 1
  have hi : Integrable (fun p : Ω × ℝ ↦
      Real.sign (U p.1+2*cdf (gaussianReal 0 1) p.2-1)*K p.1)
      (μ.prod (gaussianReal 0 1)) := by
    apply (hK.comp_fst _).bdd_mul hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p ↦ by
      simpa only [Real.norm_eq_abs] using abs_real_sign_le_one (U p.1+2*cdf (gaussianReal 0 1) p.2-1))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hbound] with ω hω
  rw [integral_mul_const, gaussian_rounding_mean hω]

lemma independent_rounding_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U K Z : Ω → ℝ}
    (hU : Measurable U) (hK : Measurable K) (hKi : Integrable K μ)
    (hbound : ∀ᵐ ω ∂μ, |U ω|≤1) (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (hind : IndepFun (fun ω ↦ (U ω,K ω)) Z μ) :
    (∫ ω, Real.sign (U ω+2*cdf (gaussianReal 0 1) (Z ω)-1)*K ω ∂μ) =
      ∫ ω, U ω*K ω ∂μ := by
  let V : Ω → ℝ × ℝ := fun ω ↦ (U ω,K ω)
  let ν : Measure (ℝ × ℝ) := μ.map V
  have hV : Measurable V := hU.prodMk hK
  have hLaw : HasLaw V ν μ := ⟨hV.aemeasurable, rfl⟩
  have hJoint := hind.hasLaw_prod hLaw hZ
  have hKi' : Integrable (Prod.snd : ℝ × ℝ → ℝ) ν :=
    (integrable_map_measure measurable_snd.aestronglyMeasurable hV.aemeasurable).mpr hKi
  have hbound' : ∀ᵐ p : ℝ × ℝ ∂ν, |p.1|≤1 := by
    apply (ae_map_iff hV.aemeasurable (measurableSet_le measurable_fst.abs measurable_const)).mpr
    exact hbound
  have hm : Measurable (fun p : (ℝ × ℝ) × ℝ ↦
      Real.sign (p.1.1+2*cdf (gaussianReal 0 1) p.2-1)*p.1.2) := by
    have hc : Measurable (fun p : (ℝ × ℝ) × ℝ ↦ cdf (gaussianReal 0 1) p.2) :=
      ((monotone_cdf _).measurable).comp measurable_snd
    exact (measurable_real_sign.comp
      (((measurable_fst.comp measurable_fst).add (hc.const_mul 2)).sub_const 1)).mul
        (measurable_snd.comp measurable_fst)
  calc
    _ = ∫ p : (ℝ × ℝ) × ℝ, Real.sign (p.1.1+2*cdf (gaussianReal 0 1) p.2-1)*p.1.2
        ∂ν.prod (gaussianReal 0 1) := hJoint.integral_comp hm.aestronglyMeasurable
    _ = ∫ p : ℝ × ℝ, p.1*p.2 ∂ν := product_rounding_integral measurable_fst hbound' hKi'
    _ = _ := (hLaw.integral_comp (measurable_fst.mul measurable_snd).aestronglyMeasurable).symm

end SKValue

end

end OAI
