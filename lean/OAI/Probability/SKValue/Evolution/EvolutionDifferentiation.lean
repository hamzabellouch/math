import Mathlib
import OAI.Probability.SKValue.Evolution.SmoothEvolution
import OAI.Probability.SKValue.Evolution.EvolveStrips
import OAI.Probability.SKValue.Equations.ParametricChain

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma SmoothEvolution.jet_joint_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) :
    ContinuousOn (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  obtain ⟨L,hL,hl⟩ := h.jet_joint n
  have hh : LipschitzOnWith ⟨2*L,by positivity⟩
      (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    simp only [Real.dist_eq,Prod.dist_eq]
    have hb := hl p.1 hp.1 q.1 hq.1 q.2 p.2
    change |iteratedDeriv n (deriv (V p.1)) p.2-iteratedDeriv n (deriv (V q.1)) q.2|≤
      (2*L)*max |p.1-q.1| |p.2-q.2|
    have hm1 := le_max_left |p.1-q.1| |p.2-q.2|
    have hm2 := le_max_right |p.1-q.1| |p.2-q.2|
    nlinarith
  exact hh.continuousOn

lemma SmoothEvolution.jet_joint_continuousAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T) (x : ℝ) :
    ContinuousAt (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (V p.1)) p.2) (t,x) := by
  exact (h.jet_joint_continuousOn n (t,x) ⟨⟨ht.1.le,ht.2.le⟩,mem_univ x⟩).continuousAt
    (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem)

lemma SmoothEvolution.gradient_time_hasDerivAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T)
    (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ deriv (V s) x)
      (-((1/2 : ℝ)*deriv (deriv (deriv (V t))) x+γ t*(deriv (V t) x*deriv (deriv (V t)) x))) t := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x)
  have hc0 : ContinuousOn (fun r ↦ deriv (V r) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_zero] using h.continuous_jet 0 x
  have hc1 : ContinuousOn (fun r ↦ deriv (deriv (V r)) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_one] using h.continuous_jet 1 x
  have hc2 : ContinuousOn (fun r ↦ deriv (deriv (deriv (V r))) x) (Icc (0 : ℝ) T) := by
    simpa only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
      using h.continuous_jet 2 x
  have hti : t∈Icc (0 : ℝ) T := ⟨ht.1.le,ht.2.le⟩
  have hn := Icc_mem_nhds ht.1 ht.2
  have hgc : ContinuousAt g t :=
    (continuousAt_const.mul ((hc2 t hti).continuousAt hn)).add
      (hγ.mul (((hc0 t hti).continuousAt hn).mul ((hc1 t hti).continuousAt hn)))
  have hgm : StronglyMeasurableAtFilter g (𝓝 t) volume := by
    refine ⟨Icc (0 : ℝ) T,hn,?_⟩
    exact (aestronglyMeasurable_const.mul (hc2.aestronglyMeasurable measurableSet_Icc)).add
      (hm.aestronglyMeasurable.mul ((hc0.aestronglyMeasurable measurableSet_Icc).mul
        (hc1.aestronglyMeasurable measurableSet_Icc)))
  have hd := (hasDerivAt_const t (deriv (V t) x)).sub
    (intervalIntegral.integral_hasDerivAt_right (a := t) (b := t) (by simp) hgm hgc)
  simp only [zero_sub] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with s hs
  have hh := h.gradient_pde t hti s hs x
  dsimp only [g,Pi.sub_apply] at *
  linarith

lemma SmoothEvolution.gradient_curve_hasDerivAt {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hm : Measurable γ) {t : ℝ} (ht : t∈Ioo (0 : ℝ) T)
    (hγ : ContinuousAt γ t) {φ : ℝ → ℝ} {b : ℝ} (hφ : HasDerivAt φ b t) :
    HasDerivAt (fun s ↦ deriv (V s) (φ s))
      (-((1/2 : ℝ)*deriv (deriv (deriv (V t))) (φ t)+
        γ t*(deriv (V t) (φ t)*deriv (deriv (V t)) (φ t)))+deriv (deriv (V t)) (φ t)*b) t := by
  apply hasDerivAt_parametric_comp (h.gradient_time_hasDerivAt hm ht hγ (φ t)) hφ
  · have he : ∀ᶠ p : ℝ×ℝ in 𝓝 (t,φ t), p.1∈Icc (0 : ℝ) T :=
      continuousAt_fst.preimage_mem_nhds (Icc_mem_nhds ht.1 ht.2)
    filter_upwards [he] with p hp
    exact ((h.slices p.1 hp).jets.smooth.differentiable
      (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) p.2).hasDerivAt
  · simpa only [iteratedDeriv_one] using h.jet_joint_continuousAt 1 ht (φ t)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma sqrt_difference_bound {δ u v : ℝ} (hδ : 0<δ) (hu : δ≤u) (hv : δ≤v) :
    |Real.sqrt u-Real.sqrt v|≤(Real.sqrt δ)⁻¹*|u-v| := by
  have hd := Real.sqrt_pos.mpr hδ
  have hu0 := hδ.le.trans hu
  have hv0 := hδ.le.trans hv
  have he : |u-v|=|Real.sqrt u-Real.sqrt v| * (Real.sqrt u+Real.sqrt v) := by
    rw [←abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),←abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hu0,Real.sq_sqrt hv0]
  have hh : Real.sqrt δ≤Real.sqrt u+Real.sqrt v := by
    linarith [Real.sqrt_le_sqrt hu,Real.sqrt_nonneg v]
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hd).mpr
  rw [he]
  exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)

lemma SmoothEvolution.heat_gradient_derivative_integral {T a t : ℝ} {γ : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V) (hm : Measurable γ)
    (ha : 0≤a) (hat : a<t) (ht : t<T) (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ heat (s-a) (deriv (V s)) x)
      (∫ z, -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) ∂standardGaussian) t := by
  let q := (a+t)/2
  have haq : a<q := by dsimp [q]; linarith
  have hqt : q<t := by dsimp [q]; linarith
  have hq0 : 0≤q := ha.trans haq.le
  have hti : t∈Icc (0 : ℝ) T := ⟨ha.trans hat.le,ht.le⟩
  have hψ := (h.slices t hti).jets
  let F := fun s z ↦ deriv (V s) (x+Real.sqrt (s-a)*z)
  let F' := fun z ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a)))
  obtain ⟨L,hL,hl⟩ := h.jet_joint 0
  simp only [iteratedDeriv_zero] at hl
  let bd := fun z : ℝ ↦ L*(1+(Real.sqrt (q-a))⁻¹*|z|)
  have hbd : Integrable bd standardGaussian := by
    exact ((integrable_const 1).add (((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs.const_mul _)).const_mul L
  have hfc0 : Continuous (deriv (V t)) := hψ.smooth.continuous
  have hfc1 : Continuous (deriv (deriv (V t))) := hψ.deriv.smooth.continuous
  have hfc2 : Continuous (deriv (deriv (deriv (V t)))) := hψ.deriv.deriv.smooth.continuous
  apply (hasDerivAt_integral_of_dominated_loc_of_lip
    (F := F) (F' := F') (s := Icc q T) (bound := bd) (μ := standardGaussian)
    (Icc_mem_nhds hqt ht)
    (by
      filter_upwards [Icc_mem_nhds hqt ht] with s hs
      exact (((h.slices s ⟨hq0.trans hs.1,hs.2⟩).jets.smooth.continuous).comp (by fun_prop)).aestronglyMeasurable)
    (hψ.expGrowth.shift_integrable hψ.smooth.continuous.measurable x (Real.sqrt (t-a)))
    (by dsimp [F']; fun_prop) _ hbd _).2
  · filter_upwards [] with z
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs r hr
    have hb := hl s ⟨hq0.trans hs.1,hs.2⟩ r ⟨hq0.trans hr.1,hr.2⟩
      (x+Real.sqrt (r-a)*z) (x+Real.sqrt (s-a)*z)
    have hsr := sqrt_difference_bound (sub_pos.mpr haq)
      (show q - a ≤ s - a by linarith [hs.1]) (show q - a ≤ r - a by linarith [hr.1])
    rw [sub_sub_sub_cancel_right] at hsr
    have he : |(x+Real.sqrt (s-a)*z)-(x+Real.sqrt (r-a)*z)|=
        |Real.sqrt (s-a)-Real.sqrt (r-a)| * |z| := by rw [add_sub_add_left_eq_sub,←sub_mul,abs_mul]
    rw [he] at hb
    simp only [Real.dist_eq,Real.coe_nnabs]
    change |F s z-F r z|≤|bd z| * |s-r|
    have hbd0 : 0 ≤ bd z := by dsimp [bd]; positivity
    rw [abs_of_nonneg hbd0]
    dsimp only [F,bd]
    have hmul := mul_le_mul_of_nonneg_right hsr (abs_nonneg z)
    nlinarith
  · filter_upwards [] with z
    have hs := ((Real.hasDerivAt_sqrt (sub_pos.mpr hat).ne').comp t
      ((hasDerivAt_id t).sub_const a)).mul_const z
    have hφ := hs.const_add x
    convert! h.gradient_curve_hasDerivAt hm ⟨ha.trans_lt hat,ht⟩ hγ hφ using 1
    dsimp [F,F']
    ring

end SKValue

end

end OAI
