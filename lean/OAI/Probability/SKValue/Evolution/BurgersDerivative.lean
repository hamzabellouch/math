import Mathlib
import OAI.Probability.SKValue.Evolution.HeatKernelBound
import OAI.Probability.SKValue.Evolution.EvolutionDifferentiation

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma SmoothEvolution.heat_gradient_hasDerivAt {T a t : ℝ} {γ : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V) (hm : Measurable γ)
    (ha : 0≤a) (hat : a<t) (ht : t<T) (hγ : ContinuousAt γ t) (x : ℝ) :
    HasDerivAt (fun s ↦ heat (s-a) (deriv (V s)) x)
      (-γ t * heat (t-a) (fun y ↦ deriv (V t) y * deriv (deriv (V t)) y) x) t := by
  have hψ := (h.slices t ⟨ha.trans hat.le,ht.le⟩).jets
  have hid := gaussian_scale_deriv_eq
    (fun y ↦ (hψ.deriv.smooth.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)) y).hasDerivAt)
    hψ.deriv.deriv.smooth.continuous hψ.deriv.expGrowth hψ.deriv.deriv.expGrowth x (Real.sqrt (t-a))
  have hI := hψ.deriv.deriv.expGrowth.shift_integrable
    hψ.deriv.deriv.smooth.continuous.measurable x (Real.sqrt (t-a))
  have hJ := (hψ.mul hψ.deriv).expGrowth.shift_integrable
    (hψ.smooth.continuous.mul hψ.deriv.smooth.continuous).measurable x (Real.sqrt (t-a))
  have hZ := hψ.deriv.expGrowth.shift_mul_integrable
    hψ.deriv.smooth.continuous.measurable x (Real.sqrt (t-a))
  have he : (∫ z, -((1/2 : ℝ)*deriv (deriv (deriv (V t))) (x+Real.sqrt (t-a)*z)+
        γ t*(deriv (V t) (x+Real.sqrt (t-a)*z)*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)))+
        deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) ∂standardGaussian) =
      -γ t * heat (t-a) (fun y ↦ deriv (V t) y * deriv (deriv (V t)) y) x := by
    have heq (z : ℝ) : deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)*(z/(2*Real.sqrt (t-a))) =
        (2*Real.sqrt (t-a))⁻¹*(z*deriv (deriv (V t)) (x+Real.sqrt (t-a)*z)) := by ring
    simp_rw [heq]
    have hadd := integral_add ((hI.const_mul (1/2 : ℝ)).add (hJ.const_mul (γ t))).neg (hZ.const_mul ((2*Real.sqrt (t-a))⁻¹))
    simp only [Pi.neg_apply,Pi.add_apply] at hadd
    rw [hadd,integral_neg,integral_add (hI.const_mul (1/2 : ℝ)) (hJ.const_mul (γ t))]
    simp only [integral_const_mul]
    rw [hid]
    dsimp only [heat]
    field_simp [(Real.sqrt_pos.mpr (sub_pos.mpr hat)).ne']
    ring
  rw [←he]
  exact h.heat_gradient_derivative_integral hm ha hat ht hγ x

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma heat_family_continuousOn {T : ℝ} {F : ℝ → ℝ → ℝ} {C : ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ F p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ))
    (hC : 0≤C) (hb : ∀ t∈Icc (0 : ℝ) T, ∀ x, |F t x|≤C) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (F t) x) (Icc (0 : ℝ) T) := by
  apply continuousOn_of_dominated (bound := fun _ ↦ |C|) (μ := standardGaussian)
  · intro t ht
    have hct : Continuous (F t) := by
      have hh : ContinuousOn (F t) univ := hc.comp (continuous_const.prodMk continuous_id).continuousOn
        (MapsTo.prodMk (fun _ _ ↦ ht) (fun _ _ ↦ mem_univ _))
      simpa only [Function.comp_def,continuousOn_univ] using hh
    exact (hct.comp (by fun_prop)).aestronglyMeasurable
  · intro t ht
    exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,abs_of_nonneg hC] using hb t ht (x+Real.sqrt (t-a)*z))
  · exact integrable_const |C|
  · filter_upwards [] with z
    exact hc.comp ((continuous_id.prodMk (by fun_prop)).continuousOn)
      (fun t ht ↦ ⟨ht,mem_univ _⟩)

lemma SmoothEvolution.heat_gradient_continuousOn {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (a x : ℝ) :
    ContinuousOn (fun t ↦ heat (t-a) (deriv (V t)) x) (Icc (0 : ℝ) T) := by
  obtain ⟨C,hC,hb⟩ := h.bound 0
  simpa only [iteratedDeriv_zero] using heat_family_continuousOn (h.jet_joint_continuousOn 0) hC hb a x

lemma SmoothEvolution.heat_gradient_lipschitzOn {T a q b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (ha : 0≤a) (haq : a<q) (hqb : q≤b) (hb : b≤T) (x : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (fun t ↦ heat (t-a) (deriv (V t)) x) (Icc q b) := by
  obtain ⟨L,hL,hl⟩ := h.jet_joint 0
  simp only [iteratedDeriv_zero] at hl
  let C := L*(1+(Real.sqrt (q-a))⁻¹)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨⟨C,hC⟩,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro s hs r hr
  have hsub : Icc q b ⊆ Icc (0 : ℝ) T :=
    (Icc_subset_Icc_iff hqb).mpr ⟨ha.trans haq.le,hb⟩
  have hsT : s∈Icc (0 : ℝ) T := hsub hs
  have hrT : r∈Icc (0 : ℝ) T := hsub hr
  have hi (u : ℝ) (hu : u∈Icc (0 : ℝ) T) :
      Integrable (fun z ↦ deriv (V u) (x+Real.sqrt (u-a)*z)) standardGaussian :=
    (h.slices u hu).jets.expGrowth.shift_integrable (h.slices u hu).jets.smooth.continuous.measurable x _
  have hz : Integrable (fun z : ℝ ↦ |z|) standardGaussian :=
    ((memLp_id_gaussianReal' 1 (by norm_num)).integrable le_rfl).abs
  have hbd : Integrable (fun z : ℝ ↦ L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * |z|)) standardGaussian :=
    ((integrable_const _).add (hz.const_mul _)).const_mul L
  have hd : |heat (s-a) (deriv (V s)) x-heat (r-a) (deriv (V r)) x|≤C*|s-r| := by
    unfold heat
    rw [←integral_sub (hi s hsT) (hi r hrT)]
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ z : ℝ, L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * |z|) ∂standardGaussian := by
        apply integral_mono_ae ((hi s hsT).sub (hi r hrT)).abs hbd
        filter_upwards [] with z
        have hh := hl s hsT r hrT (x+Real.sqrt (r-a)*z) (x+Real.sqrt (s-a)*z)
        have he : |(x+Real.sqrt (s-a)*z)-(x+Real.sqrt (r-a)*z)|=
          |Real.sqrt (s-a)-Real.sqrt (r-a)| * |z| := by rw [add_sub_add_left_eq_sub,←sub_mul,abs_mul]
        rw [he] at hh
        have hsr := sqrt_difference_bound (sub_pos.mpr haq)
          (show q-a ≤ s-a by linarith [hs.1]) (show q-a ≤ r-a by linarith [hr.1])
        rw [sub_sub_sub_cancel_right] at hsr
        have hh' := mul_le_mul_of_nonneg_right hsr (abs_nonneg z)
        simp only [Pi.sub_apply]
        exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hh') hL)
      _ = L*(|s-r|+(Real.sqrt (q-a))⁻¹*|s-r| * (∫ z : ℝ, |z| ∂standardGaussian)) := by
        rw [integral_const_mul,integral_add (integrable_const _) (hz.const_mul _),integral_const,integral_const_mul]
        simp
      _ ≤ C*|s-r| := by
        have hh := mul_le_mul_of_nonneg_left standardGaussian_abs_integral_le_one
          (show 0≤L*((Real.sqrt (q-a))⁻¹*|s-r|) by positivity)
        dsimp [C]
        nlinarith
  change dist _ _ ≤ C*dist s r
  simpa only [Real.dist_eq] using hd

end SKValue

end

end OAI
