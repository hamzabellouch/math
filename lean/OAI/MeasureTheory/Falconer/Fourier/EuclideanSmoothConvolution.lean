import OAI.MeasureTheory.Falconer.Geometry.EuclideanMollifier

namespace OAI

/-! Smooth densities for convolution with the chosen Euclidean mollifier. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal NNReal Convolution
variable {d : ℕ}


noncomputable def euclideanSmoothDensity (α : Measure (Space d)) (b : Space d → ℝ) (x : Space d) : ℝ :=
  ∫ y, b (x-y) ∂α

theorem euclideanSmoothDensity_nonneg (α : Measure (Space d)) (b : Space d → ℝ)
    (hb : ∀ y, 0 ≤ b y) (x : Space d) : 0 ≤ euclideanSmoothDensity α b x :=
  integral_nonneg (fun _ => hb _)

theorem euclidean_kernel_translate_integrable (α : Measure (Space d)) [IsFiniteMeasure α]
    (b : Space d → ℝ) (hc : HasCompactSupport b) (hb : Continuous b) (x : Space d) :
    Integrable (fun y => b (x-y)) α := by
  exact (hb.comp (by fun_prop)).integrable_of_hasCompactSupport
    (hc.comp_homeomorph (Homeomorph.subLeft x))

theorem euclideanSmoothDensity_smooth (α : Measure (Space d)) [IsFiniteMeasure α]
    (b : Space d → ℝ) (hc : HasCompactSupport b) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanSmoothDensity α b) := by
  have h := contDiffOn_convolution_right_with_param_comp (μ := α)
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun x : Space d => x) contDiffOn_id isOpen_univ hc
    (g := fun _ : Space d => b) (fun _ _ _ hx => image_eq_zero_of_notMem_tsupport hx)
    (f := fun _ : Space d => (1 : ℝ)) continuous_const.locallyIntegrable
    (hb.comp contDiff_snd).contDiffOn
  rw [contDiffOn_univ] at h
  convert h using 1
  funext x
  simp only [convolution,ContinuousLinearMap.mul_apply',one_mul,euclideanSmoothDensity]

theorem euclideanSmoothDensity_compact (α : Measure (Space d)) [IsFiniteMeasure α]
    (b : Space d → ℝ) (hc : HasCompactSupport b) {K : Set (Space d)} (hK : IsCompact K)
    (hα : ∀ᵐ y ∂α, y ∈ K) : HasCompactSupport (euclideanSmoothDensity α b) := by
  apply HasCompactSupport.intro (hK.add hc)
  intro x hx
  apply integral_eq_zero_of_ae
  filter_upwards [hα] with y hy
  apply image_eq_zero_of_notMem_tsupport
  intro hb
  exact hx ⟨y,hy,x-y,hb,by abel_nf⟩

theorem euclideanSmoothDensity_measure (α : Measure (Space d)) [IsFiniteMeasure α]
    (b : Space d → ℝ) (hc : HasCompactSupport b) (hb : Continuous b) (hn : ∀ x, 0 ≤ b x) :
    α ∗ euclideanDensityMeasure b = euclideanDensityMeasure (euclideanSmoothDensity α b) := by
  let := euclideanDensityMeasure_finite b hc hb hn
  have hbm : Measurable b := hb.measurable
  have he (f : Space d → ℝ≥0∞) (hf : Measurable f) :
      (∫⁻ x, f x ∂(α ∗ euclideanDensityMeasure b)) =
        ∫⁻ x, f x ∂euclideanDensityMeasure (euclideanSmoothDensity α b) := by
    rw [Measure.lintegral_conv hf]
    simp only [euclideanDensityMeasure]
    have hinner (y : Space d) :
        (∫⁻ x, f (y+x) ∂volume.withDensity (fun x => ENNReal.ofReal (b x))) =
          ∫⁻ x, ENNReal.ofReal (b x) * f (y+x) :=
      lintegral_withDensity_eq_lintegral_mul _ hbm.ennreal_ofReal
        (hf.comp (measurable_const.add measurable_id))
    simp_rw [hinner]
    have hd (x : Space d) : ENNReal.ofReal (euclideanSmoothDensity α b x) =
        ∫⁻ y, ENNReal.ofReal (b (x-y)) ∂α :=
      ofReal_integral_eq_lintegral_ofReal (euclidean_kernel_translate_integrable α b hc hb x)
        (Filter.Eventually.of_forall (fun _ => hn _))
    have hm : Measurable (fun p : Space d × Space d => ENNReal.ofReal (b (p.1-p.2))) := by fun_prop
    have hdm : Measurable (fun x => ENNReal.ofReal (euclideanSmoothDensity α b x)) := by
      simp_rw [hd]
      exact hm.lintegral_prod_right'
    rw [lintegral_withDensity_eq_lintegral_mul _ hdm hf]
    have hmul (x : Space d) : (∫⁻ y, ENNReal.ofReal (b (x-y)) ∂α) * f x =
        ∫⁻ y, ENNReal.ofReal (b (x-y)) * f x ∂α :=
      (lintegral_mul_const _ (by fun_prop)).symm
    simp only [Pi.mul_apply]
    simp_rw [hd,hmul]
    conv_rhs => rw [lintegral_lintegral_swap (by fun_prop)]
    apply lintegral_congr
    intro y
    have ht := lintegral_add_left_eq_self (μ := (volume : Measure (Space d)))
      (fun x => ENNReal.ofReal (b (x-y)) * f x) y
    simpa only [add_sub_cancel_left] using ht
  exact Measure.ext_of_lintegral _ he

end Falconer

end OAI
