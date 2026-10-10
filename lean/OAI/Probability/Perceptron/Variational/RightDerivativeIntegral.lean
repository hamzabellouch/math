import Mathlib
import OAI.Probability.Perceptron.Variational.FieldDerivative

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction

lemma rightDerivative_translate {F : ℝ→ℝ} {D s : ℝ}
    (hd : HasDerivWithinAt (fun t => F (s+t)) D (Ici 0) 0) :
    HasDerivWithinAt F D (Ici s) s := by
  have hd' : HasDerivWithinAt (fun t => F (s+t)) D (Ici 0) (s-s) := by simpa using hd
  have ht : HasDerivWithinAt (fun t : ℝ => t-s) 1 (Ici s) s := by
    simpa using ((hasDerivAt_id s).sub_const s).hasDerivWithinAt (s := Ici s)
  have hm : MapsTo (fun t : ℝ => t-s) (Ici s) (Ici 0) := by
    intro t ht
    change 0 ≤ t-s
    exact sub_nonneg.mpr (show s ≤ t from ht)
  have he := hd.comp_of_eq s ht hm (by simp)
  simpa only [Function.comp_def,show ∀ x : ℝ, s+(x-s)=x by intro x; ring,mul_one] using he

lemma integral_hasDerivWithinAt_right {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] {F : A→ℝ→ℝ} {D : A→ℝ} {C : ℝ}
    (hF : ∀ t, Integrable (fun a => F a t) μ)
    (hD : ∀ᵐ a ∂μ, HasDerivWithinAt (F a) (D a) (Ici 0) 0)
    (hC : ∀ t, 0 ≤ t → ∀ᵐ a ∂μ, |F a t-F a 0| ≤ C*t) :
    HasDerivWithinAt (fun t => ∫ a, F a t ∂μ) (∫ a, D a ∂μ) (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have he (t : ℝ) : slope (fun t => ∫ a, F a t ∂μ) 0 t =
      ∫ a, slope (F a) 0 t ∂μ := by
    simp only [slope,sub_zero,vsub_eq_sub,smul_eq_mul,integral_const_mul,integral_sub (hF t) (hF 0)]
  change Tendsto (fun t => slope (fun t => ∫ a, F a t ∂μ) 0 t) _ _
  simp_rw [he]
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C)
  · exact Eventually.of_forall fun t => by
      simpa only [slope,sub_zero,vsub_eq_sub,smul_eq_mul,Pi.sub_apply] using ((hF t).sub (hF 0)).aestronglyMeasurable.const_mul t⁻¹
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht.2)
    filter_upwards [hC t ht0.le] with a ha
    simp only [slope,sub_zero,vsub_eq_sub,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_inv,abs_of_pos ht0]
    calc
      t⁻¹*|F a t-F a 0| ≤ t⁻¹*(C*t) := mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr ht0.le)
      _ = C := by field_simp
  · exact integrable_const C
  · exact hD.mono fun a ha => hasDerivWithinAt_iff_tendsto_slope.mp ha

lemma sourceConditional_field_continuous (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (b : SourceBaseData n k) :
    Continuous (fun h => ∫ g, sourceKernelPressure n k f p d u h (b,g) ∂countableGaussianLaw) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (g := fun h' => sourceFieldDistance p d u h' h) ?_ ?_
  · intro h'
    simpa only [Real.norm_eq_abs] using sourceConditional_field_comparison n k f p d u h' h b
  · have hc : Tendsto (fun h' => sourceFieldDistance p d u h' h) (𝓝 h)
        (𝓝 (sourceFieldDistance p d u h h)) := (sourceFieldDistance_continuous p d u h).continuousAt
    rwa [sourceFieldDistance_self] at hc

lemma sourceConditional_field_slope (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) :
    HasDerivWithinAt (fun t => ∫ g, sourceKernelPressure n k f p d u (fun l => h l+t*a l) (b,g)
        ∂countableGaussianLaw)
      (-(∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d h u (b,g)) 2 (sourceFieldObservable a) ∂countableGaussianLaw))
      (Ici 0) 0 := by
  have H := sourceConditional_field_right_derivative n k f p d u hh0 hh ha0 ha b
  dsimp only at H
  rw [sourceConditional_response_eq n k f p d u h ha0 ha b] at H
  convert H using 1
  field_simp
  ring

lemma sourceConditional_field_slope_at (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun t => ∫ g, sourceKernelPressure n k f p d u (fun l => h l+t*a l) (b,g)
        ∂countableGaussianLaw)
      (-(∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d (fun l => h l+s*a l) u (b,g)) 2
        (sourceFieldObservable a) ∂countableGaussianLaw)) (Ici s) s := by
  apply rightDerivative_translate
  have hd := sourceConditional_field_slope n k f p d u
    (fun l => add_nonneg (hh0 l) (mul_nonneg hs (ha0 l))) (hh.add (ha.const_mul hs)) ha0 ha b
  convert hd using 1
  funext t
  have he : (fun l => h l+(s+t)*a l) = (fun l => h l+s*a l+t*a l) := by
    funext l; ring
  rw [he]

lemma sourceConditional_field_direction_bound (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) {s : ℝ} (hs : 0 ≤ s) :
    |(∫ g, sourceKernelPressure n k f p d u (fun l => h l+s*a l) (b,g) ∂countableGaussianLaw)-
      ∫ g, sourceKernelPressure n k f p d u h (b,g) ∂countableGaussianLaw| ≤ a (Fin.last k)*s := by
  have hc : Continuous (fun t : ℝ => ∫ g, sourceKernelPressure n k f p d u (fun l => h l+t*a l) (b,g)
      ∂countableGaussianLaw) := (sourceConditional_field_continuous n k f p d u b).comp (by fun_prop)
  have hbound (t : ℝ) : ‖-(∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
      (sourceCouplingHamiltonian n k f p d (fun l => h l+t*a l) u (b,g)) 2
      (sourceFieldObservable a) ∂countableGaussianLaw)‖ ≤ a (Fin.last k) := by
    rw [norm_neg]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := countableGaussianLaw)
      (ae_of_all _ fun g => show ‖gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d (fun l => h l+t*a l) u (b,g)) 2
        (sourceFieldObservable a)‖ ≤ a (Fin.last k) by
          simpa only [Real.norm_eq_abs] using sourceConditional_field_observable_bound n k f p d u _ ha0 ha b g)
  have he := norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn
    (fun t ht => sourceConditional_field_slope_at n k f p d u hh0 hh ha0 ha b ht.1)
    (fun t _ => hbound t) s (show s ∈ Icc 0 s from ⟨hs,le_rfl⟩)
  simpa only [zero_mul,add_zero,sub_zero,Real.norm_eq_abs] using he

theorem sourceExpectedPressure_field_right_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    HasDerivWithinAt (fun s => sourceExpectedPressure n k f p d (fun l => h l+s*a l) z t u)
      (-(∫ b, gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
        (sourceCouplingHamiltonian n k f p d h u b) 2 (sourceFieldObservable a)
          ∂((sourceBaseDataLaw n k z t).prod countableGaussianLaw))) (Ici 0) 0 := by
  have hi (s : ℝ) := ((sourceKernelPressure_memLp n k f p d u (fun l => h l+s*a l)
    z hz hz0 hz1 t).integrable (by norm_num))
  have hd := integral_hasDerivWithinAt_right (sourceBaseDataLaw n k z t)
    (fun s => (hi s).integral_prod_left)
    (ae_of_all _ fun b => sourceConditional_field_slope n k f p d u hh0 hh ha0 ha b)
    (C := a (Fin.last k)) (fun s hs => ae_of_all _ fun b => by
      simpa only [zero_mul,add_zero] using
        sourceConditional_field_direction_bound n k f p d u hh0 hh ha0 ha b hs)
  have hI : Integrable (fun b => gibbsReplicaMean (sourceSpinLeafKernel n k b.1)
      (sourceCouplingHamiltonian n k f p d h u b) 2 (sourceFieldObservable a))
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) :=
    kernel_replicaMean_bounded_integrable (sourceFullSpinLeafKernel n k) _
      (H := sourceCouplingHamiltonian n k f p d h u) (G := fun _ => sourceFieldObservable a)
      (sourceCouplingHamiltonian_measurable n k f p d h u)
      ((sourceFieldObservable_measurable a).comp measurable_snd)
      (ha0 _) (fun _ => sourceFieldObservable_bound ha0 ha)
  simpa only [sourceExpectedPressure,integral_prod _ (hi _),integral_neg,integral_prod _ hI] using hd

end SphericalPerceptronFreeEnergy
end

end OAI
