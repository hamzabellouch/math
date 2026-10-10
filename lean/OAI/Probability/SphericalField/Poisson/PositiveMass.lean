import Mathlib
import OAI.Probability.SphericalField.Poisson.Campbell

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma poissonRandomMeasureLaw_lintegral_pos_of_infinite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] (hκ : κ univ = ⊤)
    {f : S → ℝ} (hf : Measurable f) (hfpos : ∀ x, 0 < f x) :
    ∀ᵐ η ∂poissonRandomMeasureLaw κ, 0 < ∫⁻ x, ENNReal.ofReal (f x) ∂η := by
  have hconst : Measurable (fun _ : S => (1 : ℝ)) := measurable_const
  have he := poissonRandomMeasureLaw_laplace κ hconst (fun _ => zero_le_one)
  have hc : ENNReal.ofReal (1 - Real.exp (-1)) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  rw [lintegral_const,hκ,ENNReal.mul_top hc,expNegENNReal_top] at he
  have hi : Integrable (poissonLaplace (fun _ : S => (1 : ℝ))) (poissonRandomMeasureLaw κ) := by
    apply Integrable.of_bound (poissonLaplace_measurable hconst).aestronglyMeasurable 1
    exact ae_of_all _ fun η => by
      rw [Real.norm_eq_abs,abs_of_nonneg (poissonLaplace_bounds _ η).1]
      exact (poissonLaplace_bounds _ η).2
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun η => (poissonLaplace_bounds (fun _ : S => (1 : ℝ)) η).1) hi).mp he
  filter_upwards [hae] with η hη
  have hsp : Function.support (fun x => ENNReal.ofReal (f x)) = univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (hfpos x))
  rw [lintegral_pos_iff_support hf.ennreal_ofReal,hsp]
  by_contra hn
  have hz : η univ = 0 := bot_unique (le_of_not_gt hn)
  simp only [poissonLaplace,lintegral_const,ENNReal.ofReal_one,one_mul,hz,
    expNegENNReal_finite (by simp : (0 : ℝ≥0∞) ≠ ⊤),ENNReal.toReal_zero,neg_zero,Real.exp_zero] at hη
  exact one_ne_zero hη

lemma stablePoisson_total_positive {b : ℝ} (hb : 0 < b) :
    ∀ᵐ η ∂poissonRandomMeasureLaw (stableLogIntensity b),
      0 < ∫⁻ x, ENNReal.ofReal (Real.exp x) ∂η :=
  poissonRandomMeasureLaw_lintegral_pos_of_infinite _ (stableLogIntensity_univ hb)
    Real.measurable_exp Real.exp_pos

lemma standardGaussian_density_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hd := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert! hd using 1
  · funext y
    simp [gaussianPDFReal]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,Pi.neg_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat]
    norm_num
    ring

lemma standardGaussian_density_mul_integrable :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  convert hi using 1
  funext x
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [show -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
  ring

def finiteMeasureCutKernel {S : Type*} [MeasurableSpace S] (n : ℕ) : Kernel (Measure S) S where
  toFun η := if η univ ≤ n then η else 0
  measurable' := measurable_id.piecewise
    (measurableSet_le (Measure.measurable_coe .univ) measurable_const) measurable_const

instance finiteMeasureCutKernel_finite {S : Type*} [MeasurableSpace S] (n : ℕ) :
    IsFiniteKernel (finiteMeasureCutKernel (S := S) n) := by
  refine ⟨n,by simp,fun η => ?_⟩
  change (if η univ ≤ n then η else 0) univ ≤ n
  split_ifs with h
  · exact h
  · simp

lemma aemeasurable_measure_lintegral_of_finite {S : Type*} [MeasurableSpace S]
    {P : Measure (Measure S)} (hP : ∀ᵐ η ∂P, η univ < ⊤)
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    AEMeasurable (fun η => ∫⁻ x, H (η,x) ∂η) P := by
  have hm : Measurable (fun η => ⨆ n : ℕ, ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel n η) :=
    Measurable.iSup fun n => hH.lintegral_kernel_prod_right' (κ := finiteMeasureCutKernel n)
  apply hm.aemeasurable.congr
  filter_upwards [hP] with η hη
  apply le_antisymm
  · apply iSup_le
    intro n
    change (∫⁻ x, H (η,x) ∂(if η univ ≤ n then η else 0)) ≤ _
    split_ifs <;> simp
  · obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hη.ne
    calc
      (∫⁻ x, H (η,x) ∂η) = ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel n η := by
        change _ = ∫⁻ x, H (η,x) ∂(if η univ ≤ n then η else 0)
        rw [ite_eq_left hn.le]
      _ ≤ _ := le_iSup (fun m : ℕ => ∫⁻ x, H (η,x) ∂finiteMeasureCutKernel m η) n

lemma finitePoissonLaw_ae_finite {S : Type*} [MeasurableSpace S]
    (r : ℝ≥0) (ν : Measure S) :
    ∀ᵐ η ∂finitePoissonLaw r ν, η univ < ⊤ := by
  rw [finitePoissonLaw,Measure.ae_sum_iff]
  intro n
  apply Measure.ae_smul_measure
  rw [ae_map_iff (finitePointMeasure_measurable n).aemeasurable
    (measurableSet_lt (Measure.measurable_coe .univ) measurable_const)]
  exact ae_of_all _ fun x => by simp [finitePointMeasure,Measure.finsetSum_apply]

lemma finitePointMeasure_insertNth {S : Type*} [MeasurableSpace S]
    (n : ℕ) (i : Fin (n+1)) (x : S) (y : Fin n → S) :
    finitePointMeasure (n+1) (i.insertNth x y) = Measure.dirac x + finitePointMeasure n y := by
  classical
  rw [finitePointMeasure,Fin.sum_univ_succAbove _ i]
  simp [finitePointMeasure]

lemma finite_point_mecke {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (n : ℕ)
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y : Fin (n+1) → S, ∑ i, H (finitePointMeasure (n+1) y,y i)
      ∂Measure.pi (fun _ => ν)) = (n+1 : ℝ≥0∞) *
      ∫⁻ x, ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x)
        ∂Measure.pi (fun _ => ν) ∂ν := by
  classical
  rw [lintegral_finsetSum (f := fun (i : Fin (n+1)) (y : Fin (n+1) → S) => H (finitePointMeasure (n+1) y,y i)) _ (fun i _ => hH.comp
    ((finitePointMeasure_measurable _).prodMk (measurable_pi_apply i)))]
  have he (i : Fin (n+1)) :
      (∫⁻ y : Fin (n+1) → S, H (finitePointMeasure (n+1) y,y i)
        ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, ∫⁻ y : Fin n → S, H (Measure.dirac x + finitePointMeasure n y,x)
        ∂Measure.pi (fun _ => ν) ∂ν := by
    have hm : Measurable (fun y : Fin (n+1) → S => H (finitePointMeasure (n+1) y,y i)) :=
      hH.comp ((finitePointMeasure_measurable _).prodMk (measurable_pi_apply i))
    rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) i).symm).lintegral_comp hm]
    change (∫⁻ p : S × (Fin n → S), H (finitePointMeasure (n+1) (i.insertNth p.1 p.2),
      ((i.insertNth p.1 p.2 : Fin (n+1) → S) i)) ∂ν.prod (Measure.pi fun _ => ν)) = _
    simp only [finitePointMeasure_insertNth,Fin.insertNth_apply_same]
    exact lintegral_prod _ (hH.comp
      (((by fun_prop : Measurable (fun p : S × (Fin n → S) =>
        Measure.dirac p.1 + finitePointMeasure n p.2))).prodMk measurable_fst)).aemeasurable
  simp_rw [he]
  simp

end SphericalPerceptron
end
end

end OAI
