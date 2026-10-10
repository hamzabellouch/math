import Mathlib
import OAI.Probability.Perceptron.Variational.LabelRestorationMoments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {A : Type*} {S : Type} [MeasurableSpace A] [MeasurableSpace S] {k r : ℕ}

lemma labelRestorationWeight_joint (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    Measurable (Function.uncurry (labelRestorationWeight (S:=S) q s f)) := by
  have h₁ := (labelProfileField_product_measurable (S:=S) q).comp
    (show Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(S×IndexedLeaf k) => (p.1.1,p.2)) from
      measurable_fst.fst.prodMk measurable_snd)
  have h₂ := (labelProfileField_product_measurable (S:=S) q).comp
    (show Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(S×IndexedLeaf k) => (p.1.2,p.2)) from
      measurable_fst.snd.prodMk measurable_snd)
  exact ((gaussianAverageBCF s (expBCF 1 f)).measurable.comp h₁).mul
    ((gaussianAverageBCF s (expBCF 1 f)).measurable.comp h₂)

lemma labelRestorationWeight_exp {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : S×IndexedLeaf k) :
    labelRestorationWeight q s f z x =
      Real.exp (heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)) := by
  have he (a : ℝ) : Real.exp (heatLog s 1 f a)=gaussianAverageBCF s (expBCF 1 f) a := by
    simpa only [NNReal.coe_one,one_mul,gaussianAverageBCF_coe] using exp_heatLog s 1 (by norm_num) f a
  simp only [Real.exp_add,he,labelRestorationWeight]

variable (κ : Kernel A (S×IndexedLeaf k)) [IsMarkovKernel κ]
variable (H : A → S×IndexedLeaf k → ℝ)
variable (q : Fin (k+1) → ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
variable (v w : Fin r → ℝ →ᵇ ℝ) (F : (Fin r → S×IndexedLeaf k) → ℝ)

def labelKernelDenominator (a : A×((ℕ→ℝ)×(ℕ→ℝ))) : ℝ :=
  tiltMean (κ a.1) (H a.1) (labelRestorationWeight q s f a.2) 1

def labelKernelNumerator (a : A×((ℕ→ℝ)×(ℕ→ℝ))) : ℝ :=
  gibbsReplicaMean (κ a.1) (H a.1) r (labelRestorationTest q s f v w F a.2)

lemma labelKernelDenominator_measurable (hH : Measurable (Function.uncurry H)) :
    Measurable (labelKernelDenominator κ H q s f) := by
  have hH' := hH.comp (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.1,p.2)) from measurable_fst.fst.prodMk measurable_snd)
  have hW := (labelRestorationWeight_joint (S:=S) q s f).comp
    (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.2,p.2)) from measurable_fst.snd.prodMk measurable_snd)
  exact kernel_tiltMean_measurable (κ.comap Prod.fst measurable_fst) hH' hW

lemma labelKernelNumerator_measurable (hH : Measurable (Function.uncurry H)) (hF : Measurable F) :
    Measurable (labelKernelNumerator κ H q s f v w F) := by
  have hH' := hH.comp (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(S×IndexedLeaf k) =>
      (p.1.1,p.2)) from measurable_fst.fst.prodMk measurable_snd)
  have hG := (labelTwoMixed_measurable (S:=S) q s (fun i => expBCF 1 f*v i)
    (fun i => expBCF 1 f*w i) F hF).comp
    (show Measurable (fun p : (A×((ℕ→ℝ)×(ℕ→ℝ)))×(Fin r → S×IndexedLeaf k) =>
      (p.1.2,p.2)) from measurable_fst.snd.prodMk measurable_snd)
  exact kernel_replicaMean_measurable (κ.comap Prod.fst measurable_fst) hH' hG

lemma labelKernelNumerator_bound (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) (a : A×((ℕ→ℝ)×(ℕ→ℝ))) :
    |labelKernelNumerator κ H q s f v w F a|≤
      C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖) := by
  apply tiltMean_bound_general (Measure.pi fun _ : Fin r => κ a.1)
    (replicaPotential_measurable hH.of_uncurry_left r)
    (labelRestorationTest_measurable q s f v w hF a.2)
    (mul_nonneg (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  exact labelRestorationTest_bound q s f v w hC hb a.2

lemma labelKernelDenominator_bounds (hH : Measurable (Function.uncurry H))
    {a : A} (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    labelKernelDenominator κ H q s f (a,z) ∈ Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖)) := by
  have hm (g : ℕ→ℝ) : Measurable (fun x : S×IndexedLeaf k => heatLog s 1 f (labelProfileField q g x)) := by
    have hp := (labelProfileField_product_measurable (S:=S) q).of_uncurry_left (x:=g)
    exact (heatLog_continuous s 1 f).measurable.comp hp
  have hb (x : S×IndexedLeaf k) :
      |heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)|≤2*‖f‖ :=
    (abs_add_le _ _).trans ((add_le_add (heatLog_abs_le s 1 f _) (heatLog_abs_le s 1 f _)).trans_eq
      (two_mul ‖f‖).symm)
  have he := tiltMean_exp_bounds (κ a) hH.of_uncurry_left ((hm z.1).add (hm z.2)) hi
    (mul_nonneg (by norm_num) (norm_nonneg f)) hb
  have hw : labelRestorationWeight (S:=S) q s f z = fun x =>
      Real.exp (heatLog s 1 f (labelProfileField q z.1 x)+heatLog s 1 f (labelProfileField q z.2 x)) :=
    funext (labelRestorationWeight_exp q s f z)
  simpa only [labelKernelDenominator,hw,Set.mem_Icc,Pi.add_apply] using he

def labelKernelRestoredRatio (a : A×((ℕ→ℝ)×(ℕ→ℝ))) : ℝ :=
  labelKernelNumerator κ H q s f v w F a / (labelKernelDenominator κ H q s f a)^r

lemma labelKernelRestoredRatio_measurable (hH : Measurable (Function.uncurry H)) (hF : Measurable F) :
    Measurable (labelKernelRestoredRatio κ H q s f v w F) :=
  (labelKernelNumerator_measurable κ H q s f v w F hH hF).div
    ((labelKernelDenominator_measurable κ H q s f hH).pow_const r)

lemma labelKernelRestoredRatio_bound (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) {a : A}
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    |labelKernelRestoredRatio κ H q s f v w F (a,z)|≤
      (C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖)) /
        (Real.exp (-(2*‖f‖)))^r := by
  have hd := (labelKernelDenominator_bounds κ H q s f hH hi z).1
  have hp : 0<labelKernelDenominator κ H q s f (a,z) := (Real.exp_pos _).trans_le hd
  rw [labelKernelRestoredRatio,abs_div,abs_of_pos (pow_pos hp r)]
  have hn := labelKernelNumerator_bound κ H q s f v w F hH hF hC hb (a,z)
  calc
    _ ≤ (C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖)) /
        (labelKernelDenominator κ H q s f (a,z))^r := div_le_div_of_nonneg_right hn (pow_nonneg hp.le _)
    _ ≤ _ := by gcongr

lemma labelKernelRestoredRatio_integrable (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C)
    (P : Measure A) [IsFiniteMeasure P]
    (hi : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) :
    Integrable (labelKernelRestoredRatio κ H q s f v w F)
      (P.prod (countableGaussianLaw.prod countableGaussianLaw)) := by
  apply Integrable.of_bound (labelKernelRestoredRatio_measurable κ H q s f v w F hH hF).aestronglyMeasurable
    ((C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖)) /
        (Real.exp (-(2*‖f‖)))^r)
  have ha := (measurePreserving_fst (μ:=P) (ν:=countableGaussianLaw.prod countableGaussianLaw)).quasiMeasurePreserving.ae hi
  filter_upwards [ha] with a ha
  simpa only [Real.norm_eq_abs] using labelKernelRestoredRatio_bound κ H q s f v w F hH hF hC hb ha a.2

abbrev RestorationRange (f : ℝ →ᵇ ℝ) := Icc (Real.exp (-(2*‖f‖))) (Real.exp (2*‖f‖))

def restorationClip (f : ℝ →ᵇ ℝ) (x : ℝ) : RestorationRange f :=
  ⟨max (Real.exp (-(2*‖f‖))) (min (Real.exp (2*‖f‖)) x),le_max_left _ _,
    max_le (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg f])) (min_le_left _ _)⟩
lemma restorationClip_measurable (f : ℝ →ᵇ ℝ) : Measurable (restorationClip f) :=
  (measurable_const.max (measurable_const.min measurable_id)).subtype_mk
lemma restorationClip_eq (f : ℝ →ᵇ ℝ) {x : ℝ} (hx : x∈RestorationRange f) :
    (restorationClip f x).val=x := by
  dsimp [restorationClip]
  rw [min_eq_right hx.2,max_eq_right hx.1]

def restorationReciprocal (f : ℝ →ᵇ ℝ) (r : ℕ) : C(RestorationRange f,ℝ) :=
  ⟨fun x => (x.val^r)⁻¹, (continuous_subtype_val.pow r).inv₀
    (fun x => (pow_pos ((Real.exp_pos _).trans_le x.prop.1) r).ne')⟩

lemma gaussianAverageBCF_norm_le (s : ℝ≥0) (f : ℝ →ᵇ ℝ) : ‖gaussianAverageBCF s f‖≤‖f‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg f)]
  exact gaussianAverage_abs_le s f

def labelKernelCompactDenominator (a : A×((ℕ→ℝ)×(ℕ→ℝ))) : RestorationRange f :=
  restorationClip f (labelKernelDenominator κ H q s f a)

lemma labelKernelCompactDenominator_measurable (hH : Measurable (Function.uncurry H)) :
    Measurable (labelKernelCompactDenominator κ H q s f) :=
  (restorationClip_measurable f).comp (labelKernelDenominator_measurable κ H q s f hH)

lemma labelKernelCompactDenominator_eq (hH : Measurable (Function.uncurry H))
    {a : A} (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    (labelKernelCompactDenominator κ H q s f (a,z)).val=labelKernelDenominator κ H q s f (a,z) :=
  restorationClip_eq f (labelKernelDenominator_bounds κ H q s f hH hi z)

lemma labelKernelNumerator_uniform_bound (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) (a : A×((ℕ→ℝ)×(ℕ→ℝ))) :
    |labelKernelNumerator κ H q s f v w F a|≤
      C*(∏ i, ‖expBCF 1 f*v i‖)*(∏ i, ‖expBCF 1 f*w i‖) := by
  refine (labelKernelNumerator_bound κ H q s f v w F hH hF hC hb a).trans ?_
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ hC
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => gaussianAverageBCF_norm_le s _)
  · exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => gaussianAverageBCF_norm_le s _)
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)

lemma labelKernel_weighted_integrable (hH : Measurable (Function.uncurry H)) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |F x|≤C) (P : Measure A) [IsFiniteMeasure P]
    (J : C(RestorationRange f,ℝ)) :
    Integrable (fun a => labelKernelNumerator κ H q s f v w F a * J (labelKernelCompactDenominator κ H q s f a))
      (P.prod (countableGaussianLaw.prod countableGaussianLaw)) :=
  weighted_compact_integrable _ _ (labelKernelNumerator_measurable κ H q s f v w F hH hF)
    _ (labelKernelCompactDenominator_measurable κ H q s f hH) _ (by positivity)
    (labelKernelNumerator_uniform_bound κ H q s f v w F hH hF hC hb) J

lemma labelKernel_weighted_eq (hH : Measurable (Function.uncurry H))
    (P : Measure A) [IsFiniteMeasure P]
    (hi : ∀ᵐ a ∂P, Integrable (fun x => Real.exp (H a x)) (κ a)) (J : ℝ→ℝ) :
    (∫ a, labelKernelNumerator κ H q s f v w F a * J (labelKernelCompactDenominator κ H q s f a).val
      ∂P.prod (countableGaussianLaw.prod countableGaussianLaw)) =
    ∫ a, labelKernelNumerator κ H q s f v w F a * J (labelKernelDenominator κ H q s f a)
      ∂P.prod (countableGaussianLaw.prod countableGaussianLaw) := by
  apply integral_congr_ae
  have ha := (measurePreserving_fst (μ:=P) (ν:=countableGaussianLaw.prod countableGaussianLaw)).quasiMeasurePreserving.ae hi
  filter_upwards [ha] with a ha
  rw [labelKernelCompactDenominator_eq κ H q s f hH ha a.2]

end SphericalPerceptronFreeEnergy
end

end OAI
