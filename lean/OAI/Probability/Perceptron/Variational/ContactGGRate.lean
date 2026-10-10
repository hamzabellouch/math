import Mathlib
import OAI.Probability.Perceptron.Variational.QuantitativeGG

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical

lemma contact_gg_rate_identity {x c C : ℝ} (hx : 0<x) (hC : 0≤C) :
    (Real.sqrt (2*c)/Real.sqrt (1/x)+
      (c*x^(-(1:ℝ)/4)+4*Real.sqrt (C/x)/(x^(-(1:ℝ)/4)))/(1/x))/(x^((7:ℝ)/8)) =
      Real.sqrt (2*c)*x^(-(3:ℝ)/8)+(c+4*Real.sqrt C)*x^(-(1:ℝ)/8) := by
  rw [Real.sqrt_div zero_le_one,Real.sqrt_one,Real.sqrt_div hC,Real.sqrt_eq_rpow x]
  simp only [div_eq_mul_inv]
  ring_nf
  simp only [← Real.rpow_neg hx.le]
  norm_num
  have he1 : x^(-(1:ℝ)/4)*x*x^(-(7:ℝ)/8)=x^(-(1:ℝ)/8) := by
    calc
      _ = x^((-(1:ℝ)/4)+1+(-(7:ℝ)/8)) := by
        rw [Real.rpow_add hx,Real.rpow_add hx,Real.rpow_one]
      _ = _ := by congr 1; norm_num
  have he2 : x^((1:ℝ)/2)*x^(-(7:ℝ)/8)=x^(-(3:ℝ)/8) := by
    rw [← Real.rpow_add hx]
    congr 1
    norm_num
  have he3 : x^(-(1:ℝ)/2)*x^((1:ℝ)/4)*x*x^(-(7:ℝ)/8)=x^(-(1:ℝ)/8) := by
    calc
      _ = x^((-(1:ℝ)/2)+(1:ℝ)/4+1+(-(7:ℝ)/8)) := by
        rw [Real.rpow_add hx,Real.rpow_add hx,Real.rpow_add hx,Real.rpow_one]
      _ = _ := by congr 1; norm_num
  norm_num at he1 he2 he3
  linear_combination c*he1 + Real.sqrt c*Real.sqrt 2*he2 + 4*Real.sqrt C*he3

lemma contact_gg_rate_bound {x c C B θ u : ℝ} (hx : 0<x) (hc : 0≤c) (hC : 0≤C)
    (hB : 0≤B) (hθ : 0<θ) (hu : 1≤u) :
    (B*(Real.sqrt (2*c)/Real.sqrt (1/x)+
      (c*x^(-(1:ℝ)/4)+4*Real.sqrt (C/x)/(x^(-(1:ℝ)/4)))/(1/x)))/
      (x^((7:ℝ)/8)*θ^2*u) ≤
      B/(θ^2)*(Real.sqrt (2*c)*x^(-(3:ℝ)/8)+(c+4*Real.sqrt C)*x^(-(1:ℝ)/8)) := by
  let E := Real.sqrt (2*c)/Real.sqrt (1/x)+
    (c*x^(-(1:ℝ)/4)+4*Real.sqrt (C/x)/(x^(-(1:ℝ)/4)))/(1/x)
  have hE : 0≤E := by dsimp [E]; positivity
  have hA : 0<x^((7:ℝ)/8)*θ^2 := by positivity
  calc
    _ ≤ B*E/(x^((7:ℝ)/8)*θ^2) := div_le_div_of_nonneg_left (mul_nonneg hB hE)
      hA (le_mul_of_one_le_right hA.le hu)
    _ = B/(θ^2)*(E/x^((7:ℝ)/8)) := by ring
    _ = _ := by rw [contact_gg_rate_identity hx hC]

lemma perturbationAmplitude_product (n : ℕ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    perturbationAmplitude (n+1) (fun _ => 1) j*perturbationAmplitude (n+1) u j =
      (n+1:ℕ)^((7:ℝ)/8)*((2:ℝ)^(-((j.val+1:ℕ):ℤ)))^2*u j := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  simp only [perturbationAmplitude,perturbationScale,Real.sqrt_eq_rpow,mul_one]
  have he : ((1:ℝ)/2+(-(1:ℝ)/16))+((1:ℝ)/2+(-(1:ℝ)/16))=7/8 := by norm_num
  rw [← he,Real.rpow_add hn,Real.rpow_add hn]
  ring

lemma contact_gg_rate_tendsto (c C B θ : ℝ) :
    Tendsto (fun x : ℝ => B/(θ^2)*(Real.sqrt (2*c)*x^(-(3:ℝ)/8)+
      (c+4*Real.sqrt C)*x^(-(1:ℝ)/8))) atTop (𝓝 0) := by
  have h3 := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/8)
  have h1 := tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/8)
  convert ((h3.const_mul (Real.sqrt (2*c))).add (h1.const_mul (c+4*Real.sqrt C))).const_mul (B/(θ^2)) using 1 <;> norm_num

lemma source_contact_joint_gg_rate (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {H T c a s : ℝ} (hH : 0 ≤ H) (hhH : h 0 ≤ H) (ht : (t:ℝ) ≤ T) (hs : 0<s)
    (hu : ∀ l, u l ∈ Icc 1 2)
    (hup : ∀ l, (u+Pi.single j s : Fin (n+1) → ℝ) l ∈ Icc 1 2) (hum : ∀ l, (u+Pi.single j (-s) : Fin (n+1) → ℝ) l ∈ Icc 1 2)
    (hmin : IsLocalMin (fun r => c*(r-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j r) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) 0)
    (hp : c*(0-a)^2-(∫ b, sourceKernelPressure n k f p d u h b
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤ c*(s-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j s) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (hm : c*(0-a)^2-(∫ b, sourceKernelPressure n k f p d u h b
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤ c*(-s-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j (-s)) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (r : ℕ) (i : Fin r) {G : (Fin r → NormalizedSpin (n+1)×IndexedLeaf k) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B)
    (hc0 : 0≤c) (hsdef : s=(n+1:ℕ)^(-(1:ℝ)/4)) :
    |kernelGGDefect (sourceFullSpinLeafKernel n k)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
      (sourceCouplingHamiltonian n k f p d h u) (sourceJointMonomial p d j)
      (((k:ℝ)/(k+1:ℕ))^(d j)) r i G| ≤
      B/(((2:ℝ)^(-((j.val+1:ℕ):ℤ)))^2)*
        (Real.sqrt (2*c)*(n+1:ℕ)^(-(3:ℝ)/8)+
          (c+4*Real.sqrt (enrichedVarianceConstant k z f H T))*(n+1:ℕ)^(-(1:ℝ)/8)) := by
  have he := source_contact_joint_gg_error n k f p d h hh0 hh u j z hz hz0 hz1 t
    hH hhH ht hs hu hup hum hmin hp hm r i hG hB hGB
  rw [hsdef,perturbationAmplitude_product] at he
  have hT : 0≤T := t.coe_nonneg.trans ht
  have hC : 0≤enrichedVarianceConstant k z f H T := by
    unfold enrichedVarianceConstant
    positivity
  have hrate := contact_gg_rate_bound (by positivity : (0:ℝ)<(n+1:ℕ)) hc0 hC hB
    (by positivity : (0:ℝ)<(2:ℝ)^(-((j.val+1:ℕ):ℤ))) (hu j).1
  exact he.trans hrate

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (H : A → S → ℝ)

private def gibbsKernelDensity (a : A) (x : S) : ℝ≥0∞ :=
  if Integrable (fun y => Real.exp (H a y)) (κ a) then
    (ENNReal.ofReal (tiltPartition (κ a) (H a) 1))⁻¹*ENNReal.ofReal (Real.exp (H a x)) else 1

private lemma gibbsKernelDensity_measurable (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (gibbsKernelDensity κ H)) := by
  apply Measurable.ite
  · exact (measurableSet_kernel_integrable (κ := κ) (f := fun a x => Real.exp (H a x)) hH.exp.stronglyMeasurable).preimage measurable_fst
  · exact (((kernel_tiltPartition_measurable κ hH).ennreal_ofReal.inv).comp measurable_fst).mul hH.exp.ennreal_ofReal
  · exact measurable_const

def gibbsProbabilityKernel : Kernel A S := Kernel.withDensity κ (gibbsKernelDensity κ H)

lemma gibbsProbabilityKernel_of_integrable (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) :
    gibbsProbabilityKernel κ H a = tiltLaw (κ a) (H a) 1 := by
  rw [gibbsProbabilityKernel,Kernel.withDensity_apply _ (gibbsKernelDensity_measurable κ H hH)]
  change (κ a).withDensity (fun x => if Integrable (fun y => Real.exp (H a y)) (κ a)
    then (ENNReal.ofReal (tiltPartition (κ a) (H a) 1))⁻¹*ENNReal.ofReal (Real.exp (H a x)) else 1) = _
  simp only [ite_eq_left hi,tiltLaw,one_mul]
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (H a x))) := hH.of_uncurry_left.exp.ennreal_ofReal
  exact withDensity_smul _ hm

lemma gibbsProbabilityKernel_of_not_integrable (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : ¬Integrable (fun x => Real.exp (H a x)) (κ a)) :
    gibbsProbabilityKernel κ H a = κ a := by
  rw [gibbsProbabilityKernel,Kernel.withDensity_apply _ (gibbsKernelDensity_measurable κ H hH)]
  change (κ a).withDensity (fun x => if Integrable (fun y => Real.exp (H a y)) (κ a)
    then (ENNReal.ofReal (tiltPartition (κ a) (H a) 1))⁻¹*ENNReal.ofReal (Real.exp (H a x)) else 1) = _
  simp only [ite_eq_right hi]
  exact withDensity_one

lemma gibbsProbabilityKernel_markov (hH : Measurable (Function.uncurry H)) :
    IsMarkovKernel (gibbsProbabilityKernel κ H) := by
  constructor
  intro a
  by_cases hi : Integrable (fun x => Real.exp (H a x)) (κ a)
  · rw [gibbsProbabilityKernel_of_integrable κ H hH a hi]
    exact tilt_law_probability_of_integrable (κ a) (by simpa only [one_mul] using hi)
  · rw [gibbsProbabilityKernel_of_not_integrable κ H hH a hi]
    infer_instance

lemma gibbsProbabilityKernel_replica_integral (hH : Measurable (Function.uncurry H)) (a : A)
    (hi : Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ) (G : (Fin r → S) → ℝ) :
    (∫ x, G x ∂Measure.pi (fun _ : Fin r => gibbsProbabilityKernel κ H a)) =
      gibbsReplicaMean (κ a) (H a) r G := by
  rw [gibbsProbabilityKernel_of_integrable κ H hH a hi]
  exact (gibbsReplicaMean_integral_of_integrable _ hH.of_uncurry_left hi r G).symm

lemma gibbsProbabilityKernel_congr_apply {B : Type*} [MeasurableSpace B]
    (η : Kernel B S) [IsMarkovKernel η] (G : B→S→ℝ)
    (hH : Measurable (Function.uncurry H)) (hG : Measurable (Function.uncurry G))
    (a : A) (b : B) (he : κ a=η b) (hE : H a=G b) :
    gibbsProbabilityKernel κ H a=gibbsProbabilityKernel η G b := by
  by_cases hi : Integrable (fun x => Real.exp (H a x)) (κ a)
  · have hi' : Integrable (fun x => Real.exp (G b x)) (η b) := by simpa [←he,←hE] using hi
    rw [gibbsProbabilityKernel_of_integrable κ H hH a hi,
      gibbsProbabilityKernel_of_integrable η G hG b hi',he,hE]
  · have hi' : ¬Integrable (fun x => Real.exp (G b x)) (η b) := by simpa [←he,←hE] using hi
    rw [gibbsProbabilityKernel_of_not_integrable κ H hH a hi,
      gibbsProbabilityKernel_of_not_integrable η G hG b hi',he]

end SphericalPerceptronFreeEnergy

end

end OAI
