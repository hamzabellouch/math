import Mathlib
import OAI.Probability.SKGap.Terminal.SpinEnergy
import OAI.Probability.SKGap.Entropy.GaussianExponentialLinear

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

def edgeCoefficient {n : ℕ} (r : ℝ) (x : Spin n) : Edge n→ℝ :=
  fun e=>sqrt r*spinValue (x e.1.1)*spinValue (x e.1.2)

def gaussianSpinPartition (n : ℕ) (r : ℝ) (g : Disorder n) : ℝ :=
  ∑ x : Spin n,exp (∑ e,edgeCoefficient r x e*g e)

lemma gaussianSpinPartition_eq_partition {n : ℕ} (r : ℝ) (g : Disorder n) :
    gaussianSpinPartition n r g=partition (fun e=>sqrt r*g e) 0 := by
  unfold gaussianSpinPartition partition weight
  apply Finset.sum_congr rfl;intro x _
  rw [edge_energy_formula]
  congr 1
  apply Finset.sum_congr rfl;intro e _
  unfold edgeCoefficient;ring

lemma edgeCoefficient_sq_sum {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (x : Spin n) :
    (∑ e,edgeCoefficient r x e^2)= r*(Fintype.card (Edge n):ℝ) := by
  simp only [edgeCoefficient,mul_pow,spinValue_sq,sq_sqrt hr,mul_one,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

lemma edgeCoefficient_add_sq {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (x y : Spin n) (e : Edge n) :
    (edgeCoefficient r x e+edgeCoefficient r y e)^2=
      2*r+2*r*spinValue (spinMul x y e.1.1)*spinValue (spinMul x y e.1.2) := by
  have hc : edgeCoefficient r x e*edgeCoefficient r y e=
      r*spinValue (spinMul x y e.1.1)*spinValue (spinMul x y e.1.2) := by
    rw [spinValue_mul,spinValue_mul]
    unfold edgeCoefficient
    calc
      _ = (sqrt r)^2*spinValue (x e.1.1)*spinValue (y e.1.1)*spinValue (x e.1.2)*spinValue (y e.1.2) := by ring
      _ = _ := by rw [sq_sqrt hr];ring
  have hs (z : Spin n) : edgeCoefficient r z e^2=r := by
    simp only [edgeCoefficient,mul_pow,spinValue_sq,sq_sqrt hr,mul_one]
  nlinarith only [hc,hs x,hs y]

lemma edgeCoefficient_add_sq_sum {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (x y : Spin n) :
    (∑ e,(edgeCoefficient r x e+edgeCoefficient r y e)^2)=
      2*r*(Fintype.card (Edge n):ℝ)+r*((∑ i,spinValue (spinMul x y i))^2-(n:ℝ)) := by
  simp_rw [edgeCoefficient_add_sq hr x y]
  rw [Finset.sum_add_distrib]
  have he := edge_symmetric_sum (fun i=>spinValue (spinMul x y i))
  simp only [spinValue_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at he
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hsum : (∑ e : Edge n,2*r*spinValue (spinMul x y e.1.1)*spinValue (spinMul x y e.1.2))=
      r*(2*∑ e : Edge n,spinValue (spinMul x y e.1.1)*spinValue (spinMul x y e.1.2)) := by
    simp only [Finset.mul_sum];apply Finset.sum_congr rfl;intro e _;ring
  rw [hsum,he];ring

lemma gaussianSpinPartition_integrable (n : ℕ) (r : ℝ) :
    Integrable (gaussianSpinPartition n r) (gaussianCoordinates (Edge n)) :=
  integrable_finsetSum _ (fun x _=>linear_gaussian_exp_integrable (edgeCoefficient r x))

lemma gaussianSpinPartition_integral {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (∫ g,gaussianSpinPartition n r g ∂gaussianCoordinates (Edge n))=
      (Fintype.card (Spin n):ℝ)*exp (r*(Fintype.card (Edge n):ℝ)/2) := by
  unfold gaussianSpinPartition
  rw [integral_finsetSum _ (fun x _=>linear_gaussian_exp_integrable (edgeCoefficient r x))]
  simp only [linear_gaussian_exp_integral,edgeCoefficient_sq_sum hr,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma gaussianSpinPartition_square (n : ℕ) (r : ℝ) (g : Disorder n) :
    (gaussianSpinPartition n r g)^2=
      ∑ x : Spin n,∑ y : Spin n,exp (∑ e,(edgeCoefficient r x e+edgeCoefficient r y e)*g e) := by
  unfold gaussianSpinPartition
  rw [sq,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl;intro x _
  apply Finset.sum_congr rfl;intro y _
  rw [← exp_add]
  congr 1
  simp only [add_mul,Finset.sum_add_distrib]

lemma gaussianSpinPartition_square_integrable (n : ℕ) (r : ℝ) :
    Integrable (fun g=>(gaussianSpinPartition n r g)^2) (gaussianCoordinates (Edge n)) := by
  simp_rw [gaussianSpinPartition_square]
  exact integrable_finsetSum _ (fun x _=>integrable_finsetSum _
    (fun y _=>linear_gaussian_exp_integrable (fun e=>edgeCoefficient r x e+edgeCoefficient r y e)))

lemma gaussianSpinPartition_square_integral {n : ℕ} {r : ℝ} (hr : 0 ≤ r) :
    (∫ g,(gaussianSpinPartition n r g)^2 ∂gaussianCoordinates (Edge n))=
      (Fintype.card (Spin n):ℝ)*exp (r*(Fintype.card (Edge n):ℝ)-r*(n:ℝ)/2)*
      ∑ x : Spin n,exp (r/2*(∑ i,spinValue (x i))^2) := by
  simp_rw [gaussianSpinPartition_square]
  rw [integral_finsetSum _ (fun x _=>integrable_finsetSum _
    (fun y _=>linear_gaussian_exp_integrable (fun e=>edgeCoefficient r x e+edgeCoefficient r y e)))]
  simp_rw [integral_finsetSum _ (fun y _=>linear_gaussian_exp_integrable _),
    linear_gaussian_exp_integral,edgeCoefficient_add_sq_sum hr]
  have he (x y : Spin n) : exp ((2*r*(Fintype.card (Edge n):ℝ)+
      r*((∑ i,spinValue (spinMul x y i))^2-(n:ℝ)))/2)=
      exp (r*(Fintype.card (Edge n):ℝ)-r*(n:ℝ)/2)*exp (r/2*(∑ i,spinValue (spinMul x y i))^2) := by
    rw [← exp_add];congr 1;ring
  simp_rw [he,← Finset.mul_sum]
  have hs (x : Spin n) :
      (∑ y : Spin n,exp (r/2*(∑ i,spinValue (spinMul x y i))^2))=
      ∑ y : Spin n,exp (r/2*(∑ i,spinValue (y i))^2) :=
    sum_spinMul x (fun y=>exp (r/2*(∑ i,spinValue (y i))^2))
  simp_rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc]
  ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set

lemma second_moment_positive_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω→ℝ)
    (hZ : Measurable Z) (hi : Integrable Z μ) (hi2 : Integrable (fun x=>Z x^2) μ)
    {M B : ℝ} (hM : 0 < M) (hB : 0 < B) (hmean : (∫ x,Z x ∂μ)=M)
    (hmoment : (∫ x,Z x^2 ∂μ) ≤ B*M^2) :
    1/(4*B) ≤ μ.real {x | M/2 ≤ Z x} := by
  let S : Set Ω := {x | M/2 ≤ Z x}
  have hS : MeasurableSet S := measurableSet_le measurable_const hZ
  have hden : 0 < 4*B*M := by positivity
  have hpoint : ∀ x,Z x ≤ M/2+B*M*S.indicator (fun _=>1) x+Z x^2/(4*B*M) := by
    intro x
    by_cases hx : x∈S
    · rw [indicator_of_mem hx]
      apply (mul_le_mul_iff_right₀ hden).mp
      nlinarith [sq_nonneg (Z x-2*B*M),div_mul_cancel₀ (Z x^2) hden.ne',
        mul_nonneg hB.le (sq_nonneg M)]
    · rw [indicator_of_notMem hx]
      change ¬ M/2 ≤ Z x at hx
      have hn : 0 ≤ Z x^2/(4*B*M) := div_nonneg (sq_nonneg _) hden.le
      nlinarith [not_le.mp hx]
  have hiS : Integrable (S.indicator (fun _=> (1:ℝ))) μ := (integrable_const _).indicator hS
  have hiA : Integrable (fun x=>M/2+B*M*S.indicator (fun _=>(1:ℝ)) x) μ :=
    (integrable_const (M/2)).add (hiS.const_mul (B*M))
  have hiB : Integrable (fun x=>B*M*S.indicator (fun _=>(1:ℝ)) x) μ := hiS.const_mul _
  have hiC : Integrable (fun x=>Z x^2/(4*B*M)) μ := hi2.div_const _
  have hh := integral_mono hi (hiA.add hiC) hpoint
  change (∫ x,Z x ∂μ) ≤ ∫ x,M/2+B*M*S.indicator (fun _=>(1:ℝ)) x+Z x^2/(4*B*M) ∂μ at hh
  rw [hmean,integral_add hiA hiC,integral_add (integrable_const (M/2)) hiB,
    integral_const,integral_const_mul,integral_div,integral_indicator hS,
    setIntegral_const] at hh
  simp only [probReal_univ,smul_eq_mul,mul_one,one_mul] at hh
  have hterm : (∫ x,Z x^2 ∂μ)/(4*B*M) ≤ M/4 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hmoment]
  have hh' : 1 ≤ 4*B*μ.real S := by
    have h : M/4 ≤ B*M*μ.real S := by linarith only [hh,hterm]
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [h]
  exact (div_le_iff₀ (show 0 < 4*B by positivity)).mpr (by nlinarith only [hh'])
end SKGap
end
end

end OAI
