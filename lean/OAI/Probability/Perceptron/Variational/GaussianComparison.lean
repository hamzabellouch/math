import Mathlib
import OAI.Probability.Perceptron.Pressure.GaussianPressureDerivative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma countableGaussianCovariance_cs {S : Type*} [MeasurableSpace S]
    (v w : ℕ → S → ℝ) (L : S → ℕ) {D E : ℝ} (hD0 : 0≤D) (hE0 : 0≤E)
    (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E) (x y : S) :
    |countableGaussianCovariance v w L x y|≤Real.sqrt D*Real.sqrt E := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin (L x))))
    (fun i => maskedGaussianCoefficient w L i.val x) (fun i => maskedGaussianCoefficient v L i.val y)
  have hm : countableGaussianCovariance v w L x y^2≤E*D := hs.trans
    (mul_le_mul (maskedGaussianCoefficient_sq_bound w L hE (L x) x)
      (maskedGaussianCoefficient_sq_bound v L hD (L x) y) (by positivity) hE0)
  calc
    _ = Real.sqrt (countableGaussianCovariance v w L x y^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (E*D) := Real.sqrt_le_sqrt hm
    _ = _ := by rw [mul_comm E D, Real.sqrt_mul hD0]

lemma countableGaussian_log_comparison {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
    (hL : Measurable L) {A D E : ℝ} (hD0 : 0≤D) (hE0 : 0≤E)
    (hA : ∀ x, |W x|≤A) (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E) :
    |(∫ g, Real.log (tiltPartition μ (fun x => countableGaussianHamiltonian W v L g x+
      countableGaussianField w L g x) 1) ∂countableGaussianLaw)-
    ∫ g, Real.log (tiltPartition μ (countableGaussianHamiltonian W v L g) 1) ∂countableGaussianLaw|≤
      2*(Real.sqrt (2*D+2*E)*Real.sqrt E) := by
  apply gaussianCouplingMean_difference_bound μ hW hv hw hL hA hD hE (by positivity)
  intro a ha x y
  apply countableGaussianCovariance_cs _ _ _ (by positivity) hE0 _ hE
  intro z
  have hb : (∑ i : Fin (L z), (v i.val z+a*w i.val z)^2)≤2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 z
  have ha2 : a^2≤1 := by nlinarith [ha.1,ha.2]
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right ha2 hE0])

variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S] (n : ℕ)

def indexedCoefficientSquare (B : Fin (n+1)→I→ℝ) : ℝ := ∑ i, ∑ l, B l i^2

lemma indexedCoefficientSquare_nonneg (B : Fin (n+1)→I→ℝ) : 0 ≤ indexedCoefficientSquare n B := by
  unfold indexedCoefficientSquare
  positivity

lemma indexedCoefficientSquare_continuous : Continuous (indexedCoefficientSquare (I := I) n) := by
  unfold indexedCoefficientSquare
  fun_prop

omit [MeasurableSpace S] in
lemma indexedGaussianRow_sub (B C : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I) (j : ℕ) (x : S×IndexedLeaf n) :
    indexedGaussianRow n (fun l i => B l i-C l i) V j x =
      indexedGaussianRow n B V j x-indexedGaussianRow n C V j x := by
  unfold indexedGaussianRow finiteGaussianRow
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> ring

omit [MeasurableSpace S] in
lemma indexedGaussianRow_square_total (B : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I)
    {D : ℝ} (hD : ∀ x, (∑ i, V x i^2)≤D) (x : S×IndexedLeaf n) :
    (∑ j : Fin (indexedGaussianRowLength (I := I) n x), indexedGaussianRow n B V j.val x^2)≤
      indexedCoefficientSquare n B*D := by
  apply indexedGaussianRow_norm_le _ _ _ _ (indexedCoefficientSquare_nonneg n B) hD
  intro i
  unfold indexedCoefficientSquare
  exact Finset.single_le_sum (f := fun i => ∑ l, B l i^2) (fun j _ => by positivity) (Finset.mem_univ i)

def indexedGaussianMean (μ : Measure (S×IndexedLeaf n)) (W : S×IndexedLeaf n→ℝ)
    (V : S→EuclideanSpace ℝ I) (B : Fin (n+1)→I→ℝ) : ℝ :=
  ∫ g, Real.log (tiltPartition μ (countableGaussianHamiltonian W (indexedGaussianRow n B V)
    (indexedGaussianRowLength (I := I) n) g) 1) ∂countableGaussianLaw

lemma indexedGaussianMean_comparison (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {A D : ℝ} (hD0 : 0≤D)
    (hA : ∀ x, |W x|≤A) (hD : ∀ x, (∑ i, V x i^2)≤D) (B C : Fin (n+1)→I→ℝ) :
    |indexedGaussianMean n μ W V B-indexedGaussianMean n μ W V C|≤
      2*(Real.sqrt (2*(indexedCoefficientSquare n C*D)+
        2*(indexedCoefficientSquare n (fun l i => B l i-C l i)*D))*
      Real.sqrt (indexedCoefficientSquare n (fun l i => B l i-C l i)*D)) := by
  have hb := countableGaussian_log_comparison μ hW (indexedGaussianRow_measurable n C hV)
    (indexedGaussianRow_measurable n (fun l i => B l i-C l i) hV)
    (indexedGaussianRowLength_measurable n)
    (mul_nonneg (indexedCoefficientSquare_nonneg n C) hD0)
    (mul_nonneg (indexedCoefficientSquare_nonneg n _) hD0)
    hA (indexedGaussianRow_square_total n C V hD) (indexedGaussianRow_square_total n _ V hD)
  convert hb using 1
  unfold indexedGaussianMean
  congr 3
  funext g
  congr 2
  funext x
  simp only [countableGaussianHamiltonian,countableGaussianField,countableGaussianField,
    gaussianPrefixField,indexedGaussianRow_sub]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma indexedGaussianMean_add_const (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {A D : ℝ}
    (hA : ∀ x, |W x|≤A) (hD : ∀ x, (∑ i, V x i^2)≤D)
    (B : Fin (n+1)→I→ℝ) (c : ℝ) :
    indexedGaussianMean n μ (fun x => W x+c) V B = indexedGaussianMean n μ W V B+c := by
  have hrow := indexedGaussianRow_measurable n B hV
  have hlen := indexedGaussianRowLength_measurable (S := S) (I := I) n
  have hb := indexedGaussianRow_square_total n B V hD
  have hi := gaussianLogPartition_integrable μ hW hrow hlen hA hb
  have he : ∀ᵐ g ∂countableGaussianLaw,
      Real.log (tiltPartition μ (countableGaussianHamiltonian (fun x => W x+c) (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g) 1) =
      Real.log (tiltPartition μ (countableGaussianHamiltonian W (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g) 1)+c := by
    filter_upwards [gaussianHamiltonianPartition_pos_ae μ hW hrow hlen hA hb] with g hg
    have hf : tiltPartition μ (countableGaussianHamiltonian (fun x => W x+c) (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g) 1 =
        tiltPartition μ (countableGaussianHamiltonian W (indexedGaussianRow n B V)
          (indexedGaussianRowLength (I := I) n) g) 1*Real.exp c := by
      unfold tiltPartition countableGaussianHamiltonian
      simp only [one_mul]
      simp_rw [show ∀ x, W x+c+countableGaussianField (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g x =
        (W x+countableGaussianField (indexedGaussianRow n B V)
        (indexedGaussianRowLength (I := I) n) g x)+c by intro x; ring,Real.exp_add]
      exact integral_mul_const _ _
    rw [hf,Real.log_mul hg.ne' (Real.exp_ne_zero c),Real.log_exp]
  unfold indexedGaussianMean
  rw [integral_congr_ae he,integral_add hi (integrable_const c),integral_const,probReal_univ,one_smul]

end SphericalPerceptronFreeEnergy
end

end OAI
