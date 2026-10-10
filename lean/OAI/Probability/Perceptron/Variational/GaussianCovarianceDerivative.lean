import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedGaussianCovarianceLaw
import OAI.Probability.Perceptron.Variational.GaussianGibbsContinuity

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

section

lemma countableGaussianCovariance_add_smul {S : Type*}
    (v w z : ℕ → S → ℝ) (L : S → ℕ) (a : ℝ) (x y : S) :
    countableGaussianCovariance (fun i q => v i q+a*w i q) z L x y =
      countableGaussianCovariance v z L x y+a*countableGaussianCovariance w z L x y := by
  have hm (i : ℕ) (q : S) : maskedGaussianCoefficient (fun i q => v i q+a*w i q) L i q =
      maskedGaussianCoefficient v L i q+a*maskedGaussianCoefficient w L i q := by
    unfold maskedGaussianCoefficient
    split_ifs <;> ring
  unfold countableGaussianCovariance gaussianPrefixCovariance
  simp_rw [hm]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma tiltMean_const_mul_general {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (H G : S → ℝ) (a t : ℝ) :
    tiltMean μ H (fun x => a*G x) t = a*tiltMean μ H G t := by
  unfold tiltMean tiltIntegral
  simp_rw [← mul_assoc, mul_comm (Real.exp _) a,mul_assoc,integral_const_mul]
  ring

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x|≤A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2)≤D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2)≤E)
variable {B : ℝ} (hB : 0 ≤ B) (hCB : ∀ x y, |countableGaussianCovariance w w L x y| ≤ B)
include hW hv hw hL hA hD hE hB hCB

lemma gaussianCoupling_covariance_continuous :
    Continuous (fun a => ∫ g,
      tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
        (fun x => countableGaussianCovariance w w L x x) 1 -
      gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
        (fun x => countableGaussianCovariance w w L (x 1) (x 0)) ∂countableGaussianLaw) := by
  let H := countableGaussianHamiltonian W v L
  let Y := countableGaussianField w L
  have hH := countableGaussianHamiltonian_measurable hW hv hL
  have hY := countableGaussianField_measurable hw hL
  have he := countableGaussian_all_coupling_exp_ae μ hW hv hw hL hA hD hE
  have hm := countableGaussianCovariance_measurable hw hw hL
  have hdiag : Measurable (fun x => countableGaussianCovariance w w L x x) :=
    hm.comp (measurable_id.prodMk measurable_id)
  have hpair : Measurable (fun x : Fin 2 → S => countableGaussianCovariance w w L (x 1) (x 0)) :=
    hm.comp (show Measurable (fun x : Fin 2 → S => (x 1,x 0)) from by fun_prop)
  have hi (a : ℝ) : Integrable (fun g => tiltMean μ (fun x => H g x+a*Y g x)
      (fun x => countableGaussianCovariance w w L x x) 1) countableGaussianLaw := by
    apply Integrable.of_bound (kernel_tiltMean_measurable (Kernel.const _ μ)
      (H := fun g x => H g x+a*Y g x) (Y := fun _ x => countableGaussianCovariance w w L x x)
      (hH.add (hY.const_mul a)) (hdiag.comp measurable_snd)).aestronglyMeasurable B
    exact ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,Kernel.const_apply] using tiltMean_bound_general μ
        (H := fun x => H g x+a*Y g x) (hH.of_uncurry_left.add (hY.of_uncurry_left.const_mul a)) hdiag hB (fun x => hCB x x)
  have hj (a : ℝ) : Integrable (fun g => gibbsReplicaMean μ (fun x => H g x+a*Y g x) 2
      (fun x => countableGaussianCovariance w w L (x 1) (x 0))) countableGaussianLaw :=
    kernel_replicaMean_bounded_integrable (Kernel.const _ μ) countableGaussianLaw
      (H := fun g x => H g x+a*Y g x) (G := fun _ x => countableGaussianCovariance w w L (x 1) (x 0))
      (hH.add (hY.const_mul a)) (hpair.comp measurable_snd) hB (fun _ x => hCB _ _)
  change Continuous (fun a => ∫ g, tiltMean μ (fun x => H g x+a*Y g x) _ 1-
    gibbsReplicaMean μ (fun x => H g x+a*Y g x) 2 _ ∂countableGaussianLaw)
  simp_rw [integral_sub (hi _) (hj _)]
  exact (annealedCoupling_tiltMean_continuous countableGaussianLaw μ hH hY hdiag he hB (fun x => hCB x x)).sub
    (annealedCoupling_replicaMean_continuous countableGaussianLaw μ hH hY hpair he hB (fun x => hCB _ _))

theorem gaussianCovariance_right_derivative
    (horth : ∀ x y, countableGaussianCovariance v w L x y=0) :
    HasDerivWithinAt (fun t => ∫ g, Real.log (tiltPartition μ (fun x =>
      countableGaussianHamiltonian W v L g x+Real.sqrt t*countableGaussianField w L g x) 1) ∂countableGaussianLaw)
      ((∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
          (fun x => countableGaussianCovariance w w L x x) 1 -
        gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
          (fun x => countableGaussianCovariance w w L (x 1) (x 0)) ∂countableGaussianLaw)/2) (Ici 0) 0 := by
  let M := fun a => ∫ g, Real.log (tiltPartition μ (fun x =>
    countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 1) ∂countableGaussianLaw
  let C := fun a => ∫ g,
    tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
      (fun x => countableGaussianCovariance w w L x x) 1 -
    gibbsReplicaMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x) 2
      (fun x => countableGaussianCovariance w w L (x 1) (x 0)) ∂countableGaussianLaw
  have hd (a : ℝ) : HasDerivAt M (a*C a) a := by
    have hh := gaussianCouplingMean_derivative_covariance μ hW hv hw hL hA hD hE a
    simp_rw [countableGaussianCovariance_add_smul,horth,zero_add,
      tiltMean_const_mul_general,gibbsReplicaMean,tiltMean_const_mul_general,← mul_sub,integral_const_mul] at hh
    exact hh
  have hc : Continuous C := gaussianCoupling_covariance_continuous μ hW hv hw hL hA hD hE hB hCB
  simpa only [M,C,zero_mul,add_zero] using sqrt_coupling_right_derivative hd hc

end
variable {I : Type} [Fintype I] [DecidableEq I] {S : Type} [MeasurableSpace S]
variable (n : ℕ)

def duplicateFeature (V : S→EuclideanSpace ℝ I) (s : S) : EuclideanSpace ℝ (I ⊕ I) :=
  WithLp.toLp 2 (Sum.elim (fun i => V s i) (fun i => V s i))

def leftCoefficients (B : Fin (n+1)→I→ℝ) (l : Fin (n+1)) : I ⊕ I→ℝ :=
  Sum.elim (B l) (fun _ => 0)

def rightCoefficients (C : Fin (n+1)→I→ℝ) (l : Fin (n+1)) : I ⊕ I→ℝ :=
  Sum.elim (fun _ => 0) (C l)

omit [DecidableEq I] in
lemma duplicateFeature_measurable {V : S→EuclideanSpace ℝ I} (hV : Measurable V) :
    Measurable (duplicateFeature V) := by
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply Measurable.of_eval
  intro i
  cases i with
  | inl i => exact (EuclideanSpace.proj i).measurable.comp hV
  | inr i => exact (EuclideanSpace.proj i).measurable.comp hV

omit [DecidableEq I] [MeasurableSpace S] in
lemma duplicateFeature_square (V : S→EuclideanSpace ℝ I) (s : S) :
    (∑ i, duplicateFeature V s i^2) = 2*∑ i, V s i^2 := by
  rw [Fintype.sum_sum_type]
  simp only [duplicateFeature,Sum.elim_inl,Sum.elim_inr]
  ring

omit [DecidableEq I] [MeasurableSpace S] in
lemma indexedGaussianRow_orthogonal (B C : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf n) :
    countableGaussianCovariance (indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V))
      (indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) x y=0 := by
  rw [indexedGaussianRow_covariance,Fintype.sum_sum_type]
  simp [leftCoefficients,rightCoefficients]

omit [DecidableEq I] [MeasurableSpace S] in
lemma indexedGaussianRow_add_smul (B C : Fin (n+1)→I→ℝ) (V : S→EuclideanSpace ℝ I)
    (a : ℝ) (j : ℕ) (x : S×IndexedLeaf n) :
    indexedGaussianRow n (fun l i => B l i+a*C l i) V j x =
      indexedGaussianRow n B V j x+a*indexedGaussianRow n C V j x := by
  unfold indexedGaussianRow finiteGaussianRow
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> ring

omit [DecidableEq I] [MeasurableSpace S] in
lemma indexedHamiltonian_independent_addition (W : S×IndexedLeaf n→ℝ) (V : S→EuclideanSpace ℝ I)
    (B C : Fin (n+1)→I→ℝ) (a : ℝ) (g : ℕ→ℝ) (x : S×IndexedLeaf n) :
    countableGaussianHamiltonian W
      (indexedGaussianRow n (fun l => Sum.elim (B l) (fun i => a*C l i)) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) g x =
    countableGaussianHamiltonian W
      (indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) g x +
    a*countableGaussianField (indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V))
      (indexedGaussianRowLength (I := I ⊕ I) n) g x := by
  have he : (fun l => Sum.elim (B l) (fun i => a*C l i)) =
      fun l i => leftCoefficients n B l i+a*rightCoefficients n C l i := by
    funext l i
    cases i <;> simp [leftCoefficients,rightCoefficients]
  rw [he]
  unfold countableGaussianHamiltonian
  have hr : indexedGaussianRow n (fun l i => leftCoefficients n B l i+a*rightCoefficients n C l i) (duplicateFeature V) =
      fun j x => indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V) j x+
        a*indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V) j x := by
    funext j x
    exact indexedGaussianRow_add_smul n _ _ _ _ _ _
  rw [hr,countableGaussianField_add,countableGaussianField_smul]
  ring

theorem indexedGaussianMean_right_derivative (μ : Measure (S×IndexedLeaf n)) [IsProbabilityMeasure μ]
    {W : S×IndexedLeaf n→ℝ} {V : S→EuclideanSpace ℝ I}
    (hW : Measurable W) (hV : Measurable V) {A D : ℝ} (hD0 : 0 ≤ D)
    (hA : ∀ x, |W x| ≤ A) (hD : ∀ x, (∑ i, V x i^2) ≤ D)
    (B C : Fin (n+1)→I→ℝ) (Q : ℝ→Fin (n+1)→I→ℝ)
    (hQ : ∀ t, 0 ≤ t → ∀ l i, Q t l i^2=B l i^2+t*C l i^2) :
    let v := indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V)
    let w := indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V)
    let L := indexedGaussianRowLength (I := I ⊕ I) (S := S) n
    HasDerivWithinAt (fun t => indexedGaussianMean n μ W V (Q t))
      ((∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
          (fun x => countableGaussianCovariance w w L x x) 1 -
        gibbsReplicaMean μ (countableGaussianHamiltonian W v L g) 2
          (fun x => countableGaussianCovariance w w L (x 1) (x 0)) ∂countableGaussianLaw)/2) (Ici 0) 0 := by
  let v := indexedGaussianRow n (leftCoefficients n B) (duplicateFeature V)
  let w := indexedGaussianRow n (rightCoefficients n C) (duplicateFeature V)
  let L := indexedGaussianRowLength (I := I ⊕ I) (S := S) n
  let E := indexedCoefficientSquare n (rightCoefficients n C)*(2*D)
  have hE0 : 0 ≤ E := mul_nonneg (indexedCoefficientSquare_nonneg n _) (by positivity)
  have hDV (x : S) : (∑ i, duplicateFeature V x i^2) ≤ 2*D := by
    rw [duplicateFeature_square]
    exact mul_le_mul_of_nonneg_left (hD x) (by norm_num)
  have hv := indexedGaussianRow_measurable n (leftCoefficients n B) (duplicateFeature_measurable hV)
  have hw := indexedGaussianRow_measurable n (rightCoefficients n C) (duplicateFeature_measurable hV)
  have hEE : ∀ x, (∑ j : Fin (L x), w j.val x^2) ≤ E := indexedGaussianRow_square_total n _ _ hDV
  have hCB (x y) : |countableGaussianCovariance w w L x y| ≤ E := by
    have hh := gaussianPrefixCovariance_bound w w L hEE hEE (L x) x y
    simpa only [countableGaussianCovariance,add_self_div_two] using hh
  have hd := gaussianCovariance_right_derivative μ hW hv hw
    (indexedGaussianRowLength_measurable n) hA
    (indexedGaussianRow_square_total n (leftCoefficients n B) _ hDV)
    hEE hE0 hCB (indexedGaussianRow_orthogonal n B C V)
  apply hd.congr_of_mem _ (by simp)
  intro t ht
  have he := indexedGaussianMean_covariance_addition n μ hW hV B
    (fun l i => Real.sqrt t*C l i) (Q t) (fun l i => by rw [mul_pow,Real.sq_sqrt ht]; exact hQ t ht l i)
  rw [he]
  unfold indexedGaussianMean
  apply integral_congr_ae
  filter_upwards [] with g
  congr 2
  funext x
  exact indexedHamiltonian_independent_addition n W V B C (Real.sqrt t) g x

end SphericalPerceptronFreeEnergy
end

end OAI
