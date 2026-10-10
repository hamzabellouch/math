import Mathlib
import OAI.Probability.Perceptron.Variational.GibbsRestoration
import OAI.Probability.Perceptron.Variational.RestorationMoments
import OAI.Probability.Perceptron.Variational.TiltedPathDiagonal
import OAI.Probability.Perceptron.Variational.CountableMarkedDiagonal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S : Type} [MeasurableSpace S] {k : ℕ}

def replicaFrontLift {r : ℕ} (F : (Fin r→S)→ℝ) : (j : ℕ)→(Fin (r+j)→S)→ℝ
  | 0 => F
  | j+1 => fun x => replicaFrontLift F j (fun i => x i.succ)

lemma replicaFrontLift_measurable {r : ℕ} {F : (Fin r→S)→ℝ}
    (hF : Measurable F) (j : ℕ) : Measurable (replicaFrontLift F j) := by
  induction j with
  | zero => exact hF
  | succ j hj => exact hj.comp (Measurable.of_eval fun coordinate => measurable_pi_apply coordinate.succ)

omit [MeasurableSpace S] in
lemma replicaFrontLift_bound {r : ℕ} {F : (Fin r→S)→ℝ} {C : ℝ}
    (hF : ∀ x, |F x|≤C) (j : ℕ) (x : Fin (r+j)→S) : |replicaFrontLift F j x|≤C := by
  induction j with
  | zero => exact hF x
  | succ j hj => exact hj _

def labelRestoredFunctions {r : ℕ} (f : ℝ →ᵇ ℝ) (v : Fin r→ℝ →ᵇ ℝ) :
    (j : ℕ)→Fin (r+j)→ℝ →ᵇ ℝ
  | 0 => fun i => expBCF 1 f*v i
  | j+1 => Fin.cons (expBCF 1 f) (labelRestoredFunctions f v j)

def labelRestorationWeight (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : S×IndexedLeaf k) : ℝ :=
  gaussianAverageBCF s (expBCF 1 f) (labelProfileField q z.1 x) *
    gaussianAverageBCF s (expBCF 1 f) (labelProfileField q z.2 x)

def labelRestorationTest {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) (F : (Fin r→S×IndexedLeaf k)→ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : Fin r→S×IndexedLeaf k) : ℝ :=
  F x * labelMixedValue q s (fun i => expBCF 1 f*v i) z.1 x *
    labelMixedValue q s (fun i => expBCF 1 f*w i) z.2 x

omit [MeasurableSpace S] in
lemma labelRestorationTest_replica {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) (F : (Fin r→S×IndexedLeaf k)→ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (j : ℕ) (x : Fin (r+j)→S×IndexedLeaf k) :
    restorationReplicaTest r (labelRestorationWeight q s f z) (labelRestorationTest q s f v w F z) j x =
      replicaFrontLift F j x * labelMixedValue q s (labelRestoredFunctions f v j) z.1 x *
        labelMixedValue q s (labelRestoredFunctions f w j) z.2 x := by
  induction j with
  | zero => rfl
  | succ j hj =>
    change labelRestorationWeight q s f z (x 0) *
      restorationReplicaTest r (labelRestorationWeight q s f z) (labelRestorationTest q s f v w F z) j (fun i => x i.succ) = _
    rw [hj]
    simp only [Nat.add_succ,replicaFrontLift,labelMixedValue,labelRestoredFunctions,Fin.prod_univ_succ,
      Fin.cons_zero,Fin.cons_succ,labelRestorationWeight]
    ring

lemma labelRestorationWeight_measurable (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) : Measurable (labelRestorationWeight (S:=S) q s f z) := by
  have hm (a : ℕ→ℝ) : Measurable (fun x : S×IndexedLeaf k =>
      gaussianAverageBCF s (expBCF 1 f) (labelProfileField q a x)) :=
    by
      have hp : Measurable (fun x : S×IndexedLeaf k => (a,x)) := measurable_const.prodMk measurable_id
      have hfield := (labelProfileField_product_measurable (S:=S) q).comp hp
      exact (gaussianAverageBCF s (expBCF 1 f)).measurable.comp hfield
  exact (hm z.1).mul (hm z.2)

omit [MeasurableSpace S] in
lemma labelRestorationWeight_bound (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : S×IndexedLeaf k) :
    |labelRestorationWeight q s f z x|≤‖gaussianAverageBCF s (expBCF 1 f)‖^2 := by
  rw [labelRestorationWeight,abs_mul,pow_two]
  exact mul_le_mul ((gaussianAverageBCF s (expBCF 1 f)).norm_coe_le_norm _)
    ((gaussianAverageBCF s (expBCF 1 f)).norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _)

lemma labelRestorationTest_measurable {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) {F : (Fin r→S×IndexedLeaf k)→ℝ} (hF : Measurable F)
    (z : (ℕ→ℝ)×(ℕ→ℝ)) : Measurable (labelRestorationTest q s f v w F z) :=
  (labelTwoMixed_measurable q s (fun i => expBCF 1 f*v i) (fun i => expBCF 1 f*w i) F hF).comp
    (measurable_const.prodMk measurable_id)

lemma labelRestorationTest_bound {r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) {F : (Fin r→S×IndexedLeaf k)→ℝ} {C : ℝ} (hC : 0≤C)
    (hF : ∀ x, |F x|≤C) (z : (ℕ→ℝ)×(ℕ→ℝ)) (x : Fin r→S×IndexedLeaf k) :
    |labelRestorationTest q s f v w F z x|≤
      C*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*v i)‖)*(∏ i, ‖gaussianAverageBCF s (expBCF 1 f*w i)‖) := by
  simp only [labelRestorationTest,abs_mul]
  exact mul_le_mul (mul_le_mul (hF _) (labelMixedValue_bound q s _ _ _) (abs_nonneg _) hC)
    (labelMixedValue_bound q s _ _ _) (abs_nonneg _)
    (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))

lemma labelRestoration_moments {r : ℕ} (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (h1 : q (Fin.last k)≤1) (f : ℝ →ᵇ ℝ) (v w : Fin r→ℝ →ᵇ ℝ)
    (μ : Measure (S×IndexedLeaf k)) [IsProbabilityMeasure μ] (H : (S×IndexedLeaf k)→ℝ)
    (hH : Measurable H) (hi : Integrable (fun x => Real.exp (H x)) μ)
    (F : (Fin r→S×IndexedLeaf k)→ℝ) (hF : Measurable F) {C : ℝ} (hC : 0≤C)
    (hb : ∀ x, |F x|≤C) (j : ℕ) :
    let s : ℝ≥0 := ⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩
    (∫ z, (tiltMean μ H (labelRestorationWeight q s f z) 1)^j *
      gibbsReplicaMean μ H r (labelRestorationTest q s f v w F z)
      ∂countableGaussianLaw.prod countableGaussianLaw) =
    gibbsReplicaMean μ H (r+j) (fun xs => replicaFrontLift F j xs *
      freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f v j))
        (fun i l => if i=l then 1 else q (indexedCommonDepth k (xs l).2 (xs i).2)) *
      freshMarkedMatrixKernel (gaussianMixedTest (labelRestoredFunctions f w j))
        (fun i l => if i=l then 1 else q (indexedCommonDepth k (xs l).2 (xs i).2))) := by
  intro s
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  have he (z : (ℕ→ℝ)×(ℕ→ℝ)) := restoration_replica_moment μ hH
    (labelRestorationWeight_measurable q s f z) (labelRestorationTest_measurable q s f v w hF z) hi
    (sq_nonneg _) (mul_nonneg (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    (labelRestorationWeight_bound q s f z) (labelRestorationTest_bound q s f v w hC hb z) j
  simp_rw [←he,gibbsReplicaMean_integral_of_integrable μ hH hi,labelRestorationTest_replica]
  exact labelProfile_twoMixed_fubini q h0 hq h1 (Measure.pi fun _ : Fin (r+j) => tiltLaw μ H 1)
    (labelRestoredFunctions f v j) (labelRestoredFunctions f w j) (replicaFrontLift F j)
    (replicaFrontLift_measurable hF j) hC (replicaFrontLift_bound hb j)

omit [MeasurableSpace S] in
lemma residual_replica_weight_cancel (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (r : ℕ)
    (v w : Fin r→ℝ →ᵇ ℝ) (a b : S→ℝ) (F : (Fin r→S)→ℝ) (xs : Fin r→S) :
    (∏ i, Real.exp (heatLog s 1 f (a (xs i))+heatLog s 1 f (b (xs i)))) *
      (F xs*(∏ i, residualResponse s f (v i) (a (xs i)))*
        (∏ i, residualResponse s f (w i) (b (xs i)))) =
      F xs*(∏ i, gaussianAverageBCF s (expBCF 1 f*v i) (a (xs i)))*
        (∏ i, gaussianAverageBCF s (expBCF 1 f*w i) (b (xs i))) := by
  have hex (x : ℝ) : Real.exp (heatLog s 1 f x)=gaussianAverage s (expBCF 1 f) x := by
    simpa only [NNReal.coe_one,one_mul] using exp_heatLog s 1 (by norm_num) f x
  simp_rw [Real.exp_add,hex]
  calc
    _ = F xs * (∏ i, gaussianAverage s (expBCF 1 f) (a (xs i))*
          residualResponse s f (v i) (a (xs i))) *
        (∏ i, gaussianAverage s (expBCF 1 f) (b (xs i))*
          residualResponse s f (w i) (b (xs i))) := by
      simp only [Finset.prod_mul_distrib]; ring
    _ = _ := by simp_rw [residualResponse_weighted]; rfl

lemma residual_gibbs_restore (μ : Measure S) [IsProbabilityMeasure μ]
    (J : S→ℝ) (hJ : Measurable J) (hi : Integrable (fun x => Real.exp (J x)) μ)
    (s : ℝ≥0) (f : ℝ →ᵇ ℝ) (r : ℕ) (v w : Fin r→ℝ →ᵇ ℝ)
    (a b : S→ℝ) (F : (Fin r→S)→ℝ) :
    gibbsReplicaMean μ (fun x => J x+(heatLog s 1 f (a x)+heatLog s 1 f (b x))) r
      (fun xs => F xs*(∏ i, residualResponse s f (v i) (a (xs i)))*
        (∏ i, residualResponse s f (w i) (b (xs i)))) =
      gibbsReplicaMean μ J r (fun xs =>
        F xs*(∏ i, gaussianAverageBCF s (expBCF 1 f*v i) (a (xs i)))*
          (∏ i, gaussianAverageBCF s (expBCF 1 f*w i) (b (xs i)))) /
      (tiltMean μ J (fun x => gaussianAverageBCF s (expBCF 1 f) (a x)*
        gaussianAverageBCF s (expBCF 1 f) (b x)) 1)^r := by
  rw [gibbsReplicaMean_restore μ hJ hi]
  have hex (x : S) : Real.exp (heatLog s 1 f (a x)+heatLog s 1 f (b x)) =
      gaussianAverageBCF s (expBCF 1 f) (a x)*gaussianAverageBCF s (expBCF 1 f) (b x) := by
    rw [Real.exp_add]
    have he (y : ℝ) : Real.exp (heatLog s 1 f y)=gaussianAverageBCF s (expBCF 1 f) y := by
      simpa only [NNReal.coe_one,one_mul,gaussianAverageBCF_coe] using exp_heatLog s 1 (by norm_num) f y
    rw [he,he]
  congr 1
  · apply congrArg (gibbsReplicaMean μ J r)
    funext xs
    exact residual_replica_weight_cancel s f r v w a b F xs
  · simp_rw [hex]

lemma labelRestoration_ratio {k r : ℕ} (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : ℝ →ᵇ ℝ)
    (v w : Fin r→ℝ →ᵇ ℝ) (μ : Measure (S×IndexedLeaf k)) [IsProbabilityMeasure μ]
    (J : (S×IndexedLeaf k)→ℝ) (hJ : Measurable J)
    (hi : Integrable (fun x => Real.exp (J x)) μ)
    (F : (Fin r→S×IndexedLeaf k)→ℝ) (z : (ℕ→ℝ)×(ℕ→ℝ)) :
    gibbsReplicaMean μ (fun x => J x+(heatLog s 1 f (labelProfileField q z.1 x)+
        heatLog s 1 f (labelProfileField q z.2 x))) r
      (fun xs => F xs*(∏ i, residualResponse s f (v i) (labelProfileField q z.1 (xs i)))*
        (∏ i, residualResponse s f (w i) (labelProfileField q z.2 (xs i)))) =
      gibbsReplicaMean μ J r (labelRestorationTest q s f v w F z) /
        (tiltMean μ J (labelRestorationWeight q s f z) 1)^r :=
  residual_gibbs_restore μ J hJ hi s f r v w (labelProfileField q z.1) (labelProfileField q z.2) F

end SphericalPerceptronFreeEnergy
end

end OAI
