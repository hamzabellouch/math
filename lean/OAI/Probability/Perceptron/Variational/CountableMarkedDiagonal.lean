import Mathlib
import OAI.Probability.Perceptron.Cavity.LabelFreshKernel
import OAI.Probability.Perceptron.Cavity.FreshMarkedKernel

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma truncatedFreshMarkedKernel {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ)
    (n : ℕ) (xs : Fin r→S) :
    (∫ g, Ψ (WithLp.toLp 2 (fun i => truncatedCountableGaussianField v L n g (xs i)))
      ∂countableGaussianLaw)=
      freshMarkedMatrixKernel Ψ (fun i j => gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
  let rows : Fin r→EuclideanSpace ℝ (Fin n) := fun i =>
    WithLp.toLp 2 (fun j => maskedGaussianCoefficient v L j.val (xs i))
  have hg : Matrix.gram ℝ rows=(fun i j => gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
    ext i j
    change (∑ l : Fin n, maskedGaussianCoefficient v L l.val (xs j)*
      maskedGaussianCoefficient v L l.val (xs i)) = _
    unfold gaussianPrefixCovariance
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [←hg,←freshMarkedMatrixKernel_gaussian,←map_pi_eq_stdGaussian,
    integral_map (by fun_prop) (by fun_prop)]
  have hp := gaussianCoordinatePrefix_measurePreserving n
  have hm : AEStronglyMeasurable (fun y : Fin n→ℝ => Ψ (gaussianRows rows (WithLp.toLp 2 y)))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := by fun_prop
  rw [←hp.map_eq] at hm ⊢
  rw [integral_map hp.measurable.aemeasurable hm]
  rfl

lemma countableFreshMarkedKernel {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) {r : ℕ} (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) (xs : Fin r→S) :
    (∫ g, Ψ (WithLp.toLp 2 (fun i => countableGaussianField v L g (xs i))) ∂countableGaussianLaw)=
      freshMarkedMatrixKernel Ψ (fun i j => countableGaussianCovariance v v L (xs i) (xs j)) := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i : Fin r, ∀ g,
      truncatedCountableGaussianField v L n g (xs i)=countableGaussianField v L g (xs i) :=
    Filter.eventually_all.mpr (fun i => truncatedCountableGaussianField_eventually_eq v L (xs i))
  have hc : ∀ᶠ n : ℕ in atTop, ∀ i j : Fin r,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn,hc⟩ := (he.and hc).exists
  simpa only [hn,hc] using truncatedFreshMarkedKernel v L Ψ n xs

def gaussianMixedTest {r : ℕ} (f : Fin r→ℝ →ᵇ ℝ) : EuclideanSpace ℝ (Fin r) →ᵇ ℝ :=
  ∏ i : Fin r, (f i).compContinuous ⟨fun x => x i,by fun_prop⟩

@[simp] lemma gaussianMixedTest_apply {r : ℕ} (f : Fin r→ℝ →ᵇ ℝ)
    (x : EuclideanSpace ℝ (Fin r)) : gaussianMixedTest f x=∏ i, f i (x i) := by
  simp [gaussianMixedTest]

lemma freshMixedKernel_diagonal_noise {r n : ℕ} (f : Fin r→ℝ →ᵇ ℝ)
    (v : Fin r→EuclideanSpace ℝ (Fin n)) (s : ℝ≥0) :
    freshMarkedMatrixKernel (gaussianMixedTest f)
      (fun i j => Matrix.gram ℝ v i j + if i=j then (s:ℝ) else 0)=
      freshMarkedMatrixKernel (gaussianMixedTest (fun i => gaussianAverageBCF s (f i)))
        (Matrix.gram ℝ v) := by
  classical
  rw [←freshNoiseRows_gram v s,←freshMarkedMatrixKernel_gaussian,
    ←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  let F : (Fin n→ℝ)×(Fin r→ℝ)→ℝ := fun p =>
    ∏ i : Fin r, f i (inner ℝ (v i) (WithLp.toLp 2 p.1)+Real.sqrt s*p.2 i)
  have hF : Integrable F ((Measure.pi fun _ : Fin n => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin r => gaussianReal 0 1)) := by
    apply Integrable.of_bound (by fun_prop) (∏ i, ‖f i‖)
    exact ae_of_all _ fun p => by
      simp only [F,norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun index _ => (f index).norm_coe_le_norm _)
  have hp := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n⊕Fin r => gaussianReal 0 1)
  have hm : AEStronglyMeasurable (fun z : Fin n⊕Fin r→ℝ =>
      gaussianMixedTest f (gaussianRows (freshNoiseRows v s) (WithLp.toLp 2 z)))
      (Measure.pi fun _ => gaussianReal 0 1) := by fun_prop
  rw [←hp.map_eq] at hm ⊢
  rw [integral_map hp.measurable.aemeasurable hm]
  have he : (fun p : (Fin n→ℝ)×(Fin r→ℝ) =>
      gaussianMixedTest f (gaussianRows (freshNoiseRows v s)
        (WithLp.toLp 2 ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n⊕Fin r => ℝ)).symm p))))=F := by
    funext p
    simp only [gaussianMixedTest_apply,gaussianRows_apply]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (f i) (freshNoiseRows_apply v s p.1 p.2 i)
  rw [he,integral_prod _ hF]
  have hi (x : Fin n→ℝ) : (∫ y : Fin r→ℝ, F (x,y) ∂Measure.pi (fun _ => gaussianReal 0 1))=
      gaussianMixedTest (fun i => gaussianAverageBCF s (f i)) (gaussianRows v (WithLp.toLp 2 x)) := by
    rw [gaussianMixedTest_apply]
    change (∫ y : Fin r→ℝ, ∏ i, f i (inner ℝ (v i) (WithLp.toLp 2 x)+Real.sqrt s*y i)
      ∂Measure.pi (fun _ => gaussianReal 0 1))=_
    rw [integral_fintype_prod_eq_prod (f := fun i y => f i (inner ℝ (v i) (WithLp.toLp 2 x)+Real.sqrt s*y))]
    apply Finset.prod_congr rfl
    intro i hi
    exact (gaussianAverage_scaling s (f i) _).symm
  simp_rw [hi]
  rw [←freshMarkedMatrixKernel_gaussian,←map_pi_eq_stdGaussian,
    integral_map (by fun_prop) (by fun_prop)]

lemma countableFreshMixed_diagonal {S : Type*} [MeasurableSpace S]
    (v : ℕ→S→ℝ) (L : S→ℕ) {r : ℕ} (f : Fin r→ℝ →ᵇ ℝ) (s : ℝ≥0) (xs : Fin r→S) :
    (∫ g, ∏ i, gaussianAverageBCF s (f i) (countableGaussianField v L g (xs i)) ∂countableGaussianLaw)=
      freshMarkedMatrixKernel (gaussianMixedTest f)
        (fun i j => countableGaussianCovariance v v L (xs i) (xs j) + if i=j then (s:ℝ) else 0) := by
  have h := countableFreshMarkedKernel v L (gaussianMixedTest (fun i => gaussianAverageBCF s (f i))) xs
  simp only [gaussianMixedTest_apply] at h
  rw [h]
  obtain ⟨n,w,hw⟩ := countableGaussianCovariance_finite_gram v L r xs
  have he (i j : Fin r) := congrFun (congrFun hw i) j
  simp_rw [←he]
  exact (freshMixedKernel_diagonal_noise f w s).symm

variable {S : Type} [MeasurableSpace S] {k r : ℕ}

def labelMarkedBlockKernel (q : Fin (k+1)→ℝ) (Ψ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    CompactBlock CompactJointOverlap r →ᵇ ℝ :=
  (freshMarkedMatrixKernel Ψ).compContinuous
    ⟨fun Q => fun i j => if i=j then 1 else labelProfileInterpolant q (Q i j).2,by
      classical
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      by_cases hij : i=j
      · simp only [ite_eq_left hij]; exact continuous_const
      · simp only [ite_eq_right hij]; fun_prop⟩

lemma labelProfile_mixed_kernel (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (h1 : q (Fin.last k)≤1) (f : Fin r→ℝ →ᵇ ℝ) (xs : Fin r→S×IndexedLeaf k) :
    (∫ g, ∏ i, gaussianAverageBCF (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) (f i)
      (labelProfileField q g (xs i)) ∂countableGaussianLaw)=
      freshMarkedMatrixKernel (gaussianMixedTest f)
        (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2)) := by
  have h := countableFreshMixed_diagonal (labelProfileRow q)
    (indexedGaussianRowLength (I := Fin 1) k) f (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) xs
  apply h.trans
  apply congrArg (freshMarkedMatrixKernel (gaussianMixedTest f))
  funext i j
  rw [labelProfile_covariance q h0 hq]
  by_cases hij : i=j
  · subst j
    simp only [ite_true,indexedCommonDepth_self]
    change q (Fin.last k)+(1-q (Fin.last k))=1
    ring
  · simp only [ite_eq_right hij,add_zero]

lemma labelProfileField_product_measurable (q : Fin (k+1)→ℝ) :
    Measurable (fun p : (ℕ→ℝ)×(S×IndexedLeaf k) => labelProfileField q p.1 p.2) :=
  countableGaussianField_measurable (v := labelProfileRow q)
    (indexedGaussianRow_measurable k _ measurable_const)
    (indexedGaussianRowLength_measurable (I := Fin 1) k)

def labelMixedValue (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : Fin r→ℝ →ᵇ ℝ)
    (z : ℕ→ℝ) (xs : Fin r→S×IndexedLeaf k) : ℝ :=
  ∏ i, gaussianAverageBCF s (f i) (labelProfileField q z (xs i))

lemma measurableReplicaProduct {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (V : A→B→ℝ) (hV : Measurable (Function.uncurry V)) (f : Fin r→ℝ →ᵇ ℝ) :
    Measurable (fun p : A×(Fin r→B) => ∏ i, f i (V p.1 (p.2 i))) := by
  have h (i : Fin r) : Measurable (fun p : A×(Fin r→B) => f i (V p.1 (p.2 i))) :=
    (f i).measurable.comp (hV.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact Finset.measurable_prod Finset.univ (fun i _ => h i)

lemma labelMixedValue_measurable (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : Fin r→ℝ →ᵇ ℝ) :
    Measurable (Function.uncurry (labelMixedValue (S:=S) q s f)) :=
  measurableReplicaProduct (labelProfileField q) (labelProfileField_product_measurable q)
    (fun i => gaussianAverageBCF s (f i))

lemma labelMixedValue_bound {S : Type} [MeasurableSpace S] {k r : ℕ}
    (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f : Fin r→ℝ →ᵇ ℝ)
    (z : ℕ→ℝ) (xs : Fin r→S×IndexedLeaf k) :
    |labelMixedValue q s f z xs|≤∏ i, ‖gaussianAverageBCF s (f i)‖ := by
  simp only [labelMixedValue,Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun index _ =>
    (gaussianAverageBCF s (f index)).norm_coe_le_norm _)

lemma labelTwoMixed_measurable (q : Fin (k+1)→ℝ) (s : ℝ≥0) (f g : Fin r→ℝ →ᵇ ℝ)
    (F : (Fin r→S×IndexedLeaf k)→ℝ) (hF : Measurable F) :
    Measurable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) =>
      F p.2 * labelMixedValue q s f p.1.1 p.2 * labelMixedValue q s g p.1.2 p.2) := by
  have hf := (labelMixedValue_measurable (S:=S) q s f).comp
    (measurable_fst.fst.prodMk measurable_snd : Measurable
      (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) => (p.1.1,p.2)))
  have hg := (labelMixedValue_measurable (S:=S) q s g).comp
    (measurable_fst.snd.prodMk measurable_snd : Measurable
      (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) => (p.1.2,p.2)))
  exact ((hF.comp measurable_snd).mul hf).mul hg

lemma labelProfile_twoMixed_fubini (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q)
    (h1 : q (Fin.last k)≤1) (ν : Measure (Fin r→S×IndexedLeaf k)) [IsProbabilityMeasure ν]
    (f g : Fin r→ℝ →ᵇ ℝ) (F : (Fin r→S×IndexedLeaf k)→ℝ) (hF : Measurable F)
    {C : ℝ} (hC : 0≤C) (hb : ∀ xs, |F xs|≤C) :
    (∫ z, ∫ xs, F xs *
      (∏ i, gaussianAverageBCF (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) (f i) (labelProfileField q z.1 (xs i))) *
      (∏ i, gaussianAverageBCF (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0) (g i) (labelProfileField q z.2 (xs i))) ∂ν
      ∂countableGaussianLaw.prod countableGaussianLaw) =
    ∫ xs, F xs * freshMarkedMatrixKernel (gaussianMixedTest f)
      (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2)) *
      freshMarkedMatrixKernel (gaussianMixedTest g)
        (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2)) ∂ν := by
  let s : ℝ≥0 := (⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ : ℝ≥0)
  have hm := labelTwoMixed_measurable q s f g F hF
  have hi : Integrable (fun p : ((ℕ→ℝ)×(ℕ→ℝ))×(Fin r→S×IndexedLeaf k) =>
      F p.2 * (∏ i, gaussianAverageBCF s (f i) (labelProfileField q p.1.1 (p.2 i))) *
        (∏ i, gaussianAverageBCF s (g i) (labelProfileField q p.1.2 (p.2 i))))
      ((countableGaussianLaw.prod countableGaussianLaw).prod ν) := by
    apply Integrable.of_bound hm.aestronglyMeasurable
      (C*(∏ i, ‖gaussianAverageBCF s (f i)‖)*(∏ i, ‖gaussianAverageBCF s (g i)‖))
    exact ae_of_all _ fun p => by
      simp only [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul (mul_le_mul (hb _) (labelMixedValue_bound q s f p.1.1 p.2)
          (abs_nonneg _) hC) (labelMixedValue_bound q s g p.1.2 p.2)
        (abs_nonneg _) (mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _))

  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ fun xs => by
    change (∫ z, F xs * labelMixedValue q s f z.1 xs * labelMixedValue q s g z.2 xs
      ∂countableGaussianLaw.prod countableGaussianLaw)=_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    apply congrArg (fun y => F xs*y)
    calc
      _ = (∫ z, labelMixedValue q s f z xs ∂countableGaussianLaw)*
          (∫ z, labelMixedValue q s g z xs ∂countableGaussianLaw) := integral_prod_mul _ _
      _ = _ := congrArg₂ (·*·) (labelProfile_mixed_kernel q h0 hq h1 f xs)
        (labelProfile_mixed_kernel q h0 hq h1 g xs)

end SphericalPerceptronFreeEnergy
end

end OAI
