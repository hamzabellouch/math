import Mathlib
import OAI.Probability.SKRatio.Dynamics.Median
import OAI.Probability.SKRatio.Calculus.GradientMoments

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter

namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma transition_balance {n : ℕ} (g : Disorder n) (x y : Spin n) :
    mass g 0 x * transition g x y = mass g 0 y * transition g y x := by
  by_cases hn : n = 0
  · simp only [transition, hn, ↓reduceIte, Matrix.one_apply]
    by_cases h : x = y
    · subst y
      simp
    · simp [h, Ne.symm h]
  · simp only [transition, hn, ↓reduceIte, mul_div, Finset.mul_sum]
    simp_rw [siteKernel_balance g _ x y]

def stationaryInner {n : ℕ} (g : Disorder n) (f h : Observables n) : ℝ :=
  FiniteLaw.mean (mass g 0) (fun x => f x*h x)

def stationaryPairingCLM {n : ℕ} (g : Disorder n) (f : Observables n) :
    Observables n →L[ℝ] ℝ :=
  (show Observables n →ₗ[ℝ] ℝ from
    { toFun := stationaryInner g f
      map_add' a b := by
        simp [stationaryInner, FiniteLaw.mean, mul_add, Finset.sum_add_distrib]
      map_smul' c a := by
        simp [stationaryInner, FiniteLaw.mean, mul_left_comm, ← Finset.mul_sum]
    }).toContinuousLinearMap

@[simp] lemma stationaryPairingCLM_apply {n : ℕ} (g : Disorder n) (f h : Observables n) :
    stationaryPairingCLM g f h = stationaryInner g f h := rfl

lemma stationaryInner_symm {n : ℕ} (g : Disorder n) (f h : Observables n) :
    stationaryInner g f h = stationaryInner g h f := by
  simp only [stationaryInner, mul_comm (f _) (h _)]

lemma generator_symmetric {n : ℕ} (g : Disorder n) (f h : Observables n) :
    stationaryInner g f (generator (coupling g) h) =
      stationaryInner g (generator (coupling g) f) h := by
  have hpair : (∑ x, ∑ y, mass g 0 x * transition g x y * f x * h y) =
      ∑ y, ∑ x, mass g 0 y * transition g y x * f x * h y := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    rw [transition_balance]
  unfold stationaryInner FiniteLaw.mean
  simp only [generator_eq_transition, mul_sub, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul]
  have he (x : Spin n) (y : Spin n) :
      mass g 0 x * (f x * ((n:ℝ)*(transition g x y*h y))) =
        (n:ℝ)*(mass g 0 x*transition g x y*f x*h y) := by ring
  have he' (y : Spin n) (x : Spin n) :
      mass g 0 y * (((n:ℝ)*(transition g y x*f x))*h y) =
        (n:ℝ)*(mass g 0 y*transition g y x*f x*h y) := by ring
  simp_rw [he,he',← Finset.mul_sum,hpair]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma stationaryInner_pow_symm {n : ℕ} (g : Disorder n)
    (A : Observables n →L[ℝ] Observables n)
    (hA : ∀ f h, stationaryInner g f (A h) = stationaryInner g (A f) h)
    (k : ℕ) (f h : Observables n) :
    stationaryInner g f ((A^k) h) = stationaryInner g ((A^k) f) h := by
  induction k generalizing f h with
  | zero => simp
  | succ k ih =>
    calc
      _ = stationaryInner g (A f) ((A^k) h) := by
        rw [pow_succ', mul_apply_eq_comp, hA]
      _ = stationaryInner g ((A^k) (A f)) h := ih (A f) h
      _ = _ := by rw [pow_succ, mul_apply_eq_comp]

lemma stationaryInner_exp_symm {n : ℕ} (g : Disorder n)
    (A : Observables n →L[ℝ] Observables n)
    (hA : ∀ f h, stationaryInner g f (A h) = stationaryInner g (A f) h)
    (f h : Observables n) :
    stationaryInner g f (NormedSpace.exp A h) = stationaryInner g (NormedSpace.exp A f) h := by
  have hf : HasSum (fun k : ℕ => ((k.factorial:ℝ)⁻¹)*stationaryInner g f ((A^k) h))
      (stationaryInner g f (NormedSpace.exp A h)) := by
    simpa only [map_smul,smul_eq_mul,stationaryPairingCLM_apply] using
      (stationaryPairingCLM g f).hasSum (exp_apply_hasSum A h)
  have hh : HasSum (fun k : ℕ => ((k.factorial:ℝ)⁻¹)*stationaryInner g h ((A^k) f))
      (stationaryInner g h (NormedSpace.exp A f)) := by
    simpa only [map_smul,smul_eq_mul,stationaryPairingCLM_apply] using
      (stationaryPairingCLM g h).hasSum (exp_apply_hasSum A f)
  have hp (k : ℕ) : stationaryInner g f ((A^k) h) = stationaryInner g h ((A^k) f) := by
    rw [stationaryInner_pow_symm g A hA,stationaryInner_symm]
  simp_rw [hp] at hf
  rw [← stationaryInner_symm g h]
  exact hf.unique hh

lemma semigroup_symmetric {n : ℕ} (g : Disorder n) (t : ℝ) (f h : Observables n) :
    stationaryInner g f (semigroup (coupling g) t h) =
      stationaryInner g (semigroup (coupling g) t f) h := by
  apply stationaryInner_exp_symm
  intro a b
  have he := congrArg (fun z : ℝ => t*z) (generator_symmetric g a b)
  change (∑ x, mass g 0 x*(a x*(t*generator (coupling g) b x))) =
    ∑ x, mass g 0 x*((t*generator (coupling g) a x)*b x)
  convert he using 1 <;> simp only [stationaryInner,FiniteLaw.mean,Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro x _ <;> ring

lemma exp_apply_of_eigenvector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (f : E) (a : ℝ)
    (h : A f = a • f) : NormedSpace.exp A f = Real.exp a • f := by
  have hp (k : ℕ) : (A^k) f = a^k • f := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ',mul_apply_eq_comp,ih,map_smul,h,smul_smul,pow_succ]
  have hs : HasSum (fun k : ℕ => (k.factorial:ℝ)⁻¹*a^k) (Real.exp a) := by
    simpa only [smul_eq_mul,Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a)
  apply (exp_apply_hasSum A f).unique
  simpa only [hp,smul_smul] using hs.smul_const f

def gibbsEuclideanEquiv {n : ℕ} (g : Disorder n) :
    Observables n ≃ₗ[ℝ] EuclideanSpace ℝ (Spin n) where
  toFun f := WithLp.toLp 2 (fun x => Real.sqrt (mass g 0 x)*f x)
  invFun u x := u x/Real.sqrt (mass g 0 x)
  left_inv f := by
    funext x
    exact mul_div_cancel_left₀ (f x) (ne_of_gt (Real.sqrt_pos.2 (mass_pos g 0 x)))
  right_inv u := by
    ext x
    exact mul_div_cancel₀ (u x) (ne_of_gt (Real.sqrt_pos.2 (mass_pos g 0 x)))
  map_add' f h := by ext x; simp [mul_add]
  map_smul' a f := by ext x; simp [mul_left_comm]

@[simp] lemma gibbsEuclideanEquiv_apply {n : ℕ} (g : Disorder n) (f : Observables n) (x : Spin n) :
    gibbsEuclideanEquiv g f x = Real.sqrt (mass g 0 x)*f x := rfl

lemma gibbsEuclideanEquiv_inner {n : ℕ} (g : Disorder n) (f h : Observables n) :
    inner (𝕜 := ℝ) (gibbsEuclideanEquiv g f) (gibbsEuclideanEquiv g h) = stationaryInner g f h := by
  rw [PiLp.inner_apply]
  unfold stationaryInner FiniteLaw.mean
  apply Finset.sum_congr rfl
  intro x _
  simp only [gibbsEuclideanEquiv_apply,RCLike.inner_apply,conj_trivial]
  nlinarith only [congrArg (fun a : ℝ => a*f x*h x) (Real.sq_sqrt (mass_nonneg g 0 x))]

def negativeGeneratorEuclidean {n : ℕ} (g : Disorder n) :
    EuclideanSpace ℝ (Spin n) →ₗ[ℝ] EuclideanSpace ℝ (Spin n) :=
  (gibbsEuclideanEquiv g).toLinearMap.comp
    ((-generatorLM (coupling g)).comp (gibbsEuclideanEquiv g).symm.toLinearMap)

lemma negativeGeneratorEuclidean_lift {n : ℕ} (g : Disorder n) (f : Observables n) :
    negativeGeneratorEuclidean g (gibbsEuclideanEquiv g f) =
      gibbsEuclideanEquiv g (-generator (coupling g) f) := by
  simp [negativeGeneratorEuclidean,generatorLM]

lemma negativeGeneratorEuclidean_symmetric {n : ℕ} (g : Disorder n) :
    (negativeGeneratorEuclidean g).IsSymmetric := by
  intro u v
  obtain ⟨f,rfl⟩ := (gibbsEuclideanEquiv g).surjective u
  obtain ⟨h,rfl⟩ := (gibbsEuclideanEquiv g).surjective v
  rw [negativeGeneratorEuclidean_lift,negativeGeneratorEuclidean_lift,
    gibbsEuclideanEquiv_inner,gibbsEuclideanEquiv_inner]
  have he := generator_symmetric g f h
  simp only [stationaryInner,FiniteLaw.mean] at he ⊢
  simpa only [Pi.neg_apply,neg_mul,mul_neg,Finset.sum_neg_distrib] using congrArg Neg.neg he.symm

def spinEigenvalues {n : ℕ} (g : Disorder n) : Fin (Fintype.card (Spin n)) → ℝ :=
  (negativeGeneratorEuclidean_symmetric g).eigenvalues finrank_euclideanSpace

def spinEigenbasis {n : ℕ} (g : Disorder n) :
    OrthonormalBasis (Fin (Fintype.card (Spin n))) ℝ (EuclideanSpace ℝ (Spin n)) :=
  (negativeGeneratorEuclidean_symmetric g).eigenvectorBasis finrank_euclideanSpace

def spectralCoefficient {n : ℕ} (g : Disorder n) (f : Observables n)
    (a : Fin (Fintype.card (Spin n))) : ℝ :=
  (spinEigenbasis g).repr (gibbsEuclideanEquiv g f) a

lemma spectral_parseval {n : ℕ} (g : Disorder n) (f h : Observables n) :
    (∑ a, spectralCoefficient g f a*spectralCoefficient g h a) = stationaryInner g f h := by
  have he := (spinEigenbasis g).repr.inner_map_map (gibbsEuclideanEquiv g f) (gibbsEuclideanEquiv g h)
  rw [PiLp.inner_apply,gibbsEuclideanEquiv_inner] at he
  simpa only [spectralCoefficient,RCLike.inner_apply,conj_trivial,mul_comm] using he

lemma spectral_generator_coordinates {n : ℕ} (g : Disorder n) (f : Observables n)
    (a : Fin (Fintype.card (Spin n))) :
    spectralCoefficient g (-generator (coupling g) f) a = spinEigenvalues g a*spectralCoefficient g f a := by
  unfold spectralCoefficient
  rw [← negativeGeneratorEuclidean_lift]
  exact (negativeGeneratorEuclidean_symmetric g).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace (gibbsEuclideanEquiv g f) a

def scalarEigenfunction {n : ℕ} (g : Disorder n) (a : Fin (Fintype.card (Spin n))) : Observables n :=
  (gibbsEuclideanEquiv g).symm (spinEigenbasis g a)

@[simp] lemma lift_scalarEigenfunction {n : ℕ} (g : Disorder n) (a : Fin (Fintype.card (Spin n))) :
    gibbsEuclideanEquiv g (scalarEigenfunction g a) = spinEigenbasis g a :=
  (gibbsEuclideanEquiv g).apply_symm_apply _

lemma generator_scalarEigenfunction {n : ℕ} (g : Disorder n) (a : Fin (Fintype.card (Spin n))) :
    generator (coupling g) (scalarEigenfunction g a) = -spinEigenvalues g a • scalarEigenfunction g a := by
  have he : negativeGeneratorEuclidean g (spinEigenbasis g a) = spinEigenvalues g a • spinEigenbasis g a :=
    (negativeGeneratorEuclidean_symmetric g).apply_eigenvectorBasis finrank_euclideanSpace a
  have hf : -generator (coupling g) (scalarEigenfunction g a) = spinEigenvalues g a • scalarEigenfunction g a := by
    apply (gibbsEuclideanEquiv g).injective
    rw [← negativeGeneratorEuclidean_lift,map_smul,lift_scalarEigenfunction]
    exact he
  simpa only [neg_neg,neg_smul] using congrArg Neg.neg hf

lemma semigroup_scalarEigenfunction {n : ℕ} (g : Disorder n) (a : Fin (Fintype.card (Spin n))) (t : ℝ) :
    semigroup (coupling g) t (scalarEigenfunction g a) =
      Real.exp (-spinEigenvalues g a*t) • scalarEigenfunction g a := by
  apply exp_apply_of_eigenvector
  rw [smul_apply]
  change t • generator (coupling g) (scalarEigenfunction g a) = _
  rw [generator_scalarEigenfunction,smul_smul,mul_comm]

lemma spectral_coordinates_inner {n : ℕ} (g : Disorder n) (f : Observables n)
    (a : Fin (Fintype.card (Spin n))) :
    spectralCoefficient g f a = stationaryInner g (scalarEigenfunction g a) f := by
  rw [spectralCoefficient,OrthonormalBasis.repr_apply_apply,← lift_scalarEigenfunction g a,
    gibbsEuclideanEquiv_inner]

lemma spectral_semigroup_coordinates {n : ℕ} (g : Disorder n) (f : Observables n) (t : ℝ)
    (a : Fin (Fintype.card (Spin n))) :
    spectralCoefficient g (semigroup (coupling g) t f) a =
      Real.exp (-spinEigenvalues g a*t)*spectralCoefficient g f a := by
  rw [spectral_coordinates_inner,spectral_coordinates_inner,semigroup_symmetric,semigroup_scalarEigenfunction]
  simp only [stationaryInner,FiniteLaw.mean,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma stationary_correlation_lower {n : ℕ} (g : Disorder n) (f : Observables n)
    (hnorm : stationaryInner g f f = 1) (t : ℝ) :
    Real.exp (-t*stationaryEnergy g f) ≤ stationaryInner g f (semigroup (coupling g) t f) := by
  have hsum : (∑ a, spectralCoefficient g f a^2) = 1 := by
    simpa only [pow_two,hnorm] using spectral_parseval g f f
  have hE : (∑ a, spectralCoefficient g f a^2*spinEigenvalues g a) = stationaryEnergy g f := by
    have he := spectral_parseval g f (-generator (coupling g) f)
    simp only [spectral_generator_coordinates] at he
    rw [stationaryEnergy_eq]
    change _ = -(∑ x, mass g 0 x * (f x * generator (coupling g) f x))
    have hinner : stationaryInner g f (-generator (coupling g) f) =
        -(∑ x, mass g 0 x * (f x * generator (coupling g) f x)) := by
      simp [stationaryInner,FiniteLaw.mean]
    rw [← hinner,← he]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have he := convexOn_exp.map_sum_le (s := Set.univ) (p := fun a => -t*spinEigenvalues g a)
    (fun a (_ : a ∈ Finset.univ) => sq_nonneg (spectralCoefficient g f a)) hsum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at he
  have hl : (∑ a, spectralCoefficient g f a^2*(-t*spinEigenvalues g a)) = -t*stationaryEnergy g f := by
    rw [← hE,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hl] at he
  rw [← spectral_parseval]
  simp_rw [spectral_semigroup_coordinates]
  calc
    _ ≤ ∑ a, spectralCoefficient g f a ^ 2 * Real.exp (-t * spinEigenvalues g a) := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show -spinEigenvalues g a * t = -t * spinEigenvalues g a by ring]
      ring

lemma gibbsMean_siteKernel {n : ℕ} (g : Disorder n) (i : Fin n) (f : Observables n) :
    FiniteLaw.mean (mass g 0) (fun x => ∑ y, siteKernel g i x y * f y) =
      FiniteLaw.mean (mass g 0) f := by
  unfold FiniteLaw.mean
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, siteKernel_stationary]

lemma gibbsMean_spin_times_mean {n : ℕ} (g : Disorder n) (i : Fin n) :
    FiniteLaw.mean (mass g 0) (fun x => spin x i * mean (coupling g) x i) =
      FiniteLaw.mean (mass g 0) (fun x => mean (coupling g) x i ^ 2) := by
  have hpoint (x : Spin n) : (∑ y, siteKernel g i x y *
      (spin y i * mean (coupling g) y i)) = mean (coupling g) x i ^ 2 := by
    rw [siteKernel_apply, spin_flip_self]
    have hm : mean (coupling g) (flip i x) i = mean (coupling g) x i := by
      simp only [mean, field_flip _ (coupling_diag g)]
    rw [hm, flipRate]
    nlinarith only [congrArg (fun a : ℝ => a * mean (coupling g) x i ^ 2) (spin_sq x i)]
  rw [← gibbsMean_siteKernel g i, show
    (fun x => ∑ y, siteKernel g i x y * (spin y i * mean (coupling g) y i)) =
      (fun x => mean (coupling g) x i ^ 2) by funext x; exact hpoint x]

lemma stationary_weight_le_one {n : ℕ} (g : Disorder n) (i : Fin n) :
    FiniteLaw.mean (mass g 0) (fun x => gradientWeight (coupling g) x i) ≤ 1 := by
  have he : FiniteLaw.mean (mass g 0) (fun x => gradientWeight (coupling g) x i) =
      1 - FiniteLaw.mean (mass g 0) (fun x => mean (coupling g) x i ^ 2) := by
    simp only [gradientWeight, FiniteLaw.mean, mul_sub, mul_one, Finset.sum_sub_distrib,
      sum_mass]
    congr 1
    exact gibbsMean_spin_times_mean g i
  rw [he]
  have hn : 0 ≤ FiniteLaw.mean (mass g 0) (fun x => mean (coupling g) x i ^ 2) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg g 0 x) (sq_nonneg _))
  linarith only [hn]

lemma stationaryEnergy_spin_le_one {n : ℕ} (g : Disorder n) (i : Fin n) :
    stationaryEnergy g (fun x => spin x i) ≤ 1 := by
  have hw (x : Spin n) : weightedGradient (coupling g) (fun y => spin y i) x =
      gradientWeight (coupling g) x i := by
    simp only [weightedGradient, halfDiff_spin, ite_pow, one_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_ite, mul_one, mul_zero,
      Fintype.sum_ite_eq']
  unfold stationaryEnergy FiniteLaw.mean
  simp_rw [hw]
  exact stationary_weight_le_one g i

lemma spin_correlation_lower {n : ℕ} (g : Disorder n) (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ stationaryInner g (fun x => spin x i)
      (semigroup (coupling g) t (fun x => spin x i)) := by
  have hnorm : stationaryInner g (fun x => spin x i) (fun x => spin x i) = 1 := by
    simp [stationaryInner, FiniteLaw.mean, ← pow_two, spin_sq, sum_mass]
  have hh := stationary_correlation_lower g (fun x => spin x i) hnorm t
  have hE := mul_le_mul_of_nonneg_left (stationaryEnergy_spin_le_one g i) ht
  exact (Real.exp_le_exp.mpr (by linarith only [hE])).trans hh

def linearObservable {n : ℕ} (a : Fin n → ℝ) : Observables n := fun x => ∑ i, a i * spin x i

lemma halfDiff_linearObservable {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : Spin n) :
    halfDiff i (linearObservable a) x = a i := by
  unfold linearObservable
  rw [halfDiff_sum]
  have he (j : Fin n) : halfDiff i (fun y => a j * spin y j) x = a j * halfDiff i (fun y => spin y j) x := by
    unfold halfDiff
    ring
  simp only [he, halfDiff_spin, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq]

lemma unweightedGradient_linearObservable {n : ℕ} (a : Fin n → ℝ) (x : Spin n) :
    unweightedGradient (linearObservable a) x = ∑ i, a i ^ 2 := by
  simp only [unweightedGradient, halfDiff_linearObservable]

lemma gibbsMean_linearObservable_zero {n : ℕ} (g : Disorder n) (a : Fin n → ℝ) :
    FiniteLaw.mean (mass g 0) (linearObservable a) = 0 := by
  let e : Spin n ≃ Spin n := Function.Involutive.toPerm reversal (fun x => reversal_reversal x)
  have he := Equiv.sum_comp e (fun x => mass g 0 x * linearObservable a x)
  change (∑ x, mass g 0 (reversal x) * linearObservable a (reversal x)) = _ at he
  have hr (x : Spin n) : linearObservable a (reversal x) = -linearObservable a x := by
    simp [linearObservable, spin_reversal, Finset.sum_neg_distrib]
  simp only [mass_reversal, hr, mul_neg, Finset.sum_neg_distrib] at he
  unfold FiniteLaw.mean
  linarith only [he]

lemma stationaryEnergy_linearObservable_le {n : ℕ} (g : Disorder n) (a : Fin n → ℝ) :
    stationaryEnergy g (linearObservable a) ≤ ∑ i, a i ^ 2 := by
  unfold stationaryEnergy FiniteLaw.mean weightedGradient
  simp only [halfDiff_linearObservable, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (stationary_weight_le_one g i) (sq_nonneg (a i))
  simpa only [FiniteLaw.mean, one_mul, Finset.sum_mul, mul_assoc] using h

lemma stationary_linearObservable_variance_le {n : ℕ} (g : Disorder n) {γ : ℝ}
    (hγ : 0 < γ)
    (hgap : ∀ f : Observables n, γ * FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (a : Fin n → ℝ) :
    FiniteLaw.variance (mass g 0) (linearObservable a) ≤ (∑ i, a i ^ 2) / γ := by
  apply (le_div_iff₀ hγ).mpr
  simpa only [mul_comm γ] using (hgap (linearObservable a)).trans (stationaryEnergy_linearObservable_le g a)

lemma semigroup_linearObservable {n : ℕ} (J : Interaction n) (a : Fin n → ℝ) (t : ℝ) (x : Spin n) :
    semigroup J t (linearObservable a) x = ∑ i, a i * semigroup J t (fun y => spin y i) x := by
  have he : linearObservable a = ∑ i, a i • (fun y : Spin n => spin y i) := by
    ext y
    simp [linearObservable]
  rw [he, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma exists_distinguishing_linear {n : ℕ} (hn : 0 < n) (g : Disorder n) {t : ℝ} (ht : 0 ≤ t) :
    ∃ x : Spin n, ∃ a : Fin n → ℝ, (∑ i, a i ^ 2) = 1 ∧
      Real.sqrt n * Real.exp (-t) ≤ semigroup (coupling g) t (linearObservable a) x := by
  let F (x : Spin n) := ∑ i, spin x i * semigroup (coupling g) t (fun y => spin y i) x
  have hsum : (n : ℝ) * Real.exp (-t) ≤ FiniteLaw.mean (mass g 0) F := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => spin_correlation_lower g i ht)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      stationaryInner, FiniteLaw.mean] at h
    unfold FiniteLaw.mean
    dsimp only [F]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact h
  obtain ⟨x, _, hmax⟩ := Finset.exists_max_image Finset.univ F Finset.univ_nonempty
  have hx : (n : ℝ) * Real.exp (-t) ≤ F x := by
    calc
      _ ≤ _ := hsum
      _ ≤ ∑ y, mass g 0 y * F x := Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hmax y (Finset.mem_univ y)) (mass_nonneg g 0 y))
      _ = _ := by rw [← Finset.sum_mul, sum_mass, one_mul]
  let a (i : Fin n) := spin x i / Real.sqrt n
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnp
  refine ⟨x, a, ?_, ?_⟩
  · simp only [a, div_pow, spin_sq, Real.sq_sqrt hnp.le, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · rw [semigroup_linearObservable]
    have he : (∑ i, a i * semigroup (coupling g) t (fun y => spin y i) x) = F x / Real.sqrt n := by
      simp only [a, F, Finset.sum_div, div_mul_eq_mul_div]
    rw [he]
    apply (le_div_iff₀ hsqrt).mpr
    have heq : Real.sqrt n * Real.exp (-t) * Real.sqrt n = (n : ℝ) * Real.exp (-t) := by
      nlinarith only [congrArg (fun z : ℝ => z * Real.exp (-t)) (Real.sq_sqrt hnp.le)]
    rwa [heq]

lemma continuousDistance_lower_of_linear_variances {n : ℕ} (hn : 0 < n)
    (g : Disorder n) {t V W : ℝ} (ht : 0 ≤ t)
    (htrans : ∀ (a : Fin n → ℝ), (∑ i, a i ^ 2) = 1 → ∀ x,
      FiniteLaw.variance (continuousKernel (coupling g) t x) (linearObservable a) ≤ V)
    (hstat : ∀ (a : Fin n → ℝ), (∑ i, a i ^ 2) = 1 →
      FiniteLaw.variance (mass g 0) (linearObservable a) ≤ W) :
    1 - 2*(V+W)*Real.exp (2*t)/n ≤ continuousDistance g t := by
  obtain ⟨x,a,ha,hm⟩ := exists_distinguishing_linear hn g ht
  let m := semigroup (coupling g) t (linearObservable a) x
  let d := totalVariation (continuousKernel (coupling g) t x) (mass g 0)
  have hcommon := FiniteLaw.common_mass_square (continuousKernel (coupling g) t x)
    (mass g 0) (linearObservable a) (continuousKernel_nonneg _ t ht x)
    (mass_nonneg g 0) (continuousKernel_sum _ t x) (sum_mass g 0)
  rw [gibbsMean_linearObservable_zero, sub_zero, ← semigroup_eq_kernel] at hcommon
  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)).trans hm
  have hsq : (n : ℝ)*Real.exp (-2*t) ≤ m^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt n * Real.exp (-t)) hm0).mpr hm
    have he : (Real.exp (-t))^2 = Real.exp (-2*t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), he] using h
  have hbound : (1-continuousDistance g t)*((n : ℝ)*Real.exp (-2*t)) ≤ 2*(V+W) := by
    calc
      _ ≤ (1-continuousDistance g t)*m^2 := mul_le_mul_of_nonneg_left hsq
        (sub_nonneg.mpr (continuousDistance_le_one g ht))
      _ ≤ (1-d)*m^2 := mul_le_mul_of_nonneg_right
        (sub_le_sub_left (tv_le_continuousDistance g t x) 1) (sq_nonneg m)
      _ ≤ 2*FiniteLaw.variance (continuousKernel (coupling g) t x) (linearObservable a) +
        2*FiniteLaw.variance (mass g 0) (linearObservable a) := hcommon
      _ ≤ 2*(V+W) := by linarith only [htrans a ha x, hstat a ha]
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : ((n : ℝ)*Real.exp (-2*t)) * (Real.exp (2*t)/n) = 1 := by
    rw [mul_div_assoc', mul_assoc (n : ℝ), ← Real.exp_add,
      show -2*t+2*t=0 by ring, Real.exp_zero, mul_one, div_self hnp.ne']
  have hmultiply := mul_le_mul_of_nonneg_right hbound
    (div_nonneg (Real.exp_nonneg (2*t)) hnp.le)
  rw [mul_assoc, heq, mul_one] at hmultiply
  rw [← mul_div_assoc] at hmultiply
  linarith only [hmultiply]

lemma exp_quarter_log_div {n : ℕ} (hn : 0 < n) :
    Real.exp (2*(Real.log n/4))/(n : ℝ) = dimensionDecay (1/2) n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he : (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn').symm
  conv_lhs => rhs; rw [he]
  rw [← Real.exp_sub]
  unfold dimensionDecay
  congr 1
  ring

theorem uniform_strong_lower_of_small_set
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ γ : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hγ : 0 < γ)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      1-2*(4*(Real.exp (A*d₀)/κ+1)+1/γ)*dimensionDecay (1/2) n ≤
        continuousDistance g (Real.log n/4) := by
  have hmom := uniform_gradient_moments_of_small_set G bad hκ hA hd₀ hdrift havoid
    (D := 1) (R := 1) (by norm_num) (by norm_num)
  filter_upwards [hgap, hmom, eventually_ge_atTop 1] with n hngap hnmom hn
  intro g hg
  have hn' : 0 < n := hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have htime : Real.log n/4 ∈ Set.Icc (0 : ℝ) (1*Real.log n) := by
    constructor <;> linarith only [hlog]
  have htrans (a : Fin n → ℝ) (ha : (∑ i, a i ^ 2) = 1) (x : Spin n) :
      FiniteLaw.variance (continuousKernel (coupling g) (Real.log n/4) x)
        (linearObservable a) ≤ 4*(Real.exp (A*d₀)/κ+1) := by
    simpa only [one_mul] using (hnmom g hg (linearObservable a)
      (fun y => by rw [unweightedGradient_linearObservable,ha]) (Real.log n/4) htime).1 x
  have hstat (a : Fin n → ℝ) (ha : (∑ i, a i ^ 2) = 1) :
      FiniteLaw.variance (mass g 0) (linearObservable a) ≤ 1/γ := by
    simpa only [ha] using stationary_linearObservable_variance_le g hγ (hngap g hg) a
  have h := continuousDistance_lower_of_linear_variances hn' g htime.1 htrans hstat
  rw [mul_div_assoc, exp_quarter_log_div hn'] at h
  exact h

theorem uniform_median_lower_of_small_set
    (G : ∀ n : ℕ, Set (Disorder n))
    (bad : ∀ n, Disorder n → Set (Spin n)) {κ A d₀ γ : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hγ : 0 < γ)
    (hgap : ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ D : ℝ, 0 < D → ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n,
      ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) (D*Real.log n), ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad n g then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ D m : ℝ, 0 < D → 0 < m →
      ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, ∀ u ∈ Set.Icc d₀ (D*Real.log n), ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad n g then 1 else 0) x ≤ dimensionDecay m n) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ G n, Real.log n/4 ≤ medianTime g := by
  have hlower := uniform_strong_lower_of_small_set G bad hκ hA hd₀ hγ hgap hdrift havoid
  have hdecay := (dimensionDecay_tendsto_zero (by norm_num : (0 : ℝ)<1/2)).const_mul
    (2*(4*(Real.exp (A*d₀)/κ+1)+1/γ))
  simp only [mul_zero] at hdecay
  filter_upwards [hlower, hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2)),
    eventually_ge_atTop 1] with n hnlow hdec hn
  intro g hg
  have ht : 0 ≤ Real.log n/4 := div_nonneg
    (Real.log_nonneg (by exact_mod_cast hn)) (by norm_num)
  have hdist : 1/2 < continuousDistance g (Real.log n/4) := by
    linarith only [hnlow g hg,hdec]
  exact le_of_lt (lt_of_not_ge (fun h => not_lt_of_ge ((medianTime_le_iff g ht).mp h) hdist))

end SKRatio.Calculus

end
end

end OAI
