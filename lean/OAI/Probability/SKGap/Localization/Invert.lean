import Mathlib
import OAI.Probability.SKGap.Localization.StationaryInner

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff

def invert {n : ℕ} (x : Spin n) : Spin n := fun i => !x i
@[simp] lemma invert_invert {n : ℕ} (x : Spin n) : invert (invert x) = x := by
  funext i; simp [invert]
@[simp] lemma spin_invert {n : ℕ} (x : Spin n) (i : Fin n) :
    spin (invert x) i = -spin x i := by
  cases hi : x i <;> simp [spin, invert, hi]
def invertEquiv (n : ℕ) : Spin n ≃ Spin n where
  toFun := invert
  invFun := invert
  left_inv := invert_invert
  right_inv := invert_invert
lemma sum_invert {n : ℕ} (f : Spin n → ℝ) : (∑ x, f (invert x)) = ∑ x, f x :=
  (invertEquiv n).sum_comp f
@[simp] lemma energy_invert {n : ℕ} (J : Interaction n) (x : Spin n) :
    energy J (invert x) = energy J x := by
  simp [energy]
@[simp] lemma gibbs_invert {n : ℕ} (J : Interaction n) (x : Spin n) :
    gibbs J (invert x) = gibbs J x := by simp [gibbs]

theorem gibbs_spin_centered {n : ℕ} (J : Interaction n) (i : Fin n) :
    gibbsExpectation J (fun x => spin x i) = 0 := by
  have h := sum_invert (fun x => gibbs J x * spin x i)
  simp only [gibbs_invert, spin_invert, mul_neg, Finset.sum_neg_distrib] at h
  unfold gibbsExpectation
  linarith

@[simp] lemma generator_spin {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    generator J (fun y => spin y i) x = mean J x i - spin x i := by
  simp [generator, halfDiff_spin]

lemma siteVariance_pos {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    0 < siteVariance J x i := by
  have hl := Real.neg_one_lt_tanh (field J x i)
  have hu := Real.tanh_lt_one (field J x i)
  unfold siteVariance mean
  nlinarith
lemma siteVariance_le_one {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    siteVariance J x i ≤ 1 := by
  unfold siteVariance
  nlinarith [sq_nonneg (mean J x i)]

lemma dirichlet_nonneg {n : ℕ} (J : Interaction n) (f : Observables n) :
    0 ≤ dirichlet J f f := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (le_of_lt (gibbs_pos J x))
  apply Finset.sum_nonneg
  intro i _
  nlinarith [mul_nonneg (le_of_lt (siteVariance_pos J x i)) (sq_nonneg (halfDiff i f x))]

theorem spin_first_second {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (i : Fin n) :
    stationaryInner J (fun x => spin x i) (fun x => -generator J (fun y => spin y i) x) =
      gibbsExpectation J (fun x => siteVariance J x i) ∧
    stationaryInner J (generator J (fun x => spin x i)) (generator J (fun x => spin x i)) =
      gibbsExpectation J (fun x => siteVariance J x i) := by
  constructor
  · rw [stationaryInner, gibbs_dirichlet J hJ hdiag]
    simp [dirichlet, halfDiff_spin]
  · have hm := gibbs_coordinate_mean J hJ hdiag i (fun x => mean J x i)
      (by intro x; exact mean_flip J hdiag x i)
    simp only [stationaryInner, gibbsExpectation, generator_spin]
    have he (x : Spin n) :
        gibbs J x * ((mean J x i - spin x i) * (mean J x i - spin x i)) =
        gibbs J x * siteVariance J x i +
        2 * (gibbs J x * mean J x i * mean J x i - gibbs J x * spin x i * mean J x i) := by
      unfold siteVariance
      nlinarith [congrArg (fun a : ℝ => gibbs J x * a) (spin_sq x i)]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hm]
    ring

noncomputable def gibbsEuclideanEquiv {n : ℕ} (J : Interaction n) :
    Observables n ≃ₗ[ℝ] EuclideanSpace ℝ (Spin n) where
  toFun f := WithLp.toLp 2 (fun x => Real.sqrt (gibbs J x) * f x)
  invFun u x := u x / Real.sqrt (gibbs J x)
  left_inv f := by
    funext x
    exact mul_div_cancel_left₀ (f x) (ne_of_gt (Real.sqrt_pos.2 (gibbs_pos J x)))
  right_inv u := by
    ext x
    exact mul_div_cancel₀ (u x) (ne_of_gt (Real.sqrt_pos.2 (gibbs_pos J x)))
  map_add' f g := by ext x; simp [mul_add]
  map_smul' a f := by ext x; simp [mul_left_comm]

@[simp] lemma gibbsEuclideanEquiv_apply {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    gibbsEuclideanEquiv J f x = Real.sqrt (gibbs J x) * f x := rfl
@[simp] lemma gibbsEuclideanEquiv_symm_apply {n : ℕ} (J : Interaction n)
    (u : EuclideanSpace ℝ (Spin n)) (x : Spin n) :
    (gibbsEuclideanEquiv J).symm u x = u x / Real.sqrt (gibbs J x) := rfl

lemma gibbsEuclideanEquiv_inner {n : ℕ} (J : Interaction n) (f g : Observables n) :
    inner (𝕜 := ℝ) (gibbsEuclideanEquiv J f) (gibbsEuclideanEquiv J g) = stationaryInner J f g := by
  rw [PiLp.inner_apply]
  unfold stationaryInner gibbsExpectation
  apply Finset.sum_congr rfl
  intro x _
  simp only [gibbsEuclideanEquiv_apply, RCLike.inner_apply, conj_trivial]
  have hs := Real.sq_sqrt (le_of_lt (gibbs_pos J x))
  nlinarith only [congrArg (fun a : ℝ => a * f x * g x) hs]

noncomputable def negativeGeneratorEuclidean {n : ℕ} (J : Interaction n) :
    EuclideanSpace ℝ (Spin n) →ₗ[ℝ] EuclideanSpace ℝ (Spin n) :=
  (gibbsEuclideanEquiv J).toLinearMap.comp
    ((-generatorLM J).comp (gibbsEuclideanEquiv J).symm.toLinearMap)

lemma negativeGeneratorEuclidean_lift {n : ℕ} (J : Interaction n) (f : Observables n) :
    negativeGeneratorEuclidean J (gibbsEuclideanEquiv J f) =
      gibbsEuclideanEquiv J (-generator J f) := by
  simp [negativeGeneratorEuclidean, generatorLM]

lemma negativeGeneratorEuclidean_symmetric {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) :
    (negativeGeneratorEuclidean J).IsSymmetric := by
  intro u v
  obtain ⟨f, rfl⟩ := (gibbsEuclideanEquiv J).surjective u
  obtain ⟨g, rfl⟩ := (gibbsEuclideanEquiv J).surjective v
  rw [negativeGeneratorEuclidean_lift, negativeGeneratorEuclidean_lift,
    gibbsEuclideanEquiv_inner, gibbsEuclideanEquiv_inner]
  have he := scalar_generator_symmetric J hJ hdiag f g
  simp only [stationaryInner, gibbsExpectation] at he ⊢
  simpa only [Pi.neg_apply, neg_mul, mul_neg, Finset.sum_neg_distrib] using congrArg Neg.neg he.symm

lemma negativeGeneratorEuclidean_nonneg {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (u : EuclideanSpace ℝ (Spin n)) :
    0 ≤ inner (𝕜 := ℝ) u (negativeGeneratorEuclidean J u) := by
  obtain ⟨f, rfl⟩ := (gibbsEuclideanEquiv J).surjective u
  rw [negativeGeneratorEuclidean_lift, gibbsEuclideanEquiv_inner]
  change 0 ≤ gibbsExpectation J (fun x => f x * -generator J f x)
  rw [gibbs_dirichlet J hJ hdiag]
  exact dirichlet_nonneg J f

noncomputable def spinEigenvalues {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) :
    Fin (Fintype.card (Spin n)) → ℝ :=
  (negativeGeneratorEuclidean_symmetric J hJ hdiag).eigenvalues finrank_euclideanSpace

noncomputable def spinEigenbasis {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) :
    OrthonormalBasis (Fin (Fintype.card (Spin n))) ℝ (EuclideanSpace ℝ (Spin n)) :=
  (negativeGeneratorEuclidean_symmetric J hJ hdiag).eigenvectorBasis finrank_euclideanSpace

noncomputable def spinSpectralCoefficient {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (i : Fin n) (a : Fin (Fintype.card (Spin n))) : ℝ :=
  (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J (fun x => spin x i)) a

noncomputable def spinSpectralMass {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) : ℝ :=
  (∑ i, spinSpectralCoefficient J hJ hdiag i a ^ 2) / n

noncomputable def spinSpectralMeasure {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) : MeasureTheory.Measure ℝ :=
  ∑ a : Fin (Fintype.card (Spin n)),
    ENNReal.ofReal (spinSpectralMass J hJ hdiag a) •
      MeasureTheory.Measure.dirac (spinEigenvalues J hJ hdiag a)

end SKGapCutoff

end

end OAI
