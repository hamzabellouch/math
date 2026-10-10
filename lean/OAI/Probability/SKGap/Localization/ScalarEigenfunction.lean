import Mathlib
import OAI.Probability.SKGap.Localization.Invert

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff
open MeasureTheory

lemma spectral_parseval {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (f g : Observables n) :
    (∑ a, (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J f) a *
      (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J g) a) = stationaryInner J f g := by
  have he := (spinEigenbasis J hJ hdiag).repr.inner_map_map
    (gibbsEuclideanEquiv J f) (gibbsEuclideanEquiv J g)
  rw [PiLp.inner_apply, gibbsEuclideanEquiv_inner] at he
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using he

lemma spectral_generator_coordinates {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (f : Observables n) (a : Fin (Fintype.card (Spin n))) :
    (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J (-generator J f)) a =
      spinEigenvalues J hJ hdiag a *
        (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J f) a := by
  rw [← negativeGeneratorEuclidean_lift]
  exact (negativeGeneratorEuclidean_symmetric J hJ hdiag).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace (gibbsEuclideanEquiv J f) a

lemma spinEigenvalues_nonneg {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) : 0 ≤ spinEigenvalues J hJ hdiag a := by
  have he : negativeGeneratorEuclidean J (spinEigenbasis J hJ hdiag a) =
      spinEigenvalues J hJ hdiag a • spinEigenbasis J hJ hdiag a :=
    (negativeGeneratorEuclidean_symmetric J hJ hdiag).apply_eigenvectorBasis finrank_euclideanSpace a
  have hp := negativeGeneratorEuclidean_nonneg J hJ hdiag (spinEigenbasis J hJ hdiag a)
  rw [he, inner_smul_right] at hp
  simpa only [real_inner_self_eq_norm_sq, (spinEigenbasis J hJ hdiag).orthonormal.norm_eq_one,
    one_pow, mul_one] using hp

lemma sum_spinSpectralCoefficient_sq {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (i : Fin n) :
    ∑ a, spinSpectralCoefficient J hJ hdiag i a ^ 2 = 1 := by
  have he := spectral_parseval J hJ hdiag (fun x => spin x i) (fun x => spin x i)
  simp only [stationaryInner, ← sq, spin_sq, gibbsExpectation_const] at he
  simpa only [spinSpectralCoefficient, pow_two] using he

lemma spinSpectralMass_nonneg {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) : 0 ≤ spinSpectralMass J hJ hdiag a :=
  div_nonneg (Finset.sum_nonneg (by intro i _; exact sq_nonneg _)) (Nat.cast_nonneg n)

lemma sum_spinSpectralMass {n : ℕ} (hn : 0 < n) (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) :
    ∑ a, spinSpectralMass J hJ hdiag a = 1 := by
  simp only [spinSpectralMass, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [sum_spinSpectralCoefficient_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (ne_of_gt (Nat.cast_pos.mpr hn))

theorem spinSpectralMeasure_probability {n : ℕ} (hn : 0 < n) (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) :
    IsProbabilityMeasure (spinSpectralMeasure J hJ hdiag) := by
  constructor
  simp only [spinSpectralMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (by intro a _; exact spinSpectralMass_nonneg J hJ hdiag a),
    sum_spinSpectralMass hn J hJ hdiag, ENNReal.ofReal_one]

lemma spinSpectralMeasure_integral {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (F : ℝ → ℝ) :
    (∫ u, F u ∂spinSpectralMeasure J hJ hdiag) =
      ∑ a, spinSpectralMass J hJ hdiag a * F (spinEigenvalues J hJ hdiag a) := by
  unfold spinSpectralMeasure
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (spinSpectralMass_nonneg J hJ hdiag _)]
  · intro a _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma spinSpectralMeasure_integral_trace {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (F : ℝ → ℝ) :
    (∫ u, F u ∂spinSpectralMeasure J hJ hdiag) =
      (∑ i, ∑ a, spinSpectralCoefficient J hJ hdiag i a ^ 2 *
        F (spinEigenvalues J hJ hdiag a)) / n := by
  rw [spinSpectralMeasure_integral]
  simp only [spinSpectralMass, div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]

lemma spin_first_moment_sum {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (i : Fin n) :
    (∑ a, spinSpectralCoefficient J hJ hdiag i a ^ 2 * spinEigenvalues J hJ hdiag a) =
      gibbsExpectation J (fun x => siteVariance J x i) := by
  have he := spectral_parseval J hJ hdiag (fun x => spin x i) (-generator J (fun x => spin x i))
  simp_rw [spectral_generator_coordinates] at he
  have hm : stationaryInner J (fun x => spin x i) (-generator J (fun x => spin x i)) =
      gibbsExpectation J (fun x => siteVariance J x i) := (spin_first_second J hJ hdiag i).1
  rw [hm] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro a _
  unfold spinSpectralCoefficient
  ring

lemma spin_second_moment_sum {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (i : Fin n) :
    (∑ a, spinSpectralCoefficient J hJ hdiag i a ^ 2 * spinEigenvalues J hJ hdiag a ^ 2) =
      gibbsExpectation J (fun x => siteVariance J x i) := by
  have he := spectral_parseval J hJ hdiag (-generator J (fun x => spin x i))
    (-generator J (fun x => spin x i))
  simp_rw [spectral_generator_coordinates] at he
  have hn : stationaryInner J (-generator J (fun x => spin x i)) (-generator J (fun x => spin x i)) =
      stationaryInner J (generator J (fun x => spin x i)) (generator J (fun x => spin x i)) := by
    simp only [stationaryInner, Pi.neg_apply, neg_mul_neg]
  rw [hn, (spin_first_second J hJ hdiag i).2] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro a _
  unfold spinSpectralCoefficient
  ring

theorem spinSpectralMeasure_moments {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) :
    (∫ u, u ∂spinSpectralMeasure J hJ hdiag) =
      (∑ i, gibbsExpectation J (fun x => siteVariance J x i)) / n ∧
    (∫ u, u ^ 2 ∂spinSpectralMeasure J hJ hdiag) =
      (∑ i, gibbsExpectation J (fun x => siteVariance J x i)) / n := by
  constructor
  · rw [spinSpectralMeasure_integral_trace]
    simp_rw [spin_first_moment_sum]
  · rw [spinSpectralMeasure_integral_trace]
    simp_rw [spin_second_moment_sum]

noncomputable def scalarEigenfunction {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) : Observables n :=
  (gibbsEuclideanEquiv J).symm (spinEigenbasis J hJ hdiag a)

@[simp] lemma lift_scalarEigenfunction {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) :
    gibbsEuclideanEquiv J (scalarEigenfunction J hJ hdiag a) = spinEigenbasis J hJ hdiag a :=
  (gibbsEuclideanEquiv J).apply_symm_apply _

lemma generator_scalarEigenfunction {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) :
    generator J (scalarEigenfunction J hJ hdiag a) =
      -spinEigenvalues J hJ hdiag a • scalarEigenfunction J hJ hdiag a := by
  have he : negativeGeneratorEuclidean J (spinEigenbasis J hJ hdiag a) =
      spinEigenvalues J hJ hdiag a • spinEigenbasis J hJ hdiag a :=
    (negativeGeneratorEuclidean_symmetric J hJ hdiag).apply_eigenvectorBasis finrank_euclideanSpace a
  have hf : -generator J (scalarEigenfunction J hJ hdiag a) =
      spinEigenvalues J hJ hdiag a • scalarEigenfunction J hJ hdiag a := by
    apply (gibbsEuclideanEquiv J).injective
    rw [← negativeGeneratorEuclidean_lift, map_smul, lift_scalarEigenfunction]
    exact he
  simpa only [neg_neg, neg_smul] using congrArg Neg.neg hf

lemma semigroup_scalarEigenfunction {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) (t : ℝ) :
    semigroup J t (scalarEigenfunction J hJ hdiag a) =
      Real.exp (-spinEigenvalues J hJ hdiag a * t) • scalarEigenfunction J hJ hdiag a := by
  apply exp_apply_of_eigenvector
  rw [smul_apply]
  change t • generator J (scalarEigenfunction J hJ hdiag a) = _
  rw [generator_scalarEigenfunction, smul_smul, mul_comm]

lemma spectral_coordinates_inner {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (f : Observables n) (a : Fin (Fintype.card (Spin n))) :
    (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J f) a =
      stationaryInner J (scalarEigenfunction J hJ hdiag a) f := by
  rw [OrthonormalBasis.repr_apply_apply, ← lift_scalarEigenfunction J hJ hdiag a,
    gibbsEuclideanEquiv_inner]

lemma spectral_semigroup_coordinates {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (f : Observables n) (t : ℝ) (a : Fin (Fintype.card (Spin n))) :
    (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J (semigroup J t f)) a =
      Real.exp (-spinEigenvalues J hJ hdiag a * t) *
        (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J f) a := by
  rw [spectral_coordinates_inner, spectral_coordinates_inner,
    scalar_semigroup_symmetric J hJ hdiag, semigroup_scalarEigenfunction]
  simp only [stationaryInner, Pi.smul_apply, smul_eq_mul, mul_assoc,
    gibbsExpectation_mul_const]

theorem spinSpectralMeasure_correlation {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (t : ℝ) :
    (∫ u, Real.exp (-u*t) ∂spinSpectralMeasure J hJ hdiag) =
      (∑ i, stationaryInner J (fun x => spin x i) (semigroup J t (fun x => spin x i))) / n := by
  rw [spinSpectralMeasure_integral_trace]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← spectral_parseval J hJ hdiag]
  simp_rw [spectral_semigroup_coordinates]
  apply Finset.sum_congr rfl
  intro a _
  unfold spinSpectralCoefficient
  ring

lemma replace_eq_of_halfDiff_zero {n : ℕ} (f : Observables n)
    (h : ∀ i x, halfDiff i f x = 0) (x : Spin n) (i : Fin n) (b : Bool) :
    f (replace x i b) = f x := by
  have hh := h i x
  have hp : f (replace x i true) = f (replace x i false) := by
    unfold halfDiff at hh
    linarith
  have hs := congrArg f (replace_self x i)
  cases hi : x i <;> cases b <;> simp_all

lemma constant_of_halfDiff_zero {n : ℕ} (f : Observables n)
    (h : ∀ i x, halfDiff i f x = 0) (x y : Spin n) : f x = f y := by
  let blend (s : Finset (Fin n)) : Spin n := fun i => if i ∈ s then y i else x i
  have hs (s : Finset (Fin n)) : f (blend s) = f x := by
    induction s using Finset.induction_on with
    | empty => simp [blend]
    | @insert i s hi ih =>
      have he : blend (insert i s) = replace (blend s) i (y i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [blend]
        · simp [blend, replace, hj]
      rw [he, replace_eq_of_halfDiff_zero f h, ih]
  have hu := hs Finset.univ
  simpa only [blend, Finset.mem_univ, ↓reduceIte] using hu.symm

lemma halfDiff_zero_of_dirichlet_zero {n : ℕ} (J : Interaction n) (f : Observables n)
    (h : dirichlet J f f = 0) (i : Fin n) (x : Spin n) : halfDiff i f x = 0 := by
  have hs (y : Spin n) (j : Fin n) : 0 ≤ siteVariance J y j * halfDiff j f y * halfDiff j f y := by
    rw [mul_assoc]
    exact mul_nonneg (le_of_lt (siteVariance_pos J y j)) (mul_self_nonneg _)
  have hx : gibbs J x * (∑ j, siteVariance J x j * halfDiff j f x * halfDiff j f x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (by
      intro y _
      exact mul_nonneg (le_of_lt (gibbs_pos J y)) (Finset.sum_nonneg (by intro j _; exact hs y j)))).mp h x (Finset.mem_univ _)
  have hrow := (mul_eq_zero.mp hx).resolve_left (ne_of_gt (gibbs_pos J x))
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (by intro j _; exact hs x j)).mp hrow i (Finset.mem_univ _)
  rw [mul_assoc] at hi
  exact mul_self_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left (ne_of_gt (siteVariance_pos J x i)))

lemma constant_of_generator_zero {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (f : Observables n)
    (h : generator J f = 0) (x y : Spin n) : f x = f y := by
  have hd : dirichlet J f f = 0 := by
    rw [← gibbs_dirichlet J hJ hdiag, h]
    simp [gibbsExpectation]
  exact constant_of_halfDiff_zero f (fun i x => halfDiff_zero_of_dirichlet_zero J f hd i x) x y

lemma spinSpectralCoefficient_zero_eigenvalue {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) (ha : spinEigenvalues J hJ hdiag a = 0) (i : Fin n) :
    spinSpectralCoefficient J hJ hdiag i a = 0 := by
  have hg : generator J (scalarEigenfunction J hJ hdiag a) = 0 := by
    rw [generator_scalarEigenfunction, ha, neg_zero, zero_smul]
  have hc (x : Spin n) : scalarEigenfunction J hJ hdiag a x =
      scalarEigenfunction J hJ hdiag a (fun _ => false) :=
    constant_of_generator_zero J hJ hdiag _ hg x _
  unfold spinSpectralCoefficient
  rw [spectral_coordinates_inner]
  unfold stationaryInner
  simp_rw [hc]
  rw [gibbsExpectation_mul_const, gibbs_spin_centered, mul_zero]

theorem spinSpectralMeasure_nonpositive {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) :
    spinSpectralMeasure J hJ hdiag (Set.Iic 0) = 0 := by
  simp only [spinSpectralMeasure, Measure.finsetSum_apply, Measure.smul_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : spinEigenvalues J hJ hdiag a ≤ 0
  · have hz := le_antisymm ha (spinEigenvalues_nonneg J hJ hdiag a)
    have hw : spinSpectralMass J hJ hdiag a = 0 := by
      simp [spinSpectralMass, spinSpectralCoefficient_zero_eigenvalue J hJ hdiag a hz]
    simp [hw]
  · have he : Measure.dirac (spinEigenvalues J hJ hdiag a) (Set.Iic 0) = 0 := by
      simp [Set.mem_Iic, ha]
    rw [he]
    exact smul_zero _

end SKGapCutoff

end

end OAI
