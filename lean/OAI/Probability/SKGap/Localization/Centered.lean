import Mathlib
import OAI.Probability.SKGap.Localization.ScalarEigenfunction

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff

noncomputable def centered {n : ℕ} (J : Interaction n) (f : Observables n) : Observables n :=
  fun x => f x - gibbsExpectation J f

@[simp] lemma gibbsExpectation_centered {n : ℕ} (J : Interaction n) (f : Observables n) :
    gibbsExpectation J (centered J f) = 0 := by
  unfold centered
  rw [gibbsExpectation_sub, gibbsExpectation_const, sub_self]

@[simp] lemma halfDiff_centered {n : ℕ} (J : Interaction n) (f : Observables n)
    (i : Fin n) (x : Spin n) : halfDiff i (centered J f) x = halfDiff i f x := by
  simp only [halfDiff, centered]
  ring

lemma dirichlet_centered {n : ℕ} (J : Interaction n) (f g : Observables n) :
    dirichlet J (centered J f) (centered J g) = dirichlet J f g := by
  simp only [dirichlet, halfDiff_centered]

lemma centered_variance {n : ℕ} (J : Interaction n) (f : Observables n) :
    stationaryInner J (centered J f) (centered J f) = gibbsVariance J f := by
  simp only [stationaryInner, centered, gibbsVariance, pow_two]

lemma spectral_dirichlet {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (f : Observables n) :
    dirichlet J f f = ∑ a, spinEigenvalues J hJ hdiag a *
      ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J f) a) ^ 2 := by
  rw [← gibbs_dirichlet J hJ hdiag]
  change stationaryInner J f (-generator J f) = _
  rw [← spectral_parseval J hJ hdiag]
  simp_rw [spectral_generator_coordinates]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma centered_spectral_coordinate_zero {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (f : Observables n)
    (a : Fin (Fintype.card (Spin n))) (ha : spinEigenvalues J hJ hdiag a = 0) :
    (spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J (centered J f)) a = 0 := by
  have hg : generator J (scalarEigenfunction J hJ hdiag a) = 0 := by
    rw [generator_scalarEigenfunction, ha, neg_zero, zero_smul]
  have hc (x : Spin n) : scalarEigenfunction J hJ hdiag a x =
      scalarEigenfunction J hJ hdiag a (fun _ => false) :=
    constant_of_generator_zero J hJ hdiag _ hg x _
  rw [spectral_coordinates_inner]
  simp only [stationaryInner, hc, gibbsExpectation_mul_const, gibbsExpectation_centered,
    mul_zero]

lemma hasGap_of_positive_eigenvalues {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (γ : ℝ)
    (hγ : ∀ a, 0 < spinEigenvalues J hJ hdiag a → γ ≤ spinEigenvalues J hJ hdiag a) :
    HasGap J γ := by
  intro f
  rw [← centered_variance, ← dirichlet_centered J f f, spectral_dirichlet J hJ hdiag,
    ← spectral_parseval J hJ hdiag, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : spinEigenvalues J hJ hdiag a = 0
  · simp only [centered_spectral_coordinate_zero J hJ hdiag f a ha, mul_zero, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, le_refl]
  · have hp := lt_of_le_of_ne (spinEigenvalues_nonneg J hJ hdiag a) (Ne.symm ha)
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right (hγ a hp)
        (sq_nonneg ((spinEigenbasis J hJ hdiag).repr (gibbsEuclideanEquiv J (centered J f)) a))

theorem finite_gap_pos {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) :
    ∃ γ : ℝ, 0 < γ ∧ HasGap J γ := by
  let values : Finset ℝ := insert 1 ((Finset.univ.image (spinEigenvalues J hJ hdiag)).filter (0 < ·))
  have hne : values.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨values.min' hne, ?_, hasGap_of_positive_eigenvalues J hJ hdiag _ ?_⟩
  · have hm := Finset.min'_mem values hne
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h]; norm_num
    · exact (Finset.mem_filter.mp h).2
  · intro a ha
    apply Finset.min'_le
    exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ha⟩)

end SKGapCutoff

namespace SKGapCutoff

lemma scalarEigenfunction_centered {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) (ha : spinEigenvalues J hJ hdiag a ≠ 0) :
    gibbsExpectation J (scalarEigenfunction J hJ hdiag a) = 0 := by
  have hz := gibbs_generator_zero J hJ hdiag (scalarEigenfunction J hJ hdiag a)
  rw [generator_scalarEigenfunction] at hz
  change gibbsExpectation J (fun x => -spinEigenvalues J hJ hdiag a *
    scalarEigenfunction J hJ hdiag a x) = 0 at hz
  rw [gibbsExpectation_mul_const] at hz
  exact (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr ha)

lemma scalarEigenfunction_inner_self {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    (a : Fin (Fintype.card (Spin n))) :
    stationaryInner J (scalarEigenfunction J hJ hdiag a)
      (scalarEigenfunction J hJ hdiag a) = 1 := by
  rw [← gibbsEuclideanEquiv_inner, lift_scalarEigenfunction,
    real_inner_self_eq_norm_sq, (spinEigenbasis J hJ hdiag).orthonormal.norm_eq_one, one_pow]

lemma gap_le_positive_eigenvalue {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0)
    {γ : ℝ} (hγ : HasGap J γ) (a : Fin (Fintype.card (Spin n)))
    (ha : 0 < spinEigenvalues J hJ hdiag a) : γ ≤ spinEigenvalues J hJ hdiag a := by
  have hv : gibbsVariance J (scalarEigenfunction J hJ hdiag a) = 1 := by
    rw [gibbsVariance, scalarEigenfunction_centered J hJ hdiag a (ne_of_gt ha)]
    simp only [sub_zero, pow_two]
    exact scalarEigenfunction_inner_self J hJ hdiag a
  have hd : dirichlet J (scalarEigenfunction J hJ hdiag a)
      (scalarEigenfunction J hJ hdiag a) = spinEigenvalues J hJ hdiag a := by
    rw [← gibbs_dirichlet J hJ hdiag, generator_scalarEigenfunction]
    simp only [Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg]
    simp_rw [mul_left_comm (scalarEigenfunction J hJ hdiag a _) (spinEigenvalues J hJ hdiag a)]
    rw [gibbsExpectation_mul_const]
    change spinEigenvalues J hJ hdiag a * stationaryInner J
      (scalarEigenfunction J hJ hdiag a) (scalarEigenfunction J hJ hdiag a) = _
    rw [scalarEigenfunction_inner_self, mul_one]
  simpa only [hv, hd, mul_one] using hγ (scalarEigenfunction J hJ hdiag a)

theorem hasGap_iff_positive_eigenvalues {n : ℕ} (J : Interaction n)
    (hJ : ∀ i j, J i j = J j i) (hdiag : ∀ i, J i i = 0) (γ : ℝ) :
    HasGap J γ ↔ ∀ a, 0 < spinEigenvalues J hJ hdiag a →
      γ ≤ spinEigenvalues J hJ hdiag a :=
  ⟨fun h a ha => gap_le_positive_eigenvalue J hJ hdiag h a ha,
    hasGap_of_positive_eigenvalues J hJ hdiag γ⟩

theorem quenchedGap_iff_spectral (β : ℝ) : QuenchedGap β ↔
    ∃ γ : ℝ, 0 < γ ∧ Filter.Tendsto (fun n => (disorderLaw β n)
      {g | ∀ a, 0 < spinEigenvalues (sampledInteraction g)
        (sampledInteraction_symm g) (sampledInteraction_diag g) a →
        γ ≤ spinEigenvalues (sampledInteraction g)
          (sampledInteraction_symm g) (sampledInteraction_diag g) a})
      Filter.atTop (nhds 1) := by
  simp only [QuenchedGap, hasGap_iff_positive_eigenvalues (sampledInteraction _)
    (sampledInteraction_symm _) (sampledInteraction_diag _)]

end SKGapCutoff

end

end OAI
