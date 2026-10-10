import OAI.Probability.InvariantIsing.Arrays.ReplicaContractions

namespace OAI

/-! Exact finite spectral-block Ward identity for an arbitrary spin prior. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def coordinateWardTerm {N : ℕ} (w : Spin N → ℝ) (eig c : Fin N → ℝ)
    (i j : Fin N) (U : Orthogonal N) : ℝ :=
  gibbsAverage w (orbitHamiltonian eig c U)
      (fun σ => spinCoordinate U σ j ^ 2 - spinCoordinate U σ i ^ 2) +
    (eig i - eig j) *
      (gibbsAverage w (orbitHamiltonian eig c U) (fun σ => coordinateProduct i j U σ ^ 2) -
        gibbsAverage w (orbitHamiltonian eig c U) (coordinateProduct i j U) ^ 2)

lemma measurable_coordinateWardTerm {N : ℕ} (w : Spin N → ℝ) (eig c : Fin N → ℝ)
    (i j : Fin N) : Measurable (coordinateWardTerm w eig c i j) := by
  have hH := measurable_orbitHamiltonian eig c
  have hP (σ : Spin N) : Measurable (fun U : Orthogonal N => coordinateProduct i j U σ) :=
    (measurable_spinCoordinate σ i).mul (measurable_spinCoordinate σ j)
  exact (measurable_gibbsAverage w _ _ hH (fun σ =>
    ((measurable_spinCoordinate σ j).pow_const 2).sub
      ((measurable_spinCoordinate σ i).pow_const 2))).add
    (((measurable_gibbsAverage w _ _ hH (fun σ => (hP σ).pow_const 2)).sub
      ((measurable_gibbsAverage w _ _ hH hP).pow_const 2)).const_mul _)

lemma abs_coordinateWardTerm_le {N : ℕ} {w : Spin N → ℝ} (hw : GibbsReference w)
    (eig c : Fin N → ℝ) (i j : Fin N) (U : Orthogonal N) :
    |coordinateWardTerm w eig c i j U| ≤ N + |eig i - eig j| * (2 * (N : ℝ) ^ 2) := by
  let H := orbitHamiltonian eig c U
  have hP := abs_gibbsAverage_le hw H (coordinateProduct i j U)
    (abs_coordinateProduct_le i j U)
  have hP2 : |gibbsAverage w H (coordinateProduct i j U)| ^ 2 ≤ (N : ℝ) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hP 2
  have hQ := abs_gibbsAverage_le hw H (fun σ => coordinateProduct i j U σ ^ 2)
    (fun σ => by
      rw [abs_sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_coordinateProduct_le i j U σ) 2)
  have hD := abs_gibbsAverage_le hw H
    (fun σ => spinCoordinate U σ j ^ 2 - spinCoordinate U σ i ^ 2)
    (abs_coordinateSquareDifference_le i j U)
  have hV : |gibbsAverage w H (fun σ => coordinateProduct i j U σ ^ 2) -
      gibbsAverage w H (coordinateProduct i j U) ^ 2| ≤ 2 * (N : ℝ) ^ 2 := by
    have hP2' : |gibbsAverage w H (coordinateProduct i j U) ^ 2| ≤ (N : ℝ) ^ 2 := by
      simpa only [abs_sq, sq_abs] using hP2
    have hs := (abs_sub _ _).trans (add_le_add hQ hP2')
    linarith
  exact (abs_add_le _ _).trans (add_le_add hD (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hV (abs_nonneg _)))

lemma integrable_coordinateWardTerm {N : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ) (i j : Fin N) :
    Integrable (coordinateWardTerm w eig c i j) μ :=
  (integrable_const (N + |eig i - eig j| * (2 * (N : ℝ) ^ 2))).mono'
    (measurable_coordinateWardTerm w eig c i j).aestronglyMeasurable
    (ae_of_all _ fun U => by
      simpa only [Real.norm_eq_abs] using abs_coordinateWardTerm_le hw eig c i j U)

lemma coordinateWardTerm_block_sum {N : ℕ} (w : Spin N → ℝ) (eig c : Fin N → ℝ)
    (I J : Finset (Fin N)) (a b : ℝ)
    (hI : ∀ i ∈ I, eig i = a) (hJ : ∀ j ∈ J, eig j = b) (U : Orthogonal N) :
    (∑ i ∈ I, ∑ j ∈ J, coordinateWardTerm w eig c i j U) =
      (I.card : ℝ) * gibbsAverage w (orbitHamiltonian eig c U)
        (fun σ => blockOverlap (spinCoordinate U) J σ σ) -
      (J.card : ℝ) * gibbsAverage w (orbitHamiltonian eig c U)
        (fun σ => blockOverlap (spinCoordinate U) I σ σ) +
      (a - b) *
        (gibbsAverage w (orbitHamiltonian eig c U)
          (fun σ => blockOverlap (spinCoordinate U) I σ σ * blockOverlap (spinCoordinate U) J σ σ) -
         gibbsPairAverage w (orbitHamiltonian eig c U)
          (fun σ τ => blockOverlap (spinCoordinate U) I σ τ * blockOverlap (spinCoordinate U) J σ τ)) := by
  have he : (∑ i ∈ I, ∑ j ∈ J, coordinateWardTerm w eig c i j U) =
      ∑ i ∈ I, ∑ j ∈ J, (
        gibbsAverage w (orbitHamiltonian eig c U)
          (fun σ => spinCoordinate U σ j ^ 2 - spinCoordinate U σ i ^ 2) +
        (a - b) *
          (gibbsAverage w (orbitHamiltonian eig c U) (fun σ => coordinateProduct i j U σ ^ 2) -
            gibbsAverage w (orbitHamiltonian eig c U) (coordinateProduct i j U) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [coordinateWardTerm, hI i hi, hJ j hj]
  rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [coordinateProduct]
  rw [coordinate_difference_contraction, coordinate_fourth_contraction]
  have hm := coordinate_mean_square_contraction w (orbitHamiltonian eig c U)
    (spinCoordinate U) I J
  change (∑ i ∈ I, ∑ j ∈ J,
    gibbsAverage w (orbitHamiltonian eig c U) (coordinateProduct i j U) ^ 2) = _ at hm
  rw [hm]

/-- The exact unperturbed spectral-block rotation identity. The separate
small-perturbation and limiting GG arguments are not assumed here. -/
theorem block_ward_identity {N : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ k, |eig k| ≤ K)
    (I J : Finset (Fin N)) (hIJ : Disjoint I J) (a b : ℝ)
    (hI : ∀ i ∈ I, eig i = a) (hJ : ∀ j ∈ J, eig j = b) :
    (∫ U,
      (I.card : ℝ) * gibbsAverage w (orbitHamiltonian eig c U)
        (fun σ => blockOverlap (spinCoordinate U) J σ σ) -
      (J.card : ℝ) * gibbsAverage w (orbitHamiltonian eig c U)
        (fun σ => blockOverlap (spinCoordinate U) I σ σ) +
      (a - b) *
        (gibbsAverage w (orbitHamiltonian eig c U)
          (fun σ => blockOverlap (spinCoordinate U) I σ σ * blockOverlap (spinCoordinate U) J σ σ) -
         gibbsPairAverage w (orbitHamiltonian eig c U)
          (fun σ τ => blockOverlap (spinCoordinate U) I σ τ * blockOverlap (spinCoordinate U) J σ τ)) ∂μ) = 0 := by
  simp_rw [← coordinateWardTerm_block_sum w eig c I J a b hI hJ]
  rw [integral_finsetSum I (fun i _ => integrable_finsetSum J
    (fun j _ => integrable_coordinateWardTerm μ hw eig c i j))]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_finsetSum J (fun j _ => integrable_coordinateWardTerm μ hw eig c i j)]
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact Finset.disjoint_left.mp hIJ hi hj
  exact coordinate_ward_identity i j hij μ hw eig c K hK heig

end InvariantIsing

end

end OAI
