import OAI.Probability.InvariantIsing.Arrays.CoordinateWard
import OAI.Probability.InvariantIsing.Haar.SpecialPlaneRotation

namespace OAI

/-! Haar-averaged squared projections are constant within each eigenspace.
This follows from the finite coordinate Ward identity and holds for any
fixed nonzero nonnegative spin prior, including deterministic fields. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def meanCoordinateSquare {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (w : Spin N → ℝ) (eig c : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∫ U, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
    (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2) ∂μ

lemma integrable_gibbsCoordinateSquare {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ) (i : Fin N) :
    Integrable (fun U => gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2)) μ := by
  apply (integrable_const (N : ℝ)).mono'
    (measurable_gibbsAverage w _ _ (fun σ => (measurable_orbitHamiltonian eig c σ).comp measurable_specialToOrthogonal)
      (fun σ => ((measurable_spinCoordinate σ i).pow_const 2).comp measurable_specialToOrthogonal)).aestronglyMeasurable
  filter_upwards [] with U
  rw [Real.norm_eq_abs]
  exact abs_gibbsAverage_le hw _ _ (fun σ => by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact spinCoordinate_sq_le (specialToOrthogonal U) σ i)

lemma meanCoordinateSquare_nonneg {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) {w : Spin N → ℝ} (hw : GibbsReference w)
    (eig c : Fin N → ℝ) (i : Fin N) :
    0 ≤ meanCoordinateSquare μ w eig c i := by
  apply integral_nonneg
  intro U
  exact Finset.sum_nonneg fun σ _ =>
    mul_nonneg (finiteGibbs_nonneg hw _ σ) (sq_nonneg _)

lemma sum_meanCoordinateSquare {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ) :
    ∑ i, meanCoordinateSquare μ w eig c i = N := by
  unfold meanCoordinateSquare
  rw [← integral_finsetSum _ (fun i _ => integrable_gibbsCoordinateSquare μ hw eig c i)]
  have he (U : SpecialOrthogonal N) :
      (∑ i, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2)) = N := by
    simp only [gibbsAverage]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hnorm (σ : Spin N) : ∑ i, spinCoordinate (specialToOrthogonal U) σ i ^ 2 = N :=
      rotated_spin_sq_sum (specialRotation U) σ
    simp_rw [hnorm]
    rw [← Finset.sum_mul, finiteGibbs_sum hw, one_mul]
  simp only [he, integral_const, probReal_univ, one_smul]

lemma meanCoordinateSquare_eq_of_eigenvalue_eq {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (i j : Fin N) (hij : eig i = eig j) :
    meanCoordinateSquare μ w eig c i = meanCoordinateSquare μ w eig c j := by
  by_cases heq : i = j
  · rw [heq]
  let R := specialPlaneRotation i j
  let H := fun U : SpecialOrthogonal N => orbitHamiltonian eig c (specialToOrthogonal U)
  let A := fun U : SpecialOrthogonal N => coordinateProduct i j (specialToOrthogonal U)
  let dA := fun t U σ => spinCoordinate (specialToOrthogonal (R t * U)) σ j ^ 2 -
    spinCoordinate (specialToOrthogonal (R t * U)) σ i ^ 2
  have hR : R 0 = 1 := specialPlaneRotation_zero i j
  have hHm (σ : Spin N) : Measurable (fun U => H U σ) :=
    (measurable_orbitHamiltonian eig c σ).comp measurable_specialToOrthogonal
  have hAm (σ : Spin N) : Measurable (fun U => A U σ) :=
    ((measurable_spinCoordinate σ i).mul (measurable_spinCoordinate σ j)).comp
      measurable_specialToOrthogonal
  have hdAm (σ : Spin N) : Measurable (fun U => dA 0 U σ) := by
    simp only [dA, hR, one_mul]
    exact (((measurable_spinCoordinate σ j).pow_const 2).sub
      ((measurable_spinCoordinate σ i).pow_const 2)).comp measurable_specialToOrthogonal
  have hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => H (R s * U) σ) 0 t := by
    intro U t _ σ
    simpa only [H, R, map_mul, specialToOrthogonal_planeRotation, orbitHamiltonian,
      hij, sub_self, zero_mul] using
      (hasDerivAt_planeRotation_energy i j (specialToOrthogonal U) eig σ t).add_const
        (fieldEnergy c σ)
  have hAd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => A (R s * U) σ) (dA t U σ) t := by
    intro U t _ σ
    simpa only [A, R, dA, map_mul, specialToOrthogonal_planeRotation] using
      hasDerivAt_plane_coordinateProduct i j heq (specialToOrthogonal U) σ t
  have h := integral_special_gibbs_rotation_identity μ R hR hw H A hHm hAm
    (fun _ _ _ => 0) dA (fun _ => measurable_const) hdAm hHd hAd
    (N : ℝ) 0 (N : ℝ) (Nat.cast_nonneg _)
    (fun U σ => abs_coordinateProduct_le i j (specialToOrthogonal U) σ)
    (fun _ _ _ _ => by simp)
    (fun U t _ σ => abs_coordinateSquareDifference_le i j (specialToOrthogonal (R t * U)) σ)
  simp only [dA, hR, one_mul, H, mul_zero, gibbsAverage, Finset.sum_const_zero,
    add_zero, sub_zero] at h
  change (∫ U, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
    (fun σ => spinCoordinate (specialToOrthogonal U) σ j ^ 2 -
      spinCoordinate (specialToOrthogonal U) σ i ^ 2) ∂μ) = 0 at h
  have he (U : SpecialOrthogonal N) :
      gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => spinCoordinate (specialToOrthogonal U) σ j ^ 2 - spinCoordinate (specialToOrthogonal U) σ i ^ 2) =
      gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U)) (fun σ => spinCoordinate (specialToOrthogonal U) σ j ^ 2) -
        gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U)) (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2) := by
    simp only [gibbsAverage, mul_sub, Finset.sum_sub_distrib]
  simp_rw [he] at h
  rw [integral_sub (integrable_gibbsCoordinateSquare μ hw eig c j)
    (integrable_gibbsCoordinateSquare μ hw eig c i)] at h
  exact (sub_eq_zero.mp h).symm

end InvariantIsing

end

end OAI
