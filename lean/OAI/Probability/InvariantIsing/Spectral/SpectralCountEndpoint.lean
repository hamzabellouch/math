import OAI.Probability.InvariantIsing.Spectral.SpectralGroupMass
import OAI.Probability.InvariantIsing.Pressure.GibbsSecant

namespace OAI

/-! Endpoint derivative bounds for changing spectral multiplicities. The
fraction estimate uses the actual Haar Gibbs projection masses. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma integrable_gibbsSpectralDirection {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c delta : Fin N → ℝ) :
    Integrable (fun U => gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2)) μ := by
  have he (U : SpecialOrthogonal N) :
      gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2) =
      ∑ i, delta i * gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2) := by
    simp only [gibbsAverage, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_gibbsCoordinateSquare μ hw eig c i).const_mul _

lemma integral_gibbsSpectralDirection {N : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c delta : Fin N → ℝ) :
    (∫ U, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2) ∂μ) =
      ∑ i, delta i * meanCoordinateSquare μ w eig c i := by
  have he (U : SpecialOrthogonal N) :
      gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2) =
      ∑ i, delta i * gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
        (fun σ => spinCoordinate (specialToOrthogonal U) σ i ^ 2) := by
    simp only [gibbsAverage, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_gibbsCoordinateSquare μ hw eig c i).const_mul _)]
  simp only [integral_const_mul, meanCoordinateSquare]

lemma abs_integral_gibbsSpectralDirection_le {N m : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : Spin N → ℝ} (hw : GibbsReference w) (eig c delta : Fin N → ℝ)
    (label : Fin N → Fin m) (hlabel : Function.Surjective label)
    (lam : Fin m → ℝ) (hspectral : ∀ i, eig i = lam (label i))
    (changed : Finset (Fin N)) (hzero : ∀ i, i ∉ changed → delta i = 0)
    (L r : ℝ) (hL : 0 ≤ L) (hdelta : ∀ i, |delta i| ≤ L)
    (hcount : ∀ a, ((changed.filter fun i => label i = a).card : ℝ) ≤
      r * ((Finset.univ.filter fun i => label i = a).card : ℝ)) :
    |∫ U, gibbsAverage w (orbitHamiltonian eig c (specialToOrthogonal U))
      (fun σ => ∑ i, delta i * spinCoordinate (specialToOrthogonal U) σ i ^ 2) ∂μ| ≤ L * r * N := by
  let rep : Fin m → Fin N := fun a => (hlabel a).choose
  have hrep a : label (rep a) = a := (hlabel a).choose_spec
  let mass : Fin m → ℝ := fun a => meanCoordinateSquare μ w eig c (rep a)
  have hm a : 0 ≤ mass a := meanCoordinateSquare_nonneg μ hw eig c (rep a)
  have he i : meanCoordinateSquare μ w eig c i = mass (label i) := by
    apply meanCoordinateSquare_eq_of_eigenvalue_eq μ hw eig c
    rw [hspectral i, hspectral (rep (label i)), hrep]
  rw [integral_gibbsSpectralDirection μ hw]
  simp_rw [he]
  have hs : (∑ i, mass (label i)) = N := by
    simp_rw [← he]
    exact sum_meanCoordinateSquare μ hw eig c
  simpa only [hs] using abs_weighted_spectral_change_le label changed mass hm delta
    hzero L r hL hdelta hcount

end InvariantIsing

end

end OAI
