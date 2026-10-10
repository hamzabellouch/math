import OAI.Probability.InvariantIsing.Arrays.TensorTruncatedDiagonalWard
import OAI.Probability.InvariantIsing.Arrays.TensorWardCorrectionBound

namespace OAI

/-! The normalized one-replica Gaussian Ward correction is quadratic in
the perturbation scale, uniformly in the finite leaf restriction. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*}

def tensorRestrictionDiagonalWardContraction {N m n : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (J K : Finset (Fin N)) (x : S → Spin N × LabeledLeaf n) (s p q : S) : ℝ :=
  tensorWardPerturbationError U I degree treeDegree n u J K (x s).1 (x s).1 (x p) (x q)

lemma tensorRestrictionDiagonalWardContraction_eq {N m n : ℕ} (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (x : S → Spin N × LabeledLeaf n) (s p q : S) :
    tensorRestrictionDiagonalWardContraction (specialToOrthogonal U) I degree treeDegree u J K x s p q =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        tensorRestrictionDiagonalObservable i j x U s *
          tensorRestrictionCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x i j U p q := by
  exact (tensorNamespacedPlane_contraction_eq (specialToOrthogonal U) I degree treeDegree n u h hh h0
    J K (x s).1 (x s).1 (x p) (x q)).symm

lemma tensorRestrictionDiagonalWardCorrection_eq [Fintype S] {N m n : ℕ} (U : SpecialOrthogonal N)
    (w H : S → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (u : Fin N → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (x : S → Spin N × LabeledLeaf n) :
    gibbsKernelCorrection w H
      (tensorRestrictionDiagonalWardContraction (specialToOrthogonal U) I degree treeDegree u J K x) =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        gaussianWardCorrection w H (tensorRestrictionDiagonalObservable i j x U)
          (tensorRestrictionCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x i j U) := by
  have he : tensorRestrictionDiagonalWardContraction (specialToOrthogonal U) I degree treeDegree u J K x =
      fun s p q => ∑ a ∈ J ×ˢ K, (N : ℝ)⁻¹ ^ 2 *
        (tensorRestrictionDiagonalObservable a.1 a.2 x U s *
          tensorRestrictionCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x a.1 a.2 U p q) := by
    funext s p q
    rw [tensorRestrictionDiagonalWardContraction_eq U I degree treeDegree u h hh h0 J K x s p q]
    simp only [Finset.sum_product, ← Finset.mul_sum]
  rw [he, gibbsKernelCorrection_finset_sum]
  simp only [gibbsKernelCorrection_product, Finset.sum_product, Finset.mul_sum]

/-- The exact one-replica Gaussian correction, with its single covariance
kernel rather than a doubled Hamiltonian coefficient. -/
theorem tensorRestriction_actualDiagonalWardCorrection_abs_le [Fintype S] {N m n : ℕ}
    (hN : 0 < N) (U : SpecialOrthogonal N) {w : S → ℝ} (hw : GibbsReference w) (H : S → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (x : S → Spin N × LabeledLeaf n) :
    |(N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
      gaussianWardCorrection w H (tensorRestrictionDiagonalObservable i j x U)
        (tensorRestrictionCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
          (fun a => tensorPathProfile I degree n treeDegree h a) x i j U)| ≤
      48 * D * perturbationScale N ^ 2 := by
  rw [← tensorRestrictionDiagonalWardCorrection_eq U w H I degree treeDegree u h hh h0 J K x]
  have hb (s p q : S) :
      |tensorRestrictionDiagonalWardContraction (specialToOrthogonal U) I degree treeDegree u J K x s p q| ≤
        8 * D * perturbationScale N ^ 2 :=
    tensorWardPerturbationError_abs_le hN (specialToOrthogonal U) I degree treeDegree n u hu D hD hdegree
      J K (x s).1 (x s).1 (x p) (x q)
  exact (gibbsKernelCorrection_abs_le hw H _ hb).trans_eq (by ring)

end InvariantIsing

end

end OAI
