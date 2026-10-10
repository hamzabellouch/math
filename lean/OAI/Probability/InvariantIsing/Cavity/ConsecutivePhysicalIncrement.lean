import OAI.Probability.InvariantIsing.Cavity.ConsecutiveMinimumSequence
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPriorPressure
import OAI.Probability.InvariantIsing.Cavity.CavityOrientedFamily

namespace OAI

/-! The consecutive prior increment is the original physical constrained
rotation increment, with the same base perturbation in both dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma cavityBaseAmplitude_extend {N n : ℕ} (u : Fin N → ℝ) :
    cavityBaseAmplitude (fun i : Fin (N+n) => cavityBaseAmplitude u i) = cavityBaseAmplitude u := by
  funext j
  by_cases hj : j < N+n
  · simp only [cavityBaseAmplitude, dite_eq_left hj]
  · have hN : ¬j < N := by omega
    simp only [cavityBaseAmplitude, dite_eq_right hj, dite_eq_right hN]

def repeatedRotationIncrement {m n : ℕ}
    (μ : (N : ℕ) → Measure (Orthogonal N))
    (eig : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (C : Finset (Spin n)) (hC : C.Nonempty) (K : ℕ)
    (u : Fin (K*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  let N := K*n
  let S := consecutiveBlockConstraint n K C
  let hS := consecutiveBlockConstraint_nonempty C hC
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  (∫ z, restrictedRotationLogMean (cavityProductSlice S C)
    (cavityProductSlice_nonempty S hS C hC) z.2
    (diagonalPerturbedEigenvalues (eig (N+n)) (I (N+n)) v 1)
    (I (N+n)) (cavityBaseAmplitude u) z.1 ∂(μ (N+n)).prod θ) -
  ∫ z, restrictedRotationLogMean S hS z.2
    (diagonalPerturbedEigenvalues (eig N) (I N) v 1)
    (I N) (cavityBaseAmplitude u) z.1 ∂(μ N).prod θ

lemma consecutive_prior_increment_physical
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m n q : ℕ} (μ : (N : ℕ) → Measure (Orthogonal N))
    [∀ N, IsProbabilityMeasure (μ N)] [∀ N, (μ N).IsMulRightInvariant]
    (eig : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (u : (r : ℕ) → Fin ((q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r i, u r i ∈ Set.Icc (1 : ℝ) 2) (r : ℕ) (hN : 3 ≤ (q+r)*n) :
    consecutivePriorIncrement (cavityOrientedFamily μ) eig (fun _ _ => 0) I q C hC u v r =
      repeatedRotationIncrement μ eig I C hC (q+r) (u r) (v r) := by
  let N := (q+r)*n
  have hNN : 3 ≤ N := hN
  let S := consecutiveBlockConstraint n (q+r) C
  have hS : S.Nonempty := consecutiveBlockConstraint_nonempty C hC
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  have hf := restricted_prior_pressure_mean hhaar hgauss (by omega : 3 ≤ N+n)
    (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC)
    (μ (N+n)) θ (eig (N+n)) (I (N+n))
    (fun i => cavityBaseAmplitude (u r) i) (fun i => cavityBaseAmplitude_mem (u r) (hu r) i) (v r) 1
  have hb := restricted_prior_pressure_mean hhaar hgauss hN S hS
    (μ N) θ (eig N) (I N) (u r) (hu r) (v r) 1
  rw [cavityBaseAmplitude_extend] at hf
  rw [← cavityOrientedFamily_pos μ (by omega)] at hf
  rw [← cavityOrientedFamily_pos μ (by omega)] at hb
  unfold consecutivePriorIncrement repeatedRotationIncrement
  change _ = _-_ 
  rw [← hf, ← hb]

lemma cavity_oriented_restricted_pressure {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) (S : Finset (Spin N)) (eig c : Fin N → ℝ) :
    (∫ U, restrictedRotatedPressure S eig (specialRotation U) c ∂cavityOrientedBaseLaw hN μ) =
      ∫ V, restrictedRotatedPressure S eig (matrixRotation V⁻¹) c ∂μ := by
  calc
    _ = ∫ V, restrictedRotatedPressure S eig
        (specialRotation (cavityOrientationLift hN V⁻¹)) c ∂μ :=
      ((cavityOrientedBaseLaw_preserving hN μ).hasLaw.integral_comp
        (measurable_restrictedRotatedPressure S eig c).aestronglyMeasurable).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun V => by
        simp only [restrictedRotatedPressure, cavityOrientationLift_energy]

end InvariantIsing

end

end OAI
