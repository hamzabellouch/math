import OAI.Probability.InvariantIsing.Cavity.OffsetMinimumSequence
import OAI.Probability.InvariantIsing.Cavity.ConsecutivePhysicalIncrement
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPriorPressure
import OAI.Probability.InvariantIsing.Cavity.CavityOrientedFamily

namespace OAI

/-! The consecutive prior increment is the original physical constrained
rotation increment, with the same base perturbation in both dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def offsetRotationIncrement {m n r₀ : ℕ}
    (μ : (N : ℕ) → Measure (Orthogonal N))
    (eig : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty) (K : ℕ)
    (u : Fin (r₀+K*n) → ℝ) (v : Fin m → ℝ) : ℝ :=
  let N := r₀+K*n
  let S := offsetBlockConstraint K R C
  let hS := offsetBlockConstraint_nonempty R hR C hC
  let θ : Measure (LabeledTree 0) := labeledCascadeLaw 0 (fun _ => 1)
  (∫ z, restrictedRotationLogMean (cavityProductSlice S C)
    (cavityProductSlice_nonempty S hS C hC) z.2
    (diagonalPerturbedEigenvalues (eig (N+n)) (I (N+n)) v 1)
    (I (N+n)) (cavityBaseAmplitude u) z.1 ∂(μ (N+n)).prod θ) -
  ∫ z, restrictedRotationLogMean S hS z.2
    (diagonalPerturbedEigenvalues (eig N) (I N) v 1)
    (I N) (cavityBaseAmplitude u) z.1 ∂(μ N).prod θ

lemma offset_prior_increment_physical
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m n q r₀ : ℕ} (μ : (N : ℕ) → Measure (Orthogonal N))
    [∀ N, IsProbabilityMeasure (μ N)] [∀ N, (μ N).IsMulRightInvariant]
    (eig : (N : ℕ) → Fin N → ℝ) (I : (N : ℕ) → Fin m → Finset (Fin N))
    (R : Finset (Spin r₀)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (u : (r : ℕ) → Fin (r₀+(q+r)*n) → ℝ) (v : ℕ → Fin m → ℝ)
    (hu : ∀ r i, u r i ∈ Set.Icc (1 : ℝ) 2) (r : ℕ) (hN : 3 ≤ r₀+(q+r)*n) :
    offsetPriorIncrement (cavityOrientedFamily μ) eig (fun _ _ => 0) I q R hR C hC u v r =
      offsetRotationIncrement μ eig I R hR C hC (q+r) (u r) (v r) := by
  let N := r₀+(q+r)*n
  have hNN : 3 ≤ N := hN
  let S := offsetBlockConstraint (q+r) R C
  have hS : S.Nonempty := offsetBlockConstraint_nonempty R hR C hC
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
  unfold offsetPriorIncrement offsetRotationIncrement
  change _ = _-_ 
  rw [← hf, ← hb]


end InvariantIsing

end

end OAI
