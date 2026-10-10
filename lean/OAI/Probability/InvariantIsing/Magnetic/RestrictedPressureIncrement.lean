import OAI.Probability.InvariantIsing.Magnetic.RestrictedHaarLogIncrement
import OAI.Probability.InvariantIsing.Magnetic.RestrictedOrientationLog

namespace OAI

/-! The capped cavity logarithm is bounded by the literal difference
of the ordinary full and base Haar-averaged log partitions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_pressure_capped_increment {N n m d depth : ℕ} (hN : 0<N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i=a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (a₀ : Fin d → Fin m) (l r : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val<r a)
    (hln : ∀ a, l a+n ≤ r a) (hr : ∀ a, r a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let A := fun U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams g U)
    let q := fun V => cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
    let c := fun a => t*lam a+2*perturbationScale N*v a
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N+
      2*cavityCovarianceRate n (2*n+1) N
    (∫ z, restrictedProjectorCappedLog S hS C hC T c u t cap δ (A z.1) (q z.2) ∂μ.prod ν) ≤
      (∫ U, restrictedRotationLogMean (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) T
        (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
        (cavitySpectralGroup g) u U ∂μ) -
      ∫ V, restrictedRotationLogMean S hS T
        (diagonalPerturbedEigenvalues
          (fun i => lam (Sum.elim (fun w => w.1) a₀ (e.symm i)))
          (cavityBaseGroup k e a₀) v t) (cavityBaseGroup k e a₀) u V ∂ν := by
  intro A q c δ
  have h := restricted_haar_capped_log_increment hN S hS C hC g k ek e es B₀ a₀ l r hg hln hr
    μ ν T lam v hv u hu t cap hcap
  dsimp only at h
  rw [restricted_orientation_haar_log_mean (by omega : 0<N+n) (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) μ] at h
  simp_rw [restricted_canonical_log_partition S hS k e a₀] at h
  exact (le_sub_iff_add_le).mpr h

end InvariantIsing

end

end OAI
