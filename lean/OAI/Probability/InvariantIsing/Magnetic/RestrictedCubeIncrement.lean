import OAI.Probability.InvariantIsing.Magnetic.RestrictedTreePressureIncrement

namespace OAI

/-! The physical constrained increment includes the original cube masses
of the base and cavity slices. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_tree_cube_increment {N n m d depth : ℕ} (hN : 0<N)
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
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ] (lam v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let A := fun U => cavityCompressionFactorBlocks es lam (fun j => lam (a₀ j)) B₀
      (cavityCompressionGrams g U)
    let q := fun V => cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)
    let c := fun a => t*lam a+2*perturbationScale N*v a
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N+
      2*cavityCovarianceRate n (2*n+1) N
    let I₀ := cavityBaseGroup k e a₀
    let eig₀ := diagonalPerturbedEigenvalues
      (fun i => lam (Sum.elim (fun w => w.1) a₀ (e.symm i))) I₀ v t
    let I := cavitySpectralGroup g
    let eig := diagonalPerturbedEigenvalues (fun i => lam (g i)) I v t
    (∫ T, ∫ z, restrictedProjectorCappedLog S hS C hC T c u t cap δ (A z.1) (q z.2)
      ∂μ.prod ν ∂θ) + (Real.log C.card - n * Real.log 2) ≤
      ((∫ z, restrictedRotationLogMean (cavityProductSlice S C)
        (cavityProductSlice_nonempty S hS C hC) z.2 eig I u z.1 ∂μ.prod θ) +
          (Real.log (cavityProductSlice S C).card - (N+n) * Real.log 2)) -
      ((∫ z, restrictedRotationLogMean S hS z.2 eig₀ I₀ u z.1 ∂ν.prod θ) +
          (Real.log S.card - N * Real.log 2)) := by
  intro A q c δ I₀ eig₀ I eig
  have h := restricted_tree_pressure_capped_increment hN S hS C hC g k ek e es B₀ a₀ l r
    hg hln hr μ ν θ lam v hv u hu t cap hcap
  change (∫ T, ∫ z, restrictedProjectorCappedLog S hS C hC T c u t cap δ (A z.1) (q z.2)
    ∂μ.prod ν ∂θ) ≤
    (∫ z, restrictedRotationLogMean (cavityProductSlice S C)
      (cavityProductSlice_nonempty S hS C hC) z.2 eig I u z.1 ∂μ.prod θ) -
    ∫ z, restrictedRotationLogMean S hS z.2 eig₀ I₀ u z.1 ∂ν.prod θ at h
  rw [cavityProductSlice_log_mass S hS C hC]
  linarith only [h]

end InvariantIsing

end

end OAI
