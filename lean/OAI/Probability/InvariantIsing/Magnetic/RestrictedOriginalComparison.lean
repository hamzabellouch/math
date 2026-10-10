import OAI.Probability.InvariantIsing.Magnetic.RestrictedOriginalCutoff

namespace OAI

/-! The finite geometric comparison with the literal original-model
cutoff on its right-hand side, including empty cutoffs. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

theorem restricted_original_cutoff_comparison {N n m depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (U : Rotation (N+n)) (V : Rotation N) (T : LabeledTree depth)
    (I : Fin m → Finset (Fin (N+n))) (J : Fin m → Finset (Fin N))
    (eig : Fin (N+n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (hw : ∀ x, 1 ≤ w x)
    {C D M s₀ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hM : 0 ≤ M) (hs₀ : 0 < s₀)
    (herr : ∀ x y a, |projectedOverlap U (I a) (cavityJoinedSpin x) (cavityJoinedSpin y) -
      projectedOverlap V (J a) x.1 y.1| ≤ C / N * (w x + w y))
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let ν := ((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior Cset hCset)).prod
      (labeledLeafLaw depth T)
    let s := {x : (Spin N × Spin n) × LabeledLeaf depth | w x.1 ≤ D}
    |cavityBaseCutoffReplicaMean U V J eig eig₀ v u t w D (subtypeReference ν s)
        (fun σ => F (fun i => (σ i).val)) -
      (∫ z, cavityCutoffReplicaMean
        (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S Cset) (cavityProductSlice_nonempty S hS Cset hCset) : Measure (Spin (N+n))) T)
        (cavityRotationHamiltonian U (diagonalPerturbedEigenvalues eig I v t) I u z)
        {x | w (cavitySpinSplit N n x.1) ≤ D}
        (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates)| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n C N * (2 * D)) +
        2 * 2 * (cavityCovarianceRate n C N * (2 * D)) +
        2 * 2 * (cavityDeterministicRate n m (2 * C) N * D)) / s₀ + M^2 * s₀ / 2 := by
  intro ν s
  rw [restricted_original_cutoff_subtype S hS Cset hCset U T eig I v u hu t w D F]
  by_cases hp : ν s = 0
  · have hc : ν.comap (Subtype.val : s → (Spin N × Spin n) × LabeledLeaf depth) = 0 := by
      apply Measure.ext
      intro A hA
      rw [comap_subtype_coe_apply (Set.to_countable s).measurableSet]
      exact measure_mono_null (by rintro x ⟨y, _, rfl⟩; exact y.property) hp
    have hz : subtypeReference ν s = 0 := by simp [subtypeReference, hp, hc]
    change |cavityBaseCutoffReplicaMean U V J eig eig₀ v u t w D (subtypeReference ν s) _ -
      cavityFullCutoffReplicaMean U I eig v u t w D (subtypeReference ν s) _| ≤ _
    rw [hz]
    simp only [cavityBaseCutoffReplicaMean, cavityFullCutoffReplicaMean,
      cavityCylinderReplicaMean, referenceReplicaMean, referencePartition,
      integral_zero_measure, zero_pow (by decide : 2 ≠ 0), div_zero,
      integral_zero, sub_self, abs_zero]
    have hcov := cavityCovarianceRate_nonneg n hC N
    have hdet : 0 ≤ cavityDeterministicRate n m (2 * C) N := by
      unfold cavityDeterministicRate perturbationScale
      positivity
    positivity
  · let := subtypeReference_probability ν ((Set.to_countable s).measurableSet) hp
    exact cavity_finite_cutoff_test_comparison hN U V I J eig eig₀ v hv u hu t
      w hw hC hD herr (subtypeReference ν s) (fun σ => F (fun i => (σ i).val))
      hM (fun σ => hF _) hs₀

end InvariantIsing

end

end OAI
