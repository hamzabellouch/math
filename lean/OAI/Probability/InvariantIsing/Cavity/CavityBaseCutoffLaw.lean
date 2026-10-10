import OAI.Probability.InvariantIsing.Cavity.CavityBaseCutoffProduct

namespace OAI

/-! The base cutoff interpolation law in unconditioned product
coordinates. This form permits replacement of the whole Gaussian field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

theorem cavity_base_cutoff_product_law {N n m depth : ℕ}
    (U : Rotation (N+n)) (V : Rotation N) (T : LabeledTree depth)
    (J : Fin m → Finset (Fin N)) (eig : Fin (N+n) → ℝ) (eig₀ : Fin N → ℝ)
    (v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    let μ := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
    let ν := ((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
      (labeledLeafLaw depth T)
    let s := {x : (Spin N × Spin n) × LabeledLeaf depth | w x.1 ≤ D}
    let W := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      t * (rotatedEnergy eig U (cavityJoinedSpin x.1) - rotatedEnergy eig₀ V x.1.1)
    cavityBaseCutoffReplicaMean U V J eig eig₀ v u t w D (subtypeReference ν s)
      (fun σ => F (fun i => (σ i).val)) =
    ∫ z, cavityCutoffReplicaMean (μ.prod (uniformSpinPrior n))
      (fun x => cavityRotationHamiltonian V
        (diagonalPerturbedEigenvalues eig₀ J v t) J u z x.1 + W (cavityPairLeafUnswap x))
      (cavityPairLeafUnswap ⁻¹' s)
      (fun σ => F (fun i => cavityPairLeafUnswap (σ i))) ∂gaussianCoordinates := by
  intro μ ν s W
  let H := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
    rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1.1 + W x
  let A := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
    cavityPerturbationCoefficients V J u depth (x.1.1,x.2)
  obtain ⟨M, hM⟩ := Finite.exists_le (fun x : Spin N × Spin n =>
    |rotatedEnergy (diagonalPerturbedEigenvalues eig₀ J v t) V x.1 +
      t * (rotatedEnergy eig U (cavityJoinedSpin x) - rotatedEnergy eig₀ V x.1)|)
  have hraw : ∀ᵐ z ∂gaussianCoordinates,
      Integrable (fun x => Real.exp (H x + cylinderField (A x) z)) ν :=
    cylinder_partition_exp_integrable_ae ν H
      (cavity_bounded_base_exp_integrable ν H (fun x => hM x.1)) A
      (fun x => cavityPerturbationCoefficients_sq_le V J u hu (x.1.1,x.2))
  change (∫ z, referenceReplicaMean (subtypeReference ν s)
    (fun x => H x.val + cylinderField (A x.val) z)
    (fun σ => F (fun i => (σ i).val)) ∂gaussianCoordinates) = _
  apply integral_congr_ae
  filter_upwards [hraw] with z hz
  rw [← cavity_cutoff_replica_subtype_all ν _ hz s (Set.to_countable s).measurableSet F]
  have heq : (fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      H x + cylinderField (A x) z) = fun x =>
      cavityRotationHamiltonian V (diagonalPerturbedEigenvalues eig₀ J v t) J u z
        (x.1.1,x.2) + W x := by
    funext x
    dsimp only [H, A, cavityRotationHamiltonian]
    ring
  rw [heq]
  have hm := cavity_cutoff_replica_map ν (μ.prod (uniformSpinPrior n)) cavityPairLeafSwap
    (cavity_pair_leaf_swap_preserving N n depth T)
    (fun x => cavityRotationHamiltonian V (diagonalPerturbedEigenvalues eig₀ J v t) J u z x.1 +
      W (cavityPairLeafUnswap x)) (cavityPairLeafUnswap ⁻¹' s)
    (fun σ => F (fun i => cavityPairLeafUnswap (σ i)))
  have hs : cavityPairLeafSwap ⁻¹' (cavityPairLeafUnswap ⁻¹' s) = s := by
    ext x
    rfl
  rw [hs] at hm
  simpa only [Function.comp_def, cavityPairLeafSwap, cavityPairLeafUnswap] using hm

end InvariantIsing

end

end OAI
