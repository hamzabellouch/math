import OAI.Probability.InvariantIsing.Cavity.CavityBaseRestrictedLaw
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalCutoff

namespace OAI

/-! The actual perturbed base cutoff is the base Gibbs kernel reweighted
by the unperturbed cavity factor, with the spatial cutoff inside the weight. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

theorem cavity_base_cutoff_product {N n m depth : ℕ}
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
    ∫ z, cavityWeightedReplicaMean
      ((μ.tilted (cavityRotationHamiltonian V (diagonalPerturbedEigenvalues eig₀ J v t) J u z)).prod
        (uniformSpinPrior n))
      ((cavityPairLeafUnswap ⁻¹' s).indicator (fun x => Real.exp (W (cavityPairLeafUnswap x))))
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
  filter_upwards [hraw, cavity_rotation_exp_integrable_ae V T
    (diagonalPerturbedEigenvalues eig₀ J v t) J u hu] with z hz hj
  let B : Spin N × LabeledLeaf depth → ℝ :=
    cavityRotationHamiltonian V (diagonalPerturbedEigenvalues eig₀ J v t) J u z
  have heq : (fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      H x + cylinderField (A x) z) = fun x => B (x.1.1,x.2) + W x := by
    funext x
    dsimp only [H, A, B, cavityRotationHamiltonian]
    ring
  have hfull : Integrable (fun x => Real.exp (B (x.1.1,x.2) + W x)) ν := by
    apply hz.congr
    filter_upwards [] with x
    exact congrArg Real.exp (congrFun heq x)
  have hs : MeasurableSet s := (Set.to_countable s).measurableSet
  rw [← cavity_cutoff_replica_subtype_all ν _ hz s hs F]
  rw [heq]
  exact cavity_base_restricted_product T B W hj hfull s F

end InvariantIsing

end

end OAI
