import OAI.Probability.InvariantIsing.Cavity.CavityBaseCutoffFactor
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRotationProbability

namespace OAI

/-! A bounded spin-only cavity potential factors over the actual
perturbed base Gibbs law, retaining the spatial indicator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_rotation_cutoff_weight {N n m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (R : Finset (Spin n)) (hR : R.Nonempty)
    (V : Rotation N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (W : Spin N × Spin n → ℝ)
    (s : Set ((Spin N × LabeledLeaf depth) × Spin n))
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    (∫ z, cavityCutoffReplicaMean
      ((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
        (restrictedSpinPrior R hR))
      (fun x => cavityRotationHamiltonian V eig I u z x.1 + W (x.1.1,x.2)) s F
        ∂gaussianCoordinates) =
    ∫ z, cavityWeightedReplicaMean
      (((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian V eig I u z)).prod (restrictedSpinPrior R hR))
      (s.indicator (fun x => Real.exp (W (x.1.1,x.2)))) F ∂gaussianCoordinates := by
  let μ := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  let ν := μ.prod (restrictedSpinPrior R hR : Measure (Spin n))
  let H : (Spin N × LabeledLeaf depth) × Spin n → ℝ := fun x =>
    rotatedEnergy eig V x.1.1+W (x.1.1,x.2)
  let C : (Spin N × LabeledLeaf depth) × Spin n → ℕ →₀ ℝ := fun x =>
    cavityPerturbationCoefficients V I u depth x.1
  obtain ⟨M,hM⟩ := Finite.exists_le (fun x : Spin N × Spin n => |rotatedEnergy eig V x.1+W x|)
  have hfull : ∀ᵐ z ∂gaussianCoordinates,
      Integrable (fun x => Real.exp (H x+cylinderField (C x) z)) ν :=
    cylinder_partition_exp_integrable_ae ν H
      (cavity_bounded_base_exp_integrable ν H (fun x => hM (x.1.1,x.2))) C
      (fun x => cavityPerturbationCoefficients_sq_le V I u hu x.1)
  apply integral_congr_ae
  filter_upwards [hfull, restricted_rotation_exp_integrable_ae S hS V T eig I u hu] with z hz hj
  have he : (fun x => H x+cylinderField (C x) z) =
      fun x : (Spin N × LabeledLeaf depth) × Spin n =>
        cavityRotationHamiltonian V eig I u z x.1+W (x.1.1,x.2) := by
    funext x
    dsimp only [H,C,cavityRotationHamiltonian]
    ring
  have hz' : Integrable (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      Real.exp (cavityRotationHamiltonian V eig I u z x.1+W (x.1.1,x.2))) ν :=
    hz.congr (ae_of_all _ fun x => congrArg Real.exp (congrFun he x))
  exact cavity_base_cutoff_indicator μ (restrictedSpinPrior R hR)
    (cavityRotationHamiltonian V eig I u z) (fun x => W (x.1.1,x.2)) hj hz' s F

end InvariantIsing

end

end OAI
