import OAI.Probability.InvariantIsing.Cavity.CavityRotationMeasurability
import OAI.Probability.InvariantIsing.Cavity.CavityStabilizerAverage

namespace OAI

/-! Fresh independent rotations inside the spectral groups can be
inserted in every bounded replica observable of the actual perturbed
Gibbs law. Its diagonal and tensor perturbations are both retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

lemma measurable_cavityRotationReplicaMean {N m depth r : ℕ}
    (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (F : Orthogonal N → (Fin r → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun V => ∫ z, referenceReplicaMean
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z) (F V)
      ∂gaussianCoordinates) := by
  exact (measurable_referenceReplicaMean _
    (measurable_cavityRotationHamiltonian eig I u)
    (hF.comp (measurable_fst.fst.prodMk measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

theorem cavity_group_gibbs_average {N m depth r : ℕ}
    (k : Fin m → ℕ) (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (T : LabeledTree depth) (lam v : Fin m → ℝ) (u : ℕ → ℝ) (t : ℝ)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (η : Measure ((a : Fin m) → Orthogonal (k a))) [IsProbabilityMeasure η]
    (F : Orthogonal N → (Fin r → Spin N × LabeledLeaf depth) → ℝ)
    (hF : Measurable (Function.uncurry F)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ V σ, |F V σ| ≤ C) :
    let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
    let I := cavitySpectralGroup (fun i => (e.symm i).1)
    let eig := diagonalPerturbedEigenvalues (fun i => lam (e.symm i).1) I v t
    (∫ V, ∫ z, referenceReplicaMean ν
      (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z) (F V)
      ∂gaussianCoordinates ∂μ) =
    ∫ V, ∫ W, ∫ z, referenceReplicaMean ν
      (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z)
      (F (V * cavityGroupRotation k e W)) ∂gaussianCoordinates ∂η ∂μ := by
  intro ν I eig
  let : SecondCountableTopology (Matrix (Fin N) (Fin N) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℝ))
  let : SecondCountableTopology (Orthogonal N) :=
    (show Topology.IsInducing (Subtype.val : Orthogonal N → Matrix (Fin N) (Fin N) ℝ) from
      Topology.IsInducing.subtypeVal).secondCountableTopology
  let (a : Fin m) : SecondCountableTopology (Orthogonal (k a)) := by
    let : SecondCountableTopology (Matrix (Fin (k a)) (Fin (k a)) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin (k a) → Fin (k a) → ℝ))
    exact (show Topology.IsInducing
      (Subtype.val : Orthogonal (k a) → Matrix (Fin (k a)) (Fin (k a)) ℝ) from
        Topology.IsInducing.subtypeVal).secondCountableTopology
  let G := fun V : Orthogonal N => ∫ z, referenceReplicaMean ν
    (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z) (F V) ∂gaussianCoordinates
  have hG : Measurable G := measurable_cavityRotationReplicaMean T eig I u F hF
  have hGb V : ‖G V‖ ≤ C := by
    have hbz : ∀ᵐ z ∂gaussianCoordinates, ‖referenceReplicaMean ν
        (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z) (F V)‖ ≤ C :=
      ae_of_all _ fun z => by
        simpa only [Real.norm_eq_abs] using
          referenceReplicaMean_abs_le ν _ (F V) (measurable_of_countable _) hC (hb V)
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hbz
  let K := fun p : Orthogonal N × ((a : Fin m) → Orthogonal (k a)) =>
    G (p.1 * cavityGroupRotation k e p.2)
  have hrot : Continuous (fun p : Orthogonal N × ((a : Fin m) → Orthogonal (k a)) =>
      p.1 * cavityGroupRotation k e p.2) :=
    continuous_fst.mul ((continuous_cavityGroupRotation k e).comp continuous_snd)
  have hi : Integrable K (μ.prod η) := Integrable.of_bound
    (hG.comp hrot.measurable).aestronglyMeasurable C (ae_of_all _ fun p => hGb _)
  have hrow W : (∫ V, K (V,W) ∂μ) = ∫ V, G V ∂μ :=
    integral_mul_right_eq_self G (cavityGroupRotation k e W)
  have heq V W : K (V,W) = ∫ z, referenceReplicaMean ν
      (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z)
      (F (V * cavityGroupRotation k e W)) ∂gaussianCoordinates :=
    cavityGroupRotation_gibbs_replica k e V W T lam v u t (F (V * cavityGroupRotation k e W))
  calc
    _ = ∫ W, ∫ V, K (V,W) ∂μ ∂η := by simp only [hrow]; simp [G]
    _ = ∫ V, ∫ W, K (V,W) ∂η ∂μ := (integral_integral_swap hi).symm
    _ = _ := by simp only [heq]

end InvariantIsing

end

end OAI
