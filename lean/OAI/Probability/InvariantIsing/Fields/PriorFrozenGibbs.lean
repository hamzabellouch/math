import OAI.Probability.InvariantIsing.Fields.PriorFrozenReference

namespace OAI

/-! Both selected perturbations reconstruct the same constrained Gibbs law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

theorem priorFrozenGaussian_reference_fold_ae {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin k) (t : ℝ) :
    ∀ᵐ p : PriorFrozenData N j × (ℕ → ℝ) ∂(priorFrozenLaw μ j).prod gaussianCoordinates,
      (priorFrozenReference ν eig c I degree amplitude r h j p.1).tilted
        (fun x => t*cylinderField (jointSpectralMonomialCoefficients
          (specialRotation p.1.1) I (degree j) n (r j) x) p.2) =
      priorNamespacedReference ν eig c I degree (Function.update amplitude j t)
        (fun i => tensorPathProfile I degree n r h i) (priorFrozenInsertion j p) := by
  have hb := (measurePreserving_fst (μ := priorFrozenLaw μ j)
    (ν := gaussianCoordinates)).quasiMeasurePreserving.ae
    (priorFrozenBase_exp_integrable_ae μ ν eig c I degree amplitude r h hh h0 j)
  have hf := (priorFrozenInsertion_preserving μ j).quasiMeasurePreserving.ae
    (priorNamespaced_exp_integrable_ae μ ν eig c I degree (Function.update amplitude j t) r h hh h0)
  filter_upwards [hb,hf] with p hbase hfull
  let H : Spin N × LabeledLeaf n → ℝ := priorFrozenBaseEnergy eig c I degree amplitude r h j p.1
  let G := fun x : Spin N × LabeledLeaf n => t*cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1) I (degree j) n (r j) x) p.2
  have he : priorNamespacedHamiltonian eig c I degree (Function.update amplitude j t)
      (fun i => tensorPathProfile I degree n r h i) (priorFrozenInsertion j p) = fun x => H x+G x := by
    funext x
    simpa only [H,G,priorFrozenBaseEnergy,Function.update_idem,Function.update_self] using
      priorFrozenHamiltonian_insert eig c I degree (Function.update amplitude j t) r h hh h0 j p.1 p.2 x
  have hi : Integrable (fun x => Real.exp (H x+G x)) ν := by
    simpa only [he] using hfull
  change (gibbsProbability ν H).tilted G = gibbsProbability ν _
  rw [he,gibbsProbability_eq_tilted ν H hbase,
    gibbsProbability_eq_tilted ν (fun x => H x+G x) hi,tilted_tilted hbase G]
  rfl

theorem priorFrozenDiagonal_reference_fold_ae {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) :
    ∀ᵐ p : SpecialOrthogonal N × (ℕ → ℝ) ∂μ.prod gaussianCoordinates,
      (priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p).tilted
        (fun x : Spin N × LabeledLeaf n => N*perturbationScale N*w*
          projectedOverlap (specialRotation p.1) (I a) x.1 x.1) =
      priorNamespacedReference ν (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude (fun i => tensorPathProfile I degree n r h i) p := by
  have hb := priorNamespaced_exp_integrable_ae μ ν
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude r h hh h0
  have hw := priorNamespaced_exp_integrable_ae μ ν
    (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude r h hh h0
  filter_upwards [hb,hw] with p hp₀ hpw
  let H : Spin N × LabeledLeaf n → ℝ := priorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude
    (fun i => tensorPathProfile I degree n r h i) p
  let G := fun x : Spin N × LabeledLeaf n => N*perturbationScale N*w*
    projectedOverlap (specialRotation p.1) (I a) x.1 x.1
  have he : priorNamespacedHamiltonian
      (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude
      (fun i => tensorPathProfile I degree n r h i) p = fun x => H x+G x := by
    funext x
    dsimp only [priorNamespacedHamiltonian,H,G]
    rw [rotatedEnergy_diagonal_coordinate hN eig (specialRotation p.1) I v t a w x.1]
    ring
  have hi : Integrable (fun x => Real.exp (H x+G x)) ν := by
    simpa only [he] using hpw
  change (gibbsProbability ν H).tilted G = gibbsProbability ν _
  rw [he,gibbsProbability_eq_tilted ν H hp₀,
    gibbsProbability_eq_tilted ν (fun x => H x+G x) hi,tilted_tilted hp₀ G]
  rfl

end InvariantIsing

end

end OAI
