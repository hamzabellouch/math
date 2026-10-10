import OAI.Probability.InvariantIsing.Fields.SpinPriorFrozenReference

namespace OAI

/-! Frozen Gaussian and diagonal tilts reconstruct the same actual Gibbs law. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem spinPriorFrozenGaussian_reference_fold_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (j : Fin k) (t : ℝ) :
    ∀ᵐ p : TensorFrozenData N n j × (ℕ → ℝ) ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates,
      (spinPriorFrozenReference π eig c I degree amplitude n r h j p.1).tilted
        (fun x => t * cylinderField (jointSpectralMonomialCoefficients
          (specialRotation p.1.1.1) I (degree j) n (r j) x) p.2) =
      spinPriorNamespacedReference (n := n) π eig c I degree (Function.update amplitude j t) r h
        (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2)) := by
  have hp := tensorFrozenInsertion_measurePreserving μ n b j
  have hbase := (measurePreserving_fst (μ := tensorFrozenLaw μ n b j)
    (ν := gaussianCoordinates)).quasiMeasurePreserving.ae
    (spinPriorFrozenBase_exp_integrable_ae μ π eig c I degree amplitude n b r h hh h0 j)
  have hfull := hp.quasiMeasurePreserving.ae
    (spinPriorNamespaced_exp_integrable_ae μ π eig c I degree (Function.update amplitude j t) n b r h hh h0)
  filter_upwards [hbase, hfull] with p hb hf
  let ν := labeledSpinReference n π p.1.1.2
  let H := tensorFrozenBaseEnergy eig c I degree amplitude n r h j p.1
  let G := fun x : Spin N × LabeledLeaf n => t * cylinderField (jointSpectralMonomialCoefficients
    (specialRotation p.1.1.1) I (degree j) n (r j) x) p.2
  have he : tensorNamespacedHamiltonian eig c I degree (Function.update amplitude j t) n r h
      (p.1.1, gaussianNamespaceJoin (j + 1) (p.2, p.1.2)) = fun x => H x + G x := by
    funext x
    have he := tensorFrozenEnergy_insert eig c I degree (Function.update amplitude j t)
      n r h hh h0 j p.1 p.2 x
    simpa only [tensorNamespacedHamiltonian, tensorFrozenBaseEnergy, Function.update_idem,
      Function.update_self, H, G] using he
  have hi : Integrable (fun x => Real.exp (H x + G x)) ν := by
    convert hf using 1
    funext x
    exact congrArg Real.exp (congrFun he x).symm
  change (gibbsProbability ν H).tilted G = gibbsProbability ν
    (tensorNamespacedHamiltonian eig c I degree (Function.update amplitude j t) n r h
      (p.1.1, gaussianNamespaceJoin (j+1) (p.2,p.1.2)))
  have hH : Integrable (fun x => Real.exp (H x)) ν := hb
  rw [he, gibbsProbability_eq_tilted ν H hH, gibbsProbability_eq_tilted ν (fun x => H x + G x) hi]
  rw [tilted_tilted hH G]
  rfl

theorem spinPriorFrozenDiagonal_reference_fold_ae {N m k : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) :
    ∀ᵐ p : TensorFlatDisorder N n
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      (spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t)
        c I degree amplitude r h p).tilted
        (fun x : Spin N × LabeledLeaf n => N * perturbationScale N * w *
          projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1) =
      spinPriorNamespacedReference (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
        c I degree amplitude r h p := by
  have hb := spinPriorNamespaced_exp_integrable_ae μ π
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n b r h hh h0
  have hw := spinPriorNamespaced_exp_integrable_ae μ π
    (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n b r h hh h0
  filter_upwards [hb, hw] with p hp₀ hpw
  let ν := labeledSpinReference n π p.1.2
  let H := tensorNamespacedHamiltonian
    (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude n r h p
  let G := fun x : Spin N × LabeledLeaf n => N * perturbationScale N * w *
    projectedOverlap (specialRotation p.1.1) (I a) x.1 x.1
  have he : tensorNamespacedHamiltonian
      (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) c I degree amplitude n r h p =
      fun x => H x + G x := by
    funext x
    dsimp only [tensorNamespacedHamiltonian, H, G]
    rw [rotatedEnergy_diagonal_coordinate hN eig (specialRotation p.1.1) I v t a w x.1]
    ring
  have hi : Integrable (fun x => Real.exp (H x + G x)) ν := by
    convert hpw using 1
    funext x
    exact congrArg Real.exp (congrFun he x).symm
  change (gibbsProbability ν H).tilted G = gibbsProbability ν
    (tensorNamespacedHamiltonian (diagonalPerturbedEigenvalues eig I (Function.update v a w) t)
      c I degree amplitude n r h p)
  have hH : Integrable (fun x => Real.exp (H x)) ν := hp₀
  rw [he, gibbsProbability_eq_tilted ν H hH, gibbsProbability_eq_tilted ν (fun x => H x + G x) hi]
  rw [tilted_tilted hH G]
  rfl

end InvariantIsing

end

end OAI
