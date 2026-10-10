import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalLogIncrement
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorPartition

namespace OAI

/-! An additive lower bound for the literal full-system log partition,
written entirely in the physical projector and compression data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_physical_projector_increment {N n m d depth : ℕ} (hN : 0 < N)
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (U : SpecialOrthogonal (N+n)) (lam : Fin m → ℝ) (a₀ : Fin d → Fin m)
    (B : (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin d) ℝ)
    (hB : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      B (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 1)
    (hBT : (B (cavityCompressionGrams g (cavitySpecialOrthogonal U))).transpose *
      cavitySpectralStack (cavityCompressionGrams g (cavitySpecialOrthogonal U)) = 0)
    (hA : ∀ a, (cavityCompressionGrams g (cavitySpecialOrthogonal U) a).PosDef)
    (T : LabeledTree depth) (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t cap : ℝ) (hcap : 0 ≤ cap) :
    let G := cavityCompressionGrams g (cavitySpecialOrthogonal U)
    let A := cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun j => lam (a₀ j))) (B G) (cavitySpectralStack G)
    let p := cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U)
    let c := fun a => t*lam a+2*perturbationScale N*v a
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N +
      2*cavityCovarianceRate n (2*n+1) N
    cavityProjectorCappedLog T c u t cap δ A p + cavityProjectorLogPartition T c u p.1 ≤
      ∫ z, Real.log (∫ x, Real.exp
        (cavityRotationHamiltonian (specialRotation U)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z x)
        ∂labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
        ∂gaussianCoordinates := by
  intro G A p c δ
  obtain ⟨V,hV,hc⟩ := cavity_physical_capped_increment hN g k ek e es U lam a₀ B
    hB hBT hA T v hv u hu t cap hcap
  let g₀ : Fin N → Fin m := fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)
  let eig₀ : Fin N → ℝ := fun j => Sum.elim (fun w => lam w.1) (fun j => lam (a₀ j)) (e.symm j)
  have hp : p.1 = fun a => cavitySpectralProjector V (cavitySpectralGroup g₀ a) := by
    rw [show p = cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) from hV]
    exact cavityCanonicalProjectorFrame_action_fst k e a₀ V
  have hEig : (fun j => lam (g₀ j)) = eig₀ := by
    funext j
    dsimp only [g₀,eig₀]
    cases e.symm j <;> rfl
  have hb := cavity_projector_log_partition g₀ V T lam v u t
  rw [hEig, ← hp] at hb
  have hfull z := cavity_pair_leaf_full_partition (N := N) (n := n) T
    (cavityRotationHamiltonian (specialRotation U)
      (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
      (cavitySpectralGroup g) u z)
  have hbase z := cavity_pair_leaf_base_partition (n := n) T
    (cavityRotationHamiltonian (matrixRotation V⁻¹)
      (diagonalPerturbedEigenvalues eig₀ (cavityBaseGroup k e a₀) v t)
      (cavityBaseGroup k e a₀) u z)
  change cavityProjectorCappedLog T c u t cap δ A p ≤
    (∫ z, Real.log (∫ x, Real.exp (cavityRotationHamiltonian (specialRotation U)
      (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
      (cavitySpectralGroup g) u z (cavityJoinedSpin x.1,x.2))
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n : Measure (Spin n))).prod
        (labeledLeafLaw depth T)) ∂gaussianCoordinates) -
    ∫ z, Real.log (∫ x, Real.exp (cavityRotationHamiltonian (matrixRotation V⁻¹)
      (diagonalPerturbedEigenvalues eig₀ (cavityBaseGroup k e a₀) v t)
      (cavityBaseGroup k e a₀) u z (x.1.1,x.2))
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n : Measure (Spin n))).prod
        (labeledLeafLaw depth T)) ∂gaussianCoordinates at hc
  simp_rw [hfull, hbase] at hc
  have hJ : cavitySpectralGroup g₀ = cavityBaseGroup k e a₀ := rfl
  rw [hJ] at hb
  rw [← hb] at hc
  linarith

end InvariantIsing

end

end OAI
