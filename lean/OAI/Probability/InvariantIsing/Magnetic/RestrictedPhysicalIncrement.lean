import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalCutoffComparison
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCappedIncrement
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorLog
import OAI.Probability.InvariantIsing.Magnetic.RestrictedLogMap
import OAI.Probability.InvariantIsing.Magnetic.RestrictedProjectorLog

namespace OAI

/-! The actual geometric pressure increment dominates the capped
projector cavity logarithm, with the explicit vanishing quadratic error. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem restricted_physical_capped_increment {N n m d depth : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
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
    let eig₀ := fun j => Sum.elim (fun w => lam w.1) (fun j => lam (a₀ j)) (e.symm j)
    let J := cavityBaseGroup k e a₀
    let ν := ((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior C hC)).prod
      (labeledLeafLaw depth T)
    let δ := cavityDeterministicRate n m (2*(2*n+1)) N +
      2*cavityCovarianceRate n (2*n+1) N
    ∃ V : Orthogonal N,
      p = cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) ∧
      restrictedProjectorCappedLog S hS C hC T (fun a => t*lam a+2*perturbationScale N*v a)
        u t cap δ A p ≤
      (∫ z, Real.log (∫ x, Real.exp
        (cavityRotationHamiltonian (specialRotation U)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z (cavityJoinedSpin x.1,x.2)) ∂ν) ∂gaussianCoordinates) -
      ∫ z, Real.log (∫ x, Real.exp
        (cavityRotationHamiltonian (matrixRotation V⁻¹) (diagonalPerturbedEigenvalues eig₀ J v t)
          J u z (x.1.1,x.2)) ∂ν) ∂gaussianCoordinates := by
  intro G A p eig₀ J ν δ
  obtain ⟨V, hSpectrum, hProj, hSpecial, herr₀⟩ :=
    cavity_coupled_labeled_projectors hN g k ek e es U a₀ B hB hBT hA
  refine ⟨V, hProj, ?_⟩
  let w := cavityGeometricWeight g (B G) U
  have herr (x z : Spin N × Spin n) (a : Fin m) :
      |projectedOverlap (specialRotation U) (cavitySpectralGroup g a)
        (cavityJoinedSpin x) (cavityJoinedSpin z) -
        projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a) x.1 z.1| ≤
        (2*(n : ℝ)+1)/N*(w x+w z) := by
    have h := herr₀ a (cavityJoinedSpin x) (cavityJoinedSpin z)
    simp only [cavityJoinedSpin, Fin.append_left] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (Nat.cast_nonneg N))
    dsimp only [w, cavityGeometricWeight, G, cavityJoinedSpin]
    linarith
  have hc := cavity_finite_capped_energy_increment hN (specialRotation U) (matrixRotation V⁻¹)
    (cavitySpectralGroup g) J (fun i => lam (g i)) eig₀ v hv u hu t cap hcap ν w
    (cavityGeometricWeight_one_le g (B G) U) (by positivity) herr
  dsimp only at hc
  have hp : p.1 = fun a => cavitySpectralProjector V
      (cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) a) := by
    rw [show p = cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) from hProj]
    exact cavityCanonicalProjectorFrame_action_fst k e a₀ V
  have hI : cavitySpectralGroup (fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)) = J := rfl
  have hEig : (fun j => lam (Sum.elim (fun w => w.1) a₀ (e.symm j))) = eig₀ := by
    funext j
    dsimp only [eig₀]
    cases e.symm j <;> rfl
  have hw (x : Spin N × Spin n) :
      w x = 1+‖cavityFrameCoordinates p.2 x.1‖^2 := by
    dsimp only [w, cavityGeometricWeight]
    rw [← WithLp.toLp_ofLp 2 (cavityFullSpecialCoordinates g (B G) U (cavityJoinedSpin x)),
      cavity_physical_special_coordinates g U B hBT hA]
    rfl
  have he (x : Spin N × Spin n) :
      rotatedEnergy (fun i => lam (g i)) (specialRotation U) (cavityJoinedSpin x) -
        rotatedEnergy eig₀ (matrixRotation V⁻¹) x.1 =
      cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1) x.2 := by
    have h := cavity_physical_energy_difference g es U lam (fun j => lam (a₀ j)) B
      hB hBT hA x.1 x.2
    dsimp only at h
    rw [hSpectrum, cavityQuadratic_inverse_rotation,
      cavity_physical_special_coordinates g U B hBT hA] at h
    exact h
  have hlog : restrictedProjectorCappedLog S hS C hC T (fun a => t*lam a+2*perturbationScale N*v a)
      u t cap δ A p =
      ∫ z, Real.log (∫ x, Real.exp
        (min (t*(rotatedEnergy (fun i => lam (g i)) (specialRotation U) (cavityJoinedSpin x.1) -
          rotatedEnergy eig₀ (matrixRotation V⁻¹) x.1.1)) cap - δ*w x.1)
        ∂ν.tilted (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues eig₀ J v t) J u z (x.1.1,x.2))) ∂gaussianCoordinates := by
    rw [restricted_projector_capped_log S hS C hC _ V T lam v u t cap δ A p hp]
    rw [hI, hEig]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      have hm := restricted_log_weight_pair_leaf S hS C hC T
        (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹)
          (diagonalPerturbedEigenvalues eig₀ J v t) J u z x.1)
        (fun x => min (t*cavityLogFactor A.1 A.2.1 A.2.2
          (cavityFrameCoordinates p.2 x.1.1) x.2) cap -
            δ*(1+‖cavityFrameCoordinates p.2 x.1.1‖^2))
      simpa only [Function.comp_def, cavityPairLeafSwap, he, hw, ν] using hm.symm
  rw [hlog]
  exact hc

end InvariantIsing

end

end OAI
