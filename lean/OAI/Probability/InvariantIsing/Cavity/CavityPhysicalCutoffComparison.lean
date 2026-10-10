import OAI.Probability.InvariantIsing.Cavity.CavityCoupledProjectors
import OAI.Probability.InvariantIsing.Cavity.CavityCoupledEnergy
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorCutoffLaw
import OAI.Probability.InvariantIsing.Cavity.CavityBaseCutoffLaw
import OAI.Probability.InvariantIsing.Cavity.CavityGeometricTest
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalComparison

namespace OAI

/-! The original perturbed Ising cutoff test is approximated by a
measurable physical-projector cavity observable, with the explicit
finite-volume covariance and deterministic errors. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_physical_cutoff_comparison {N n m d depth : ℕ} (hN : 0 < N)
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
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    {D M s : ℝ} (hD : 1 ≤ D) (hM : 0 ≤ M) (hs : 0 < s)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ)
    (hF : ∀ σ, |F σ| ≤ M) :
    let G := cavityCompressionGrams g (cavitySpecialOrthogonal U)
    let B₁ := B G
    let A := cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
      (Matrix.diagonal (fun j => lam (a₀ j))) B₁ (cavitySpectralStack G)
    let p := cavityPhysicalLabeledProjectors g B a₀ (cavitySpecialOrthogonal U)
    let w := cavityGeometricWeight g B₁ U
    |cavityProjectorCavityMean T (fun a => t*lam a+2*perturbationScale N*v a)
        u t D A (fun σ => F (fun i => cavityPairLeafUnswap (σ i))) p -
      (∫ z, cavityCutoffReplicaMean
        (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
        (cavityRotationHamiltonian (specialRotation U)
          (diagonalPerturbedEigenvalues (fun i => lam (g i)) (cavitySpectralGroup g) v t)
          (cavitySpectralGroup g) u z)
        {x | w (cavitySpinSplit N n x.1) ≤ D}
        (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates)| ≤
      (2 * (2 : ℝ)^2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityCovarianceRate n (2*n+1) N * (2*D)) +
        2 * 2 * (cavityDeterministicRate n m (2*(2*n+1)) N * D)) / s + M^2*s/2 := by
  intro G B₁ A p w
  obtain ⟨V, hSpectrum, hProj, hSpecial, herr₀⟩ :=
    cavity_coupled_labeled_projectors hN g k ek e es U a₀ B hB hBT hA
  let eig₀ := fun j => Sum.elim (fun b => lam b.1) (fun j => lam (a₀ j)) (e.symm j)
  have herr (x z : Spin N × Spin n) (a : Fin m) :
      |projectedOverlap (specialRotation U) (cavitySpectralGroup g a)
        (cavityJoinedSpin x) (cavityJoinedSpin z) -
        projectedOverlap (matrixRotation V⁻¹) (cavityBaseGroup k e a₀ a) x.1 z.1| ≤
        (2 * (n : ℝ) + 1) / N * (w x + w z) := by
    have h := herr₀ a (cavityJoinedSpin x) (cavityJoinedSpin z)
    simp only [cavityJoinedSpin, Fin.append_left] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (Nat.cast_nonneg N))
    dsimp only [w, cavityGeometricWeight, B₁, G, cavityJoinedSpin]
    linarith
  have hc := cavity_original_cutoff_comparison hN (specialRotation U) (matrixRotation V⁻¹)
    T (cavitySpectralGroup g) (cavityBaseGroup k e a₀) (fun i => lam (g i)) eig₀
    v hv u hu t w (cavityGeometricWeight_one_le g B₁ U) (by positivity) hD hM hs herr F hF
  dsimp only at hc
  rw [cavity_base_cutoff_product_law (specialRotation U) (matrixRotation V⁻¹) T
    (cavityBaseGroup k e a₀) (fun i => lam (g i)) eig₀ v u hu t w D F] at hc
  let g₀ : Fin N → Fin m := fun j => Sum.elim (fun w => w.1) a₀ (e.symm j)
  have hp : p.1 = fun a => cavitySpectralProjector V (cavitySpectralGroup g₀ a) := by
    rw [show p = cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀) from hProj]
    exact cavityCanonicalProjectorFrame_action_fst k e a₀ V
  have hcan := cavity_projector_cavity_cutoff g₀ V T lam v u t D A p hp
    (fun σ => F (fun i => cavityPairLeafUnswap (σ i)))
  have hI : cavitySpectralGroup g₀ = cavityBaseGroup k e a₀ := rfl
  have hEig : (fun j => lam (g₀ j)) = eig₀ := by
    funext j
    dsimp only [g₀, eig₀]
    cases e.symm j <;> rfl
  rw [hI, hEig] at hcan
  have hw (x : (Spin N × LabeledLeaf depth) × Spin n) :
      w (cavityPairLeafUnswap x).1 = 1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 := by
    dsimp only [w, cavityGeometricWeight, cavityPairLeafUnswap]
    rw [← WithLp.toLp_ofLp 2 (cavityFullSpecialCoordinates g B₁ U
      (cavityJoinedSpin (x.1.1,x.2))),
      cavity_physical_special_coordinates g U B hBT hA x.1.1 x.2]
    rfl
  have he (x : (Spin N × LabeledLeaf depth) × Spin n) :
      rotatedEnergy (fun i => lam (g i)) (specialRotation U)
        (cavityJoinedSpin (cavityPairLeafUnswap x).1) -
          rotatedEnergy eig₀ (matrixRotation V⁻¹) (cavityPairLeafUnswap x).1.1 =
      cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2 := by
    have h := cavity_physical_energy_difference g es U lam (fun j => lam (a₀ j)) B
      hB hBT hA x.1.1 x.2
    dsimp only at h
    rw [hSpectrum, cavityQuadratic_inverse_rotation,
      cavity_physical_special_coordinates g U B hBT hA] at h
    exact h
  have hcut : (cavityPairLeafUnswap ⁻¹'
      {x : (Spin N × Spin n) × LabeledLeaf depth | w x.1 ≤ D}) =
      {x : (Spin N × LabeledLeaf depth) × Spin n |
        1 + ‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D} := by
    ext x
    change w (cavityPairLeafUnswap x).1 ≤ D ↔ _
    rw [hw]
    rfl
  simp_rw [he] at hc
  rw [hcut, ← hcan] at hc
  exact hc

end InvariantIsing

end

end OAI
