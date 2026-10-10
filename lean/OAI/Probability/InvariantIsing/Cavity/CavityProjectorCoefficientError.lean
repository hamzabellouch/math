import OAI.Probability.InvariantIsing.Cavity.CavityProjectorCutoffLaw
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffEnergyComparison
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientProbability
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientError

namespace OAI

/-! A change of the small cavity blocks on a fixed spatial cutoff
controls the normalized observable without inverse-normalizer estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix

namespace InvariantIsing

theorem cavity_projector_coefficient_error {N n m d depth : ℕ}
    (g : Fin N → Fin m) (V : Orthogonal N) (T : LabeledTree depth)
    (lam v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (t : ℝ) {D : ℝ} (hD : 0 ≤ D) (A A' : CavityFactorBlocks d n)
    (p : CavityProjectorFrame N m d)
    (hp : p.1 = fun a => cavitySpectralProjector V (cavitySpectralGroup g a))
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ)
    {M s : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) (hs : 0 < s) :
    |cavityProjectorCavityMean T (fun a => t*lam a+2*perturbationScale N*v a)
        u t D A F p -
      cavityProjectorCavityMean T (fun a => t*lam a+2*perturbationScale N*v a)
        u t D A' F p| ≤
      4*(|t| *cavityFactorDeviation A A'*D)/s+M^2*s/2 := by
  rw [cavity_projector_cavity_cutoff g V T lam v u t D A p hp F,
    cavity_projector_cavity_cutoff g V T lam v u t D A' p hp F]
  let ν := (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
    (uniformSpinPrior n : Measure (Spin n))
  let eig := diagonalPerturbedEigenvalues (fun j => lam (g j)) (cavitySpectralGroup g) v t
  let E := fun σ : Spin N × Spin n => rotatedEnergy eig (matrixRotation V⁻¹) σ.1
  let Q := fun A : CavityFactorBlocks d n => fun σ : Spin N × Spin n =>
    t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 σ.1) σ.2
  let H := fun x : (Spin N × LabeledLeaf depth) × Spin n => E (x.1.1,x.2)+Q A (x.1.1,x.2)
  let J := fun x : (Spin N × LabeledLeaf depth) × Spin n => E (x.1.1,x.2)+Q A' (x.1.1,x.2)
  let C := fun x : (Spin N × LabeledLeaf depth) × Spin n =>
    cavityPerturbationCoefficients (matrixRotation V⁻¹) (cavitySpectralGroup g) u depth x.1
  let S := {x : (Spin N × LabeledLeaf depth) × Spin n |
    1+‖cavityFrameCoordinates p.2 x.1.1‖^2 ≤ D}
  obtain ⟨L, hL⟩ := Finite.exists_le (fun x : Spin N × Spin n => |E x+Q A x|)
  obtain ⟨L', hL'⟩ := Finite.exists_le (fun x : Spin N × Spin n => |E x+Q A' x|)
  have hchange (x : (Spin N × LabeledLeaf depth) × Spin n) (hx : x ∈ S) :
      |H x-J x| ≤ |t| *cavityFactorDeviation A A'*D := by
    dsimp only [H, J, Q]
    rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul, cavityLogFactor_sub]
    have hg := cavity_logFactor_growth (A.1-A'.1) (A.2.1-A'.2.1) (A.2.2-A'.2.2)
      (cavityFrameCoordinates p.2 x.1.1) x.2
    apply (mul_le_mul_of_nonneg_left hg (abs_nonneg t)).trans
    simpa only [cavityFactorDeviation, cavityFactorSize, mul_assoc] using
      mul_le_mul_of_nonneg_left hx (mul_nonneg (abs_nonneg t) (cavityFactorDeviation_nonneg A A'))
  have hb := cavity_bounded_cutoff_energy_comparison ν H J
    (fun x => hL (x.1.1,x.2)) (fun x => hL' (x.1.1,x.2)) C
    (fun x => cavityPerturbationCoefficients_sq_le (matrixRotation V⁻¹) (cavitySpectralGroup g)
      u hu x.1) S (mul_nonneg (mul_nonneg (abs_nonneg t) (cavityFactorDeviation_nonneg A A')) hD)
    hchange F hM hF hs
  have he z : (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      H x+cylinderField (C x) z) = fun x =>
      cavityRotationHamiltonian (matrixRotation V⁻¹) eig (cavitySpectralGroup g) u z x.1 +
        t*cavityLogFactor A.1 A.2.1 A.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2 := by
    funext x
    dsimp only [H, E, Q, C, cavityRotationHamiltonian]
    ring
  have he' z : (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      J x+cylinderField (C x) z) = fun x =>
      cavityRotationHamiltonian (matrixRotation V⁻¹) eig (cavitySpectralGroup g) u z x.1 +
        t*cavityLogFactor A'.1 A'.2.1 A'.2.2 (cavityFrameCoordinates p.2 x.1.1) x.2 := by
    funext x
    dsimp only [J, E, Q, C, cavityRotationHamiltonian]
    ring
  simp_rw [he, he'] at hb
  exact hb

end InvariantIsing

end

end OAI
