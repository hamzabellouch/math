import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearPolynomialSolver
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticFamily
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedQuadraticFamily
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

/-! One fixed family of actual polynomial solvers for every doubled and
mixed phase in the local three-phase construction. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseGeometry

theorem uniform_linear_quadratic_solvers {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    (φ : Fin 3 → Base → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (S : Fin 3 → Compacts Base)
    (Ω U K : QuadraticLabel (Fin 3) → Set SmallModes.Base)
    (hΩ : ∀ l, IsOpen (Ω l)) (hU : ∀ l, IsOpen (U l)) (hK : ∀ l, IsCompact (K l))
    (hUK : ∀ l, U l ⊆ K l) (hKΩ : ∀ l, K l ⊆ Ω l)
    (ξ : QuadraticLabel (Fin 3) → SmallModes.Base) (hξ : ∀ l, ξ l ≠ 0)
    (hImm : ∀ l x, x ∈ Ω l → Function.Injective
      (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ l x, x ∈ Ω l → Good
      (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) (ξ l))
    (hS : ∀ l, (modeSupport (quadraticCompacts S l) : Set SmallModes.Base) ⊆ U l)
    {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base) (hU₀K : U₀ ⊆ K₀)
    (hSU₀ : ∀ l, (quadraticCompacts S l : Set Base) ⊆ U₀)
    (hphase : ∀ l, coordinatePhase (quadraticFamilyPhase φ l) = phaseLinear (ξ l)) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (H : QuadraticLabel (Fin 3) → ℕ → ℝ) (Pjet : ℕ → ℝ),
      (∀ l m, 1 ≤ H l m) → (∀ m, 0 ≤ Pjet m) →
      ∃ C D J I : QuadraticLabel (Fin 3) → ℕ → ℝ,
      (∀ l m, 0 ≤ C l m) ∧ (∀ l m, 0 ≤ D l m) ∧
      (∀ l m, 1 ≤ J l m) ∧ (∀ l m, 1 ≤ I l m) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
      0 ≤ C₀ → C₀ < ρ₀ →
      WeightedBound univ 1 2 C₀
        ((G ∘ planeCoordinateIsometry.symm)-(F ∘ planeCoordinateIsometry.symm)) →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ l m, WeightedBound (linearPhaseChart (ξ l) (hξ l) (U l) (hU l)).target
        s (m+1) (H l (m+1)) (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
          (linearPhaseChart (ξ l) (hξ l) (U l) (hU l)).symm))) →
      (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j (Pjet m/(s : ℝ)^(j-2)) G) →
      ∀ τ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      ∃ c : ∀ l, PolynomialSolveData P ε G hG (quadraticFamilyPhase φ l)
        (quadraticCompacts S l) τ s,
        (∀ l, (c l).C = C l) ∧ (∀ l, (c l).D = D l) ∧ (∀ l, (c l).J = J l) ∧
        (∀ l m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c l).e.target,
          ‖iteratedFDerivWithin ℝ j (c l).e.symm (c l).e.target x‖ ≤ I l m) := by
  classical
  choose a ha hall using fun l => uniform_linear_polynomial_solver_all_profiles P hP hF
    (hΩ l) (hU l) (hK l) (hUK l) (hKΩ l) (hξ l) (hImm l) (hgood l)
    (quadraticCompacts S l) (hS l) hU₀ K₀ hU₀K (hSU₀ l)
    (quadraticFamilyPhase_smooth hφ l) (hphase l)
  obtain ⟨ρ,hρ,_,hρa⟩ := finite_positive_threshold a ha
  refine ⟨ρ,hρ,?_⟩
  intro H Pjet hH hPjet
  choose Q C D J I hQ hC hD hJ hI hd using fun l => hall l (H l) Pjet (hH l) hPjet
  refine ⟨C,D,J,I,hC,hD,hJ,hI,?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ ε hτ hτs hε hε1
  have hex (l : QuadraticLabel (Fin 3)) :=
    (hd l G hG C₀ hC₀ (hCρ.trans_le (hρa l)) hclose s hs hs1
      (hjet l) hpref τ ε hτ hτs hε hε1).2
  choose c _ _ _ hc hd hj hi using hex
  exact ⟨c,hc,hd,hj,hi⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
