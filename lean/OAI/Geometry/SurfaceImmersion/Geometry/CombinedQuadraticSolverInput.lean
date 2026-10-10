import OAI.Geometry.SurfaceImmersion.Geometry.CombinedQuadraticTargetBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialInputNorm

namespace OAI

/-! The actual perturbed quadratic targets in the norm of a phase solver.
The target estimate is made on a fixed compact jet domain.  The phase
solver may use its own domain, since its input norm only transports the
supported tensor through its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

/-- Changing the auxiliary domains used to prove smoothness does not change
the supported combined quadratic target. -/
theorem combinedQuadraticTarget_domain_independent {n : ℕ} {ι : Type*}
    {D D' : Set Base} {O O' : Set LowJet} (hD : IsOpen D) (hD' : IsOpen D')
    (hO : IsOpen O) (hO' : IsOpen O') (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k j, (P k j).SmoothCoeffs O) (hP' : ∀ k j, (P k j).SmoothCoeffs O')
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) {K : ι → Compacts Base}
    (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i))
    (hGO : Set.MapsTo (lowJet G) D O) (hGO' : Set.MapsTo (lowJet G) D' O')
    (l : QuadraticLabel ι) (hKD : (quadraticCompacts K l : Set Base) ⊆ D)
    (hKD' : (quadraticCompacts K l : Set Base) ⊆ D') (ε τ t : ℝ) :
    combinedQuadraticTarget hD hO P hP hG φ hφ H hGO l hKD ε τ t =
      combinedQuadraticTarget hD' hO' P hP' hG φ hφ H hGO' l hKD' ε τ t := by
  apply DFunLike.ext
  intro x
  rfl

/-- A constant chosen before the map and scales bounds the actual perturbed
quadratic target in any corresponding quadratic-phase solver norm. -/
theorem combined_quadratic_solver_input_bound {n : ℕ} {ι : Type*}
    {D : Set Base} {O Q : Set LowJet} (hD : IsOpen D) (hO : IsOpen O)
    (hQ : IsCompact Q) (hQO : Q ⊆ O) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k j, (P k j).SmoothCoeffs O) (m : ℕ) (B F M A : ℝ)
    (hB : 1 ≤ B) (hF : 0 ≤ F) (hM : 0 ≤ M) (hA : 0 < A) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G)
      (φ : ι → Base → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
      (K : ι → Compacts Base) (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i))
      (s : ℝ≥0) (δ τ ε : ℝ), 0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ tensorLoss P ≤ 1 →
      (hGQ : Set.MapsTo (lowJet G) D Q) →
      WeightedBound D s (m + tensorOrder P) B (lowJet G) →
      (∀ i, WeightedBound Set.univ s (m + tensorOrder P + 1) (A * (δ * τ)) (H i)) →
      (∀ i v, WeightedBound D s (m + tensorOrder P) F
        (fun x => fderiv ℝ (φ i) x (coordinateVector v))) →
      (∀ i v, ‖v‖ ≤ 1 → WeightedBound Set.univ s m M
        (SmallModes.coordDeriv v (coordinatePhase (φ i)))) →
      ∀ (l : QuadraticLabel ι) (hKD : (quadraticCompacts K l : Set Base) ⊆ D)
        (c : PolynomialSolveData P ε G hG (quadraticFamilyPhase φ l)
          (quadraticCompacts K l) τ s) (I : ℕ → ℝ),
      (∀ j, 1 ≤ I j) →
      (∀ a j, 1 ≤ j → j ≤ a → ∀ x ∈ c.e.target,
        ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ I a) →
      c.norm (combinedQuadraticTarget hD hO P hP hG φ hφ H
        (fun _ hx => hQO (hGQ hx)) l hKD ε τ 0) m ≤
        δ ^ 2 * tensorChartBudget m (I m) (I (m + 1)) * E := by
  obtain ⟨E,hE,he⟩ := combinedQuadraticTarget_bounds (ι := ι)
    hD hO hQ hQO P hP m B F M A hB hF hM hA
  refine ⟨E,hE,?_⟩
  intro G hG φ hφ K H s δ τ ε hδ hτ hs hτs hs1 hε hε1 hsmall
    hGQ hGb hHb hφb hφm l hKD c I hI hcoords
  have ht := he hG φ hφ K H s δ τ ε hδ hτ hs hτs hs1 hε hε1 hsmall
    hGQ hGb hHb hφb hφm l hKD
  have hn := c.norm_le_of_weightedBound hs hs1 I hI hcoords m
    (mul_nonneg (sq_nonneg δ) hE) _ ht
  calc
    _ ≤ tensorChartBudget m (I m) (I (m + 1)) * (δ ^ 2 * E) := hn
    _ = _ := by ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
