import OAI.Geometry.SurfaceImmersion.Correction.FinitePolynomialCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedQuadraticFamily
import OAI.Geometry.SurfaceImmersion.Correction.FreeForcedIncrementIdentity

namespace OAI

/-! Cancel the actual nonzero quadratic tensor of the free displacement,
including the polynomial Hessian, with the finite supported solver. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

theorem polynomial_quadratic_cancellation {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (K : ι → Compacts Base) (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i))
    {τ : ℝ} {s : ℝ≥0}
    (c : ∀ l, PolynomialSolveData P ε G hG (quadraticFamilyPhase φ l) (quadraticCompacts K l) τ s)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q : ℕ) :
    let f := fun l => combinedQuadraticTarget (c l).openU (c l).openO P (c l).smoothP hG φ hφ H
      (c l).mapsG l (c l).supportU ε τ 0
    ∃ V : RealModes.RField 4, ContDiff ℝ ∞ V ∧
      tsupport V ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m (∑ l, (c l).size (f l) q m) V) ∧
      (∀ m, WeightedBound Set.univ τ m (∑ l, (c l).residual (f l) q m)
        (coordinateFullLinearized P ε G V + combinedNonzeroQuadratic P ε G φ (fun i => H i) τ)) := by
  classical
  dsimp only
  let f := fun l => combinedQuadraticTarget (c l).openU (c l).openO P (c l).smoothP hG φ hφ H
    (c l).mapsG l (c l).supportU ε τ 0
  obtain ⟨V,hV,hsp,hb,hr⟩ := finite_polynomial_cancellation P ε hG (quadraticFamilyPhase φ)
    (quadraticCompacts K) c hτ hs hτs hs1 hε hsmall f q
  refine ⟨V,hV,hsp.trans ?_,hb,?_⟩
  · intro x hx
    obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hx
    rw [modeSupport_quadraticCompacts] at hl
    rcases l with i | ⟨i,j,b⟩
    · exact Set.mem_iUnion.mpr ⟨i,hl⟩
    · exact Set.mem_iUnion.mpr ⟨i,hl.1⟩
  · have he : (fun x => ∑ l, QuadraticMean.displacement τ
        (coordinatePhase (quadraticFamilyPhase φ l)) (f l) x) =
        combinedNonzeroQuadratic P ε G φ (fun i => H i) τ := by
      funext x
      apply Finset.sum_congr rfl
      intro l _
      have hp : coordinatePhase (quadraticFamilyPhase φ l) =
          RealModes.quadraticPhase (fun i => coordinatePhase (φ i)) l := by
        funext y
        exact coordinate_quadratic_phase φ l y
      rw [hp]
      rfl
    intro m
    apply (hr m).congr
    intro x _
    change coordinateFullLinearized P ε G V x + combinedNonzeroQuadratic P ε G φ (fun i => H i) τ x = _
    rw [← he]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
