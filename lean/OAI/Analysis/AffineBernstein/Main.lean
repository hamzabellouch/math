import Mathlib
import OAI.Analysis.AffineBernstein.HessianDominance
import OAI.Analysis.AffineBernstein.ConstantHessianQuadratic
import OAI.Analysis.AffineBernstein.QuadraticAffineImage

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal


/-- Literal main theorem, with its stated affine-image consequence. -/
theorem affine_bernstein
    (n : ℕ) (hn₃ : 3 ≤ n) (hn₉ : n ≤ 9)
    (Ω : Set (Space n)) (hΩne : Ω.Nonempty) (hΩopen : IsOpen Ω)
    (hΩconvex : Convex ℝ Ω) (u : Space n → ℝ)
    (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hmax : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u) :
    Ω = univ ∧
      (∃ (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (c : ℝ),
        A.IsSymm ∧ A.PosDef ∧
        ∀ x, u x = (1 / 2 : ℝ) * (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j)
          + (∑ i : Fin n, b i * x i) + c) ∧
      (∃ e : (Space n × ℝ) ≃ᵃ[ℝ] (Space n × ℝ),
        e '' standardParaboloid n = graph Ω u) := by
  obtain ⟨hU,ρ,hρ,hρ1,hbal⟩ := affineMaximal_entire_and_balance hn₃ hn₉ hΩopen hΩne
    hΩconvex hu hpos hmax hcomplete
  refine ⟨hU,?_⟩
  subst Ω
  have hu' : ContDiff ℝ ∞ u := contDiffOn_univ.mp hu
  have hp' : ∀ x, (hessian u x).PosDef := fun x => hpos x (mem_univ x)
  have hH := balanced_constant_hessian (by omega) hu' hp' hmax hρ hρ1 hbal
  have hq := quadratic_of_constant_hessian hu' hH
  constructor
  · refine ⟨hessian u 0, WithLp.toLp 2 (fun i => fderiv ℝ u 0 (coordinateVector n i)), u 0,
      Matrix.isHermitian_iff_isSymm.mp (hp' 0).isHermitian, hp' 0, ?_⟩
    intro x
    change u x = (1/2:ℝ)*(∑ i, ∑ j, x i*hessian u 0 i j*x j) +
      (∑ i, fderiv ℝ u 0 (coordinateVector n i)*x i) + u 0
    rw [← continuousLinearMap_coordinate_sum]
    exact hq x
  · exact quadratic_graph_affine_image (hp' 0) (fderiv ℝ u 0) (u 0) hq



end
end AffineBernstein

end

end OAI
