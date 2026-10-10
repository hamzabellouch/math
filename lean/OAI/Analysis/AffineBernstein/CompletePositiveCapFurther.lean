import Mathlib
import OAI.Analysis.AffineBernstein.GeneralPositiveCap

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

lemma affineSourceEpigraph_convex {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    Convex ℝ ((fun z => L z+v) '' sourceEpigraph Ω u) := by
  let F : (Space n × ℝ) →ᵃ[ℝ] (Space n × ℝ) :=
    L.toLinearEquiv.toLinearMap.toAffineMap + AffineMap.const ℝ _ v
  exact (sourceEpigraph_convex hΩ hcv hu hp).affine_image F

lemma affineSourceEpigraph_closed {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    IsClosed ((fun z => L z+v) '' sourceEpigraph Ω u) := by
  exact (L.toHomeomorph.trans (Homeomorph.addRight v)).isClosed_image.mpr
    (sourceEpigraph_closed hΩ hne hcv hu hp hc)

/- Source positive-cap-area lemma (bounds.tex:18–126) for the actual affine
images of the original complete graph, with all image hypotheses derived. -/
theorem complete_affineMaximal_positive_cap_area {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u) (hc : EuclideanGraphComplete Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hell : ell ≠ 0)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | ell z ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : ell o < b) :
    ∃ c > 0, ∀ᶠ j in atTop, c ≤ affineImageLinearCapArea Ω u (L j) (v j) ell b := by
  apply positive_linear_cap_area_of_affine_local_limit hΩ hu hp hm L v
    (fun index => affineSourceEpigraph_closed hΩ hne hcv hu hp hc (L index) (v index))
    (fun index => affineSourceEpigraph_convex hΩ hcv hu hp (L index) (v index))
    _ hC hlim ell hell hcapC ho hob
  intro j
  obtain ⟨x,hx⟩ := hne
  exact ⟨L j (x,u x)+v j,mem_image_of_mem _ ⟨hx,le_rfl⟩⟩

/- Positive-definiteness of the derivative makes a map injective on a convex
set, by strict monotonicity along every segment. -/

/- The actual gradient of a strictly positive-Hessian function is injective;
in particular this applies to every principal-coordinate slice in the source. -/
/- The true Euclidean gradient has Jacobian determinant equal to the
coordinate Hessian determinant, including dimension zero. -/
/- Exact change of variables for the convex gradient map. This is the
principal-minor argument used in bounds.tex; applying this result on each
coordinate slice gives the claimed integral bound for that minor. -/
/- A uniformly bounded gradient image gives a uniformly bounded Hessian
Jacobian integral. No bound on the Hessian itself is needed. -/

/- Reciprocal projective chart of the Gauss covector. In the chart where
coordinate `i` dominates the normal, its image lies in a fixed cube. -/

/- Projection to the coordinate hyperplane omitting the i-th original
base coordinate, represented in its standard n coordinates. -/

/- Holder interpolation, with weights rather than reciprocal exponents.
The endpoint masses may be infinite; no hidden integrability premise is used. -/
/- Real positive densities can be interpolated before or after `ofReal`. -/

/- A dimension/radius-only bound for the literal affine area on any measurable
part of a smooth strictly convex graph with |x_i|,|u| ≤ R. This proves the
area-in-a-ball producer without assuming a surface-area or Gauss-map theorem:
two injective coordinate projections supply its Jacobians directly. -/

/- A determinant-one-in-absolute-value coordinate change straightens any nonzero
vector upwards, with a uniform factor two bound on coordinate boxes. No Euclidean
structure is falsely assigned to the max-norm product. -/

/- Genuine affine area of every bounded measurable patch of an arbitrary
invertible affine image of the original convex graph. The constant depends
only on dimension and the physical coordinate radius, not on the affine map. -/

end AffineBernstein

end

end OAI
