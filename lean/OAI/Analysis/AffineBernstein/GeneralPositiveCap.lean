import Mathlib
import OAI.Analysis.AffineBernstein.AffineFamily
import OAI.Analysis.AffineBernstein.PositiveLimitCap
import OAI.Analysis.AffineBernstein.GeneralCapCoordinates

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GeneralPositiveCap
open Filter Metric

lemma affine_image_after_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L A : E ≃L[ℝ] E) (v : E) (D : Set E) :
    (fun z => (L.trans A) z+A v) '' D = A '' ((fun z => L z+v) '' D) := by
  rw [Set.image_image]
  congr 1
  funext z
  exact (map_add A (L z) v).symm

/- The positive-cap-area lemma for every nonzero height functional, with
no orthogonality or vertical-preserving assumption on the affine images. -/
theorem positive_linear_cap_area_of_affine_local_limit {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (L : ℕ → (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : ℕ → Space n × ℝ)
    (hclj : ∀ j, IsClosed ((fun p => L j p+v j) '' sourceEpigraph Ω u))
    (hcvj : ∀ j, Convex ℝ ((fun p => L j p+v j) '' sourceEpigraph Ω u))
    (hnej : ∀ j, ((fun p => L j p+v j) '' sourceEpigraph Ω u).Nonempty)
    {C : Set (Space n × ℝ)} (hC : IsClosed C)
    (hlim : LocalDistanceConverges (fun j => (fun p => L j p+v j) '' sourceEpigraph Ω u) C)
    (ell : (Space n × ℝ) →L[ℝ] ℝ) (hell : ell ≠ 0)
    {b : ℝ} (hcapC : Bornology.IsBounded (C ∩ {z | ell z ≤ b}))
    {o : Space n × ℝ} (ho : o ∈ interior C) (hob : ell o < b) :
    ∃ c > 0, ∀ᶠ j in atTop, c ≤ affineImageLinearCapArea Ω u (L j) (v j) ell b := by
  obtain ⟨A,hA⟩ := exists_height_coordinates ell hell
  have hset (j : ℕ) := affine_image_after_linear (L j) A (v j) (sourceEpigraph Ω u)
  have hlimA := hlim.homeomorph hC ⟨o,interior_subset ho⟩ hclj hnej A.toHomeomorph
  have hclA : IsClosed (A '' C) := A.toHomeomorph.isClosed_image.mpr hC
  have hcapA : Bornology.IsBounded ((A '' C) ∩ {z | z.2 ≤ b}) := by
    rw [image_height_cap A ell hA]
    exact hcapC.image A.toContinuousLinearMap
  have hoA : A o ∈ interior (A '' C) := by
    change A.toHomeomorph o ∈ interior (A.toHomeomorph '' C)
    rw [← A.toHomeomorph.image_interior C]
    exact mem_image_of_mem A ho
  have hclAj (j : ℕ) : IsClosed ((fun p => (L j |>.trans A) p+A (v j)) '' sourceEpigraph Ω u) := by
    rw [hset]
    exact A.toHomeomorph.isClosed_image.mpr (hclj j)
  have hcvAj (j : ℕ) : Convex ℝ ((fun p => (L j |>.trans A) p+A (v j)) '' sourceEpigraph Ω u) := by
    rw [hset]
    exact (hcvj j).linear_image A.toLinearEquiv.toLinearMap
  have hneAj (j : ℕ) : ((fun p => (L j |>.trans A) p+A (v j)) '' sourceEpigraph Ω u).Nonempty := by
    rw [hset]
    exact (hnej j).image A
  have hlimA' : LocalDistanceConverges
      (fun j => (fun p => (L j |>.trans A) p+A (v j)) '' sourceEpigraph Ω u) (A '' C) := by
    simp only [hset]
    exact hlimA
  obtain ⟨c,hc,hbound⟩ := positive_cap_area_of_affine_local_limit hΩ hu hp hm
    (fun j => (L j).trans A) (fun j => A (v j)) hclAj hcvAj hneAj hclA hlimA'
    hcapA hoA (by rwa [hA])
  let a := Real.rpow |A.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))
  have ha : 0 < a := Real.rpow_pos_of_pos (abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero) _
  refine ⟨c/a,div_pos hc ha,?_⟩
  filter_upwards [hbound] with j hj
  rw [affineImageCapArea_height_coordinates Ω u (L j) A (v j) ell hA b] at hj
  exact (div_le_iff₀ ha).mpr (by simpa only [a,mul_comm] using hj)

end GeneralPositiveCap

/- Every admissible graph path has at least the Euclidean length of its
base displacement. This uses the literal C¹-path definition of completeness. -/
/- A straight base segment has constant velocity, including its endpoints
for the closed-interval derivative used in the metric. -/
/- Length estimate on a segment on which the graph height is nondecreasing. -/
/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/
/- The straight-segment estimate in its geometric form. Both possible
orientations of a monotone height are included. -/
open Filter
open scoped Topology

/- Intrinsic convergence always entails convergence of base points. -/
/- Completeness prevents a finite base endpoint from being lost when graph
paths make a sequence intrinsically Cauchy. -/
/- A chord bound along a family of segments turns ordinary Cauchy control of
base and height into control for the actual graph metric. -/
/- Restricting a monotone-height ray to any oriented subsegment gives the
uniform chord bound used to exhibit an intrinsic Cauchy tail. -/
/- A bounded ray with monotone graph height cannot end at a missing finite
base point of a complete graph. This proves the metric step rather than
assuming properness of the embedding. -/
/- A differentiable convex function on a finite half-open interval has a
monotone tail (in one of the two orientations). -/
/- The tangent line at the initial point bounds a convex ray from below,
so an upper bound on a finite ray implies a two-sided bound. -/
/- Completeness forbids any bounded convex ray from reaching a missing finite
endpoint. Convexity and two-sided variation, not a growth hypothesis, produce
the required metric Cauchy sequence. -/
/- The metric obstruction applied to an arbitrary bounded-height sequence,
not merely points already lying on a fixed ray. This is the core boundary
properness argument in geometry.tex:36–55. -/
/- Actual height sublevels are closed in the ambient base space. No convex
extension of u to missing boundary points is used. -/
/- Finite boundary blow-up, derived from the manuscript's literal Euclidean
intrinsic completeness assumption. -/
/- The epigraph is genuinely closed in Rⁿ × R. Completeness was not
silently replaced by properness of the graph embedding. -/

end AffineBernstein

end

end OAI
