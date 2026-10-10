import Mathlib
import OAI.Analysis.AffineBernstein.CapArea
import OAI.Analysis.AffineBernstein.AffineCapGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section AffineCapArea

/- Uniform positive area for genuine affine images of the original solution.
The only uniform geometric data are a bounded compact cap and an interior ball
strictly below its top. This joins the source ray, shear and smooth-cap arguments. -/
theorem exists_uniform_positive_affine_cap_area (n : ℕ) {ε r R : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Set (Space n)) (u : Space n → ℝ)
      (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v o : Space n × ℝ) (b : ℝ),
      IsOpen Ω → ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
      IsCompact {z | z ∈ (fun p => L p+v) '' sourceEpigraph Ω u ∧ z.2 ≤ b} →
      (∀ z ∈ (fun p => L p+v) '' sourceEpigraph Ω u, z.2 ≤ b → ‖z‖ ≤ R) →
      (Metric.ball o r ⊆ (fun p => L p+v) '' sourceEpigraph Ω u) →
      o.2 ≤ b-6*ε → C ≤ affineImageCapArea Ω u L v b := by
  let P : ℝ := (2*R+1)/(6*ε)
  let R' : ℝ := (1+P)*R
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨C,hC,huniform⟩ := exists_uniform_positive_graph_cap_area n (R := 2*R') hε hr
  refine ⟨C,hC,?_⟩
  intro Ω u L v o b hΩ hu hp hm hK hcap hball hgap
  let D := (fun p => L p+v) '' sourceEpigraph Ω u
  have ho : o ∈ D := hball (Metric.mem_ball_self hr)
  obtain ⟨hcpos,hpbound⟩ := affineEpigraph_positive_vertical L v hR
    (show 0 < 6*ε by positivity) hcap ho hgap
  let c := (L (0,1)).2
  let p := c⁻¹ • (L (0,1)).1
  let S := verticalShear p
  let M := L.trans S
  let w := S v
  have hMV : M (0,1) = ((0 : Space n),c) :=
    verticalShear_straightens (L (0,1)) hcpos.ne'
  let B := triangularBaseEquiv M hMV hcpos.ne'
  let Ω' := {y | B.symm (y-w.1) ∈ Ω}
  let g := triangularGraphFunction u M hMV hcpos.ne' w
  have hepi : sourceEpigraph Ω' g = S '' D := by
    rw [← triangular_sourceEpigraph_image Ω u M hMV hcpos w]
    exact affine_image_after_shear p L v (sourceEpigraph Ω u)
  obtain ⟨hΩ',hg,hpg,hmg⟩ := triangularGraph_regular hΩ hu hp hm M hMV hcpos w
  have hcapS : ∀ z ∈ sourceEpigraph Ω' g, z.2 ≤ b → ‖z‖ ≤ R' := by
    intro z hz hzb
    rw [hepi] at hz
    obtain ⟨y,hy,rfl⟩ := hz
    have hyb : y.2 ≤ b := hzb
    calc
      ‖S y‖ ≤ (1+‖p‖)*‖y‖ := norm_verticalShear_le p y
      _ ≤ (1+P)*R := mul_le_mul (by change 1+‖p‖ ≤ 1+P; linarith [hpbound])
        (hcap y hy hyb) (norm_nonneg y) (by linarith)
  have hKS : IsCompact {z | z ∈ sourceEpigraph Ω' g ∧ z.2 ≤ b} := by
    rw [hepi,shear_image_cap]
    exact hK.image S.continuous
  have hgK : IsCompact {x | x ∈ Ω' ∧ g x ≤ b} :=
    isCompact_graph_sublevel_of_cap (by simpa only [sourceEpigraph, Set.mem_ofPred_eq, and_assoc] using hKS)
  have hbase : ∀ x ∈ Metric.ball (S o).1 r, x ∈ Ω' ∧ g x ≤ b-6*ε := by
    intro x hx
    have hz := shear_horizontal_ball p hball x hx
    rw [← hepi] at hz
    exact ⟨hz.1,hz.2.trans hgap⟩
  have hocap : ‖(S o).1‖ ≤ R' := by
    apply (norm_fst_le (S o)).trans
    apply hcapS
    · rw [hepi]; exact ⟨o,ho,rfl⟩
    · change o.2 ≤ b
      linarith
  have hbound := graph_cap_radius_bound hocap
    (fun z hz hgz hzb => hcapS z ⟨hz,hgz⟩ hzb)
  have h := huniform Ω' g b (S o).1 hΩ' hg hpg hmg hgK hbase hbound
  have heq := triangular_graph_cap_area hΩ hu hp M hMV hcpos w b
  change (∫ x in {x | x ∈ Ω' ∧ g x < b}, affineAreaDensity g x) = _ at heq
  rw [heq] at h
  simpa only [M,w,S,affineImageCapArea_shear] using h

end AffineCapArea

section ConvexLocalLimits
open scoped Topology NNReal

open Filter Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- The local distance-function topology used in geometry.tex:70–101. Sets
are separately required to be nonempty and closed when those properties enter. -/
/- Every point of a local limit has an actual sequence of nearby points
in the approximating closed convex bodies (convexity is not needed here). -/
/- Local convergence prevents approximants from meeting any fixed compact
set disjoint from the closed limit. -/
/- Limits of convergent points of approximants belong to the local limit. -/
/- Uniform cap compactness, geometry.tex:104–125. The proof traps a chord
on a fixed compact sphere, rather than choosing escaping directions. -/
/- A point on the top of a limit cap is approximated from strictly below
its top by contracting toward a fixed strict point. -/
/- Reverse Hausdorff inclusion for a compact cap. -/
/- Full Hausdorff cap convergence, geometry.tex:104–125, with no asserted
smoothness of the limiting boundary. -/
/- Compactness of the bounded-at-one-point nonnegative unit-Lipschitz
family in the compact-open topology. This is the actual Arzelà–Ascoli input
for local convex-set compactness. -/
/- Extract locally uniformly convergent distance functions. At this stage
we do not yet assert that the limit is a distance function. -/
/- A pointwise limit of nonnegative unit-Lipschitz distance functions of
nonempty closed sets, on a proper space, is itself their zero-set's distance
function. Nearest points supply the nonempty zero set and attain the distance. -/
/- Local compactness of nonempty closed convex sets meeting a fixed bounded
set, the extraction used in geometry.tex:70–101. The topology and the limit
are literal sets and Euclidean distance functions. -/
end ConvexLocalLimits

open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- Normed-space inner containment. In particular this applies to the literal
product coordinates used for the epigraph, whose norm is not a Hilbert norm. -/

end AffineBernstein
end

end OAI
