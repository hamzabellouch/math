import Mathlib
import OAI.Analysis.AffineBernstein.ActualLogCells
import OAI.Analysis.AffineBernstein.ModelPositiveLogMass

namespace OAI

noncomputable section

namespace AffineBernstein
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Metric Filter
/-- The actual analytic contradiction excludes every normalized maximal model
with at least two orthant directions. None of its mass bounds is an assumption. -/
theorem affineMaximal_no_normalized_maximal_model {n k m d : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (e : Fin n ≃ Fin k ⊕ Fin d) (eE : Fin m ≃ Fin d ⊕ Unit)
    (f : WithLp 2 (Space d × ℝ) ≃ₗᵢ[ℝ] Space m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hmP : AffineMaximalOn Ω u)
    (hcomplete : EuclideanGraphComplete Ω u)
    (hmax : ∀ d' : ℕ, m = d'+1 → ∀ C' : Set (Space (k+1) × Space d'),
      IsModelShape C' → InAffineLimitFamily (sourceEpigraph Ω u) C' → False)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {C : Set (Space k × Space m)} (hC : IsModelShape C)
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C)
    (hlim : LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C)
    {r R₀ : ℝ} (hr : 0 < r)
    (hin : closedBall (0:Space m) r ⊆ modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R₀) : False := by
  let : NeZero m := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n := by
    have hh := Fintype.card_congr e
    simp only [Fintype.card_fin,Fintype.card_sum] at hh
    omega
  let D := fun j => regularPositiveFiberDomain (affineEpigraphPullback Ω u (a j) (L j))
  let bE := (EuclideanSpace.basisFun (Fin m) ℝ).reindex eE
  obtain ⟨T,c,hc,hpos⟩ := normalized_model_positive_log_mass hn1 hk1 hm e eE f
    hΩ hne hcv hu hp hmP hcomplete a L hC hlim hr hin hout
  obtain ⟨Cσ,hCσ,hcell⟩ := maximal_model_uniform_log_cells hn1 hk1 hm e eE f
    hΩ hne hcv hu hp hmP hcomplete hmax
  have hclosed := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have hclj j : IsClosed (affineEpigraphPullback Ω u (a j) (L j)) := affineEpigraphPullback_isClosed hclosed _ _
  have hcvj j : Convex ℝ (affineEpigraphPullback Ω u (a j) (L j)) :=
    ((sourceEpigraph_convex hΩ hcv hu hp).translate_preimage_right (a j)).linear_preimage (L j).toLinearMap
  have hnej j : (affineEpigraphPullback Ω u (a j) (L j)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    refine ⟨(L j).symm ((x,u x)-a j),?_⟩
    change (a j + (L j) ((L j).symm ((x,u x)-a j))).1 ∈ Ω ∧ _
    simp [hx]
  refine affineMaximal_no_eventual_bounded_log_cells hn hn9 hk hkn (fun _ => Ω) (fun _ => u) a L D bE
    (fun _ => hΩ) (fun _ => hcv) (fun _ => hu) (fun _ => hp) (fun _ => hmP)
    (fun _ => regularPositiveFiberDomain_isOpen _)
    (fun _ => regularPositiveFiberDomain_positive _)
    (fun _ _ hs => regularPositiveFiberDomain_compact _ hs)
    (fun _ _ hs => regularPositiveFiberDomain_zero _ hs) (l₀ := T) ?_ hc hCσ hpos ?_
  · intro R _
    exact hlim.eventually_regular_logBox hC hclj hcvj hnej hr hin hout R
  · exact hcell C hC hf a L hlim D (fun _ => regularPositiveFiberDomain_positive _)

/- Coordinate Hessian. On the open domain it depends only on the restriction of `u`.
The order of the two differentiations is immaterial under the smoothness hypothesis. -/
/- The coefficient U^{ij} = det(D²u) (D²u)^{-1}_{ij}. -/
/- The classical determinant weight; in particular, this is not a generalized exponent. -/
/- Length on [0,1] for g_x(v,v) = ‖v‖² + (Du_x v)², the metric induced
by the Euclidean graph embedding x ↦ (x,u(x)). The product norm on Lean's ordinary
product type is NOT used (it would be the maximum norm). -/
/- The intrinsic extended distance: infimum of lengths of C¹ paths in the domain.
Using a single C¹ path gives the same intrinsic distance as piecewise C¹ paths,
by smooth endpoint reparameterization and concatenation. -/
/- Sequential completeness for the induced Euclidean path metric. This states
that every intrinsic Cauchy sequence of points in Ω has an intrinsic limit in Ω.
It imposes no growth condition and no completeness condition on the affine metric. -/
/- The graph, regarded as an affine subset of R^{n+1}. -/

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

/- Quantitative inner containment from distance-function closeness. This is
an actual projection argument for convex bodies, not an assumed stability axiom. -/
/- An interior ball of the limit has a fixed smaller ball lying in the
interiors of all late approximants. -/
/- Compact subsets of the interior are eventually interior subsets of the
approximants, as required by the model normalization argument. -/

open Filter Metric
open scoped Topology Pointwise

/- The geometric conditions of a k-model, in its distinguished coordinates.
Membership in the affine local-limit family is separate from these conditions. -/
/- The transverse fiber, including lower-dimensional and boundary fibers. -/
/- The ray containment recession argument in geometry.tex does not need
full-dimensionality. -/
namespace IsModelShape

variable {k m : ℕ} {C : Set (Space k × Space m)} (h : IsModelShape C)
include h

/- Every strictly positive fiber is full dimensional; this proof also covers
m=0, using the ordinary topology of the zero-dimensional space. -/
/- Monotonicity and homothety turn a bound on the distinguished fiber into
a uniform bound on every fixed base box. -/
end IsModelShape

/- Normalized model limits retain the genuine geometric model conditions.
The fixed inner balls prevent collapse; the distinguished-fiber outer bound
controls every cap by the already proved recession/fiber inequalities. -/
/- The shrinking factor avoids any positivity assumption on approximating
base coordinates. It tends to one and contracts each coordinate below one. -/
/- Exact-fiber approximation in geometry.tex:285–300. The actual contracting
points are used, not an assumed commutation of slicing with local limits. -/
/- Uniform reverse Hausdorff inclusion follows by compactness of the actual
positive limit fiber and the preceding exact approximations. -/
/- Exact-fiber Hausdorff convergence with a common outer radius. This is
stronger than pointwise local convergence but follows from the model recession
structure; arbitrary slices of arbitrary converging bodies need not converge. -/
/- A failure of all growing centering constants forces the origin onto the
boundary of the limit fiber. No centering stability is assumed. -/
/- A fiber support at zero extends to the whole model by the same actual
contraction and recession operation used for exact-fiber approximation. -/
/- The nonzero supporting functional whose new positive coordinate is used
in the thin-slice blowup. Hahn–Banach is reused from pinned Mathlib. -/

/- For distance functions, pointwise convergence is automatically locally
uniform, by the common unit Lipschitz constant and a finite compact cover. -/
/- Fixed changes of coordinates preserve local set convergence. A proper
homeomorphism suffices: compact preimages supply the lower distance bound and
actual approximating points supply the upper bound. In particular this applies
to every fixed invertible affine change of coordinates. -/
/- A diagonal choice of approximating bodies. The bounds on the growing
closed balls are the literal metric construction behind the affine-family
closure assertion, not an assumed transitivity of sequential limits. -/
/- Literal full-dimensional affine local-limit family of geometry.tex:87.
The affine maps may vary along the approximating sequence. -/

open scoped Pointwise

/- The coordinate action of the actual matrix linear equivalence. -/
/- A convex combination allowing unused mass at the origin. -/
/- The cross-polytope spanned by any points of a symmetric convex body lies
in that body. This is the inner-inclusion half of max-determinant normalization. -/
/- The exact ℓ¹/Euclidean comparison used for the inner ball. -/
/- The exact ℓ∞/Euclidean comparison used for the outer ball. -/
/- A compact body's column determinant has a maximizer, with nonzero value
whenever the body contains a ball about zero. -/
/- Maximal determinant makes each inverse coordinate of a body point at most
one. The proof is the literal one-column replacement identity. -/
/- The symmetric max-determinant normalization, with the exact weaker radius
n sufficient for all centered normalizations used in the source. -/
open scoped Pointwise

/- Exact centered normalization in geometry.tex (2/(C+1), 2n), proved
without importing John's theorem: first normalize the symmetric difference
body, then use the actual balance inclusion. -/
/- A dimension-only inscribed ball in the standard simplex. This allows
noncentered model fibers to be normalized without importing John's theorem. -/
/- A linear normalization of an arbitrary full-dimensional compact convex
body containing the distinguished origin. The dimension-only outer radius
is intentionally not John's sharp radius; it suffices for the compactness
argument and does not alter the source's final centered normalization. -/
/- The same intermediate normalization with the zero-dimensional convention
made explicit. Its radii are only used in compactness arguments. -/

/- A nonzero real functional has full range. -/
/- A nonzero support is strictly positive at every interior point. -/
/- The literal split along a normalized support vector. The second component
is the kernel of the support; no quotient or degenerate coordinate is used. -/
/- Coordinates which keep the support as the first coordinate and send a
chosen interior point of a convex fiber to (1,0). Scaling the support, rather
than translating the body, preserves the ambient origin and all recession rays. -/

/- Append one real base coordinate, placing it first in Fin (k+1). -/
open Filter Metric
open scoped Topology Pointwise
variable {k d : ℕ}

/- The thin slices and rescalings in geometry.tex:304–332, before the harmless
reordering of the k+1 base coordinates. -/
/- Supports and the original orthant after a support-coordinate split. -/
namespace IsSupportedSplitModel
variable {C : Set (Space k × (ℝ × Space d))} (h : IsSupportedSplitModel C)
include h

/- Every slice at a sufficiently low positive support level contains a real
ball about zero, obtained by contraction of the interior ball at (1,0). -/
/- The decisive uniform cap bound. Its constant is exactly the source's
2*T*R for an arbitrary slice outer radius R (including d=0). -/
end IsSupportedSplitModel

/- Eventual membership of a fixed point is sufficient for passage to the
local limit, including initial rescalings on which it is not yet present. -/
/- All the geometric properties of the (k+1)-direction model supplied by the
thin-slice limit. The new base is still written (s,r), before reindexing it as
R^(k+1). This theorem includes the zero-dimensional transverse endpoint. -/

end AffineBernstein

end

end OAI
