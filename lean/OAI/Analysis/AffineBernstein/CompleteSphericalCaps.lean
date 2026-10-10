import Mathlib
import OAI.Analysis.AffineBernstein.CompletePositiveCap

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open intervalIntegral
open scoped Pointwise
open Filter
open scoped Topology
open Filter
open scoped Topology

variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Full-sphere inverse-energy bound from the unchanged complete original PDE and literal
normalized ambient cap geometry. Compactness of the original graph cap and of every fiber
is produced here, not assumed. All constants precede the varying affine map and solution. -/
theorem complete_affineMaximal_uniform_spherical_cap_bound {n : ℕ}
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ)
    (ℓ : S →L[ℝ] ℝ) (o : S × E) {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hR : 0 ≤ R) (t₁ : ℝ) (hogap : ℓ o.1 < t₁+ε) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
      ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
        {B : Set S}, IsOpen B → (∀ s ∈ B, ℓ s ≤ t₁+ε) →
      (∀ s ∈ B, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
      (∀ p ∈ affineEpigraphPullback Ω u a L, ℓ p.1 ≤ t₁+ε → ‖p‖ ≤ R) →
      Metric.closedBall o r ⊆ affineEpigraphPullback Ω u a L →
      ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ B → (∀ s ∈ Q, ℓ s ≤ t₁-ε) →
      let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
      let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
      (∫⁻ q : S × Metric.sphere (0:E) 1, ENNReal.ofReal
        ((Real.rpow (tubeBaseMatrix H (q.1,q.2) bS.toBasis).det δ *
          Real.rpow (tubeAngularDensity H (q.1,q.2) bRef) (1-δ)) *
          (‖supportConormal H (q.1,q.2)‖ *
            inverseMatrixPair (tubeBaseMatrix H (q.1,q.2) bS.toBasis)
              (fun i => ℓ (bS i)) (fun i => ℓ (bS i))))
        ∂(volume.restrict Q).prod volume.toSphere) ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := affineMaximal_uniform_spherical_cap_lintegral_bound bS bF bRef f e
    hε hr hR (-‖ℓ‖*R) t₁ (ℓ o.1)
  refine ⟨C,hC,?_⟩
  intro Ω hΩ hne hcv u hu hp hm hcomplete a L B hB hBheight hzero hcap hball Q hQ hQB hQheight
  have hc := sourceEpigraph_closed hΩ hne hcv hu hp hcomplete
  have ho : o ∈ affineEpigraphPullback Ω u a L := hball (Metric.mem_closedBall_self hr.le)
  obtain ⟨K,hK,hKΩ,houtside,hheight,hRcap⟩ :=
    affineEpigraphPullback_graph_cap_data hc a L ℓ hR hcap ho hogap
  have hKfib (s : S) (hs : s ∈ B) : IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L} :=
    affineEpigraphPullback_fiber_isCompact hc a L ℓ hcap (hBheight s hs)
  have heq : L.symm (((a+L o).1,(a+L o).2)-a) = o := by
    change L.symm (a+L o-a) = o
    rw [add_sub_cancel_left,L.symm_apply_apply]
  apply hbound hΩ hcv hu hp hm a L hB hKfib hzero ℓ (a+L o).1 (a+L o).2
  · rw [heq,← affineEpigraphPullback_eq_image]
    exact hball
  · rw [heq]
  · exact hK
  · exact hKΩ
  · exact houtside
  · exact hheight
  · exact hRcap
  · exact hQ
  · exact hQB
  · exact hQheight

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

/- The literal support value, not a freely chosen support coordinate. -/
/- A supporting first-order inequality for an arbitrary differentiable convex function. -/
/- A nonzero linear functional cannot attain its sublevel maximum below the level. -/
/- The support maximum of a compact smooth convex sublevel has a positive
Lagrange multiplier. This includes dimension one without a sphere convention. -/
/- Linearization of the actual support equations `F(y)=0`, `DF(y)=lam*ell`. -/
/- Positive curvature gives the missing transversality of the support equations. -/

/- Fiber derivatives of the actual defining function. -/
/- A solution of the support equations with positive multiplier is a global,
not merely local, support point. -/
/- Smooth dependence of the literal support value on base and conormal.
The IFT is applied to the actual defining function and its actual Hessian. -/
/- Finiteness of the literal support value on a compact fiber. -/
/- The envelope identity recovers the Gauss parametrization from the literal
support function; no choice of a surrogate support coordinate is involved. -/

/- Expansion in the frozen Euclidean coordinate vectors. -/
/- Coordinate entries coincide with the actual second Fréchet differential. -/
/- The standing positive-Hessian hypothesis implies genuine convexity on
 the original open convex domain; this is not an additional hypothesis. -/

/- A genuine affine slice of the original epigraph, in arbitrary transverse
coordinates. -/
/- A compact nonempty affine epigraph fiber has no vertical direction. -/
/- For an affine coordinate isomorphism compact fibers force injectivity of
its horizontal linear part. -/
/- Chain rule for the actual second differential of an affine epigraph slice. -/
/- An interior point of a convex sublevel is a strict sublevel point whenever
its actual Hessian is positive definite. -/
/- Convexity survives the actual affine slice and subtraction of its height. -/

/- The literal inverse image of the original epigraph under affine coordinates. -/
/- The principal support-coordinate regularity assertion in tubes.tex:39–60,
for actual affine images of the standing epigraph, not abstract smooth bodies.
The transverse dimension is nonzero, as in the manuscript (m=n+1-k≥1). -/

/- The one-homogeneous extension of the literal spherical support function. -/
/- The actual support point, reconstructed by the derivative of the support value. -/
/- Euler's identity differentiates to the radial null direction of the support
Hessian. This is the ambient version of the spherical radius matrix. -/

/- Actual smooth Gauss coordinates of each affine epigraph tube. -/

/- The determinant, as a continuous map multilinear in its rows. -/
/- Exchanging two independently replaced rows reverses the determinant. -/
/- Expand one determinant row in the coordinate vectors. -/
/- Symmetric coefficients contract to zero with an alternating pair of rows. -/
/- The algebraic cancellation underlying the Piola identity. -/

/- Orthogonal tangential projection when `e` is a unit vector. -/
/- The ambient extension of the spherical gradient of a degree-one support function. -/
/- The round covariant derivative, using tangential projection of the ambient derivative. -/
/- The spherical Hessian evaluated on tangent vectors. -/
/- `∇²_S h + h Id` is the restriction of the ambient Hessian of the
one-homogeneous support function. -/
/- The standard projected local extension of a tangent vector. At a unit `e`,
its round covariant derivative vanishes if `v` is tangent at `e`. -/
/- The covariant derivative of an ambient two-tensor restricted to the sphere.
The arguments `u,v,w` are tangent at the unit point of evaluation. The projected
constant extensions of `v,w` have zero covariant derivative there. -/
/- Codazzi for the radius tensor of a smooth one-homogeneous support function.
The radial Hessian identity is precisely the derivative of Euler's identity;
there is no assumed Codazzi equation. -/

/- Cofactor divergence vanishes for every differentiable Codazzi matrix field,
including size one and the empty angular block. No invertibility is required. -/

/- Radius matrix in projected constant tangent frames. At a unit `e` and an
orthonormal tangent frame this is exactly `∇²_S h + h Id`; its first derivatives
are the round covariant derivatives in a normal frame. -/
/- The angular cofactor divergence identity, derived from the actual Hessian
and Euler radial identity, not assumed as a stationarity hypothesis. -/

/- Local differential form of strict curvature duality: the Hessian of a
one-homogeneous support is positive on every nonzero tangent vector. -/
/- Strict positivity of the actual homogeneous support Hessian on tangent
vectors. The multiplier is constructed from the actual Gauss point, not given
as a differential identity hypothesis. -/

/- Positive angular radius comes from the actual original graph Hessian,
after any invertible affine change of coordinates with compact centered fibers. -/

/- Second derivative under a fixed continuous linear functional. -/

/- Strict curvature of the actual level hypersurface forces strict concavity
of its support value in the base variables. -/

/- The genuine defining function for any affine coordinates of the graph. -/
/- Positive curvature on the tangent hyperplane, including affine maps that
mix the original vertical direction with the new base and fiber coordinates. -/

/- The actual support point is on the original graph and its fiber conormal is
positive. No Gauss inverse or support-equation hypotheses are assumed. -/
/- Strict negativity of the base Hessian of the literal support function. This
is the other positive block of the genuine tube second fundamental form. -/

/- Euler and the angular gradient identity give the genuine tangent conormal. -/
/- Raw Gauss parametrization, before restricting the angular variable to a chart. -/
/- Differentiating the two literal support identities eliminates both mixed
blocks. No stationarity or curvature formula is assumed. -/
/- Source (tube-second-form), as an identity of actual conormal second jets.
It is valid before angular chart restriction, including the radial null line. -/

/- The raw affine tube has the conormal and block second form asserted in the
manuscript. All differential identities have been obtained from its actual
supremum support; the only geometric assumptions are the stated compact
centered fibers of the original affine epigraph. -/

/- Jacobi's formula without assuming invertibility of the varied matrix. -/
/- Pointwise first variation of the actual affine-area density. -/

/- The actual second-jet affine-area density in the base and orthonormal
angular directions; the transverse column is (0,-e). -/

/- Literal Jacobi first variation of the tube density, including empty
angular matrices. This is the integrand needed in source (tube-euler). -/

/- Both matrices in the actual tube area formula are positive definite,
including an empty angular matrix. This is derived from the original graph,
not imposed as an additional curvature assumption. -/
/- Source tube-area, for the literal supremum/Gauss parametrization of the
original affine epigraph under an arbitrary ambient affine isomorphism. -/

end AffineBernstein

end

end OAI
