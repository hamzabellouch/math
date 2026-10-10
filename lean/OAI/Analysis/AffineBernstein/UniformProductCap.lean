import Mathlib
import OAI.Analysis.AffineBernstein.UniformFlatCap
import OAI.Analysis.AffineBernstein.FlatProductCoordinates

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The original PDE cap bound in literal base times flat-projective fiber coordinates.
No measurability or integrability of the energy is assumed in this conversion. -/
theorem affineMaximal_uniform_product_cap_lintegral_bound {n : ℕ}
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ) {ε r R : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hR : 0 ≤ R) (t₀ t₁ c₀ : ℝ) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Convex ℝ Ω →
    ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
    (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u →
    ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
      {B : Set S}, IsOpen B →
    (∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    (∀ s ∈ B, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
    ∀ (ℓ : S →L[ℝ] ℝ) (o : Space n) (c : ℝ),
    Metric.closedBall (L.symm ((o,c)-a)) r ⊆
      (fun p => L.symm (p-a)) '' sourceEpigraph Ω u →
    ℓ (L.symm ((o,c)-a)).1 = c₀ →
    ∀ {K : Set (Space n)}, IsCompact K → K ⊆ Ω →
    (∀ x ∈ Ω, x ∉ K → t₁+ε ≤ pulledBaseGraphFunction u a L ℓ x) →
    (∀ x ∈ K, pulledBaseGraphFunction u a L ℓ x ∈ Icc t₀ (t₁+ε)) →
    (∀ x ∈ K, ‖L.symm ((x,u x)-a)‖ ≤ R) →
    ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ B →
    (∀ s ∈ Q, ℓ s ≤ t₁-ε) →
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let bE := flatProductFiberBasis bF f
    let δ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    (∫⁻ q : S × F, ENNReal.ofReal (tubeAreaDensity
      (tubeBaseMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bS.toBasis)
      (tubeRadiusMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bE) δ *
      (‖supportConormal H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ))))‖ *
        inverseMatrixPair (tubeBaseMatrix H (q.1,f (WithLp.toLp 2 (q.2,(1:ℝ)))) bS.toBasis)
          (fun i => ℓ (bS i)) (fun i => ℓ (bS i)))) ∂(volume.restrict Q).prod volume) ≤
        ENNReal.ofReal C := by
  let bE := flatProductFiberBasis bF f
  obtain ⟨C,hC,hcap⟩ := affineMaximal_uniform_flat_cap_lintegral_bound bS.toBasis bE e
    hε hr hR t₀ t₁ c₀
  refine ⟨C,hC,?_⟩
  intro Ω hΩ hcv u hu hp hm a L B hB hKfib hzero ℓ o c hball hcenter
    K hK hKΩ houtside hheight hbound Q hQ hQB hQheight
  let Z := flatProductCoordinates bS bF e
  let J := (flatProductEmbedding (S:=S) f).comp Z.toContinuousLinearMap
  let q₀ : S × E := (0,f (WithLp.toLp 2 (0,(1:ℝ))))
  have hq (x : Space n) : q₀+J x = ((Z x).1,f (WithLp.toLp 2 ((Z x).2,(1:ℝ)))) :=
    flatProductEmbedding_affine f (Z x)
  have hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1 := by
    simp only [q₀,bE,flatProductFiberBasis_last,f.inner_map_map]
    simp
  have hJ : Function.Injective J := (flatProductEmbedding_injective f).comp Z.injective
  have hJvert (x : Space n) : inner ℝ (J x).2 (bE (Sum.inr ())) = 0 :=
    flatProductEmbedding_vertical bF f (Z x)
  have hJe (i : Fin n) : J (coordinateVector n i) = tubeTangent bS.toBasis bE (e i) := by
    change flatProductEmbedding f (Z (coordinateVector n i)) = _
    rw [flatProductCoordinates_basis]
    rcases e i with j | j <;> simp [tubeTangent,bE]
  obtain ⟨φ,hsource,ht,hφ,hψ,heφ,henergy⟩ := hcap hΩ hcv hu hp hm a L hB hKfib hzero
    q₀ hd J hJ hJvert hJe ℓ o c hball hcenter hK hKΩ houtside hheight hbound
  let T : Set (S × F) := Q ×ˢ univ
  have hT : MeasurableSet T := hQ.prod MeasurableSet.univ
  have hZT : MeasurableSet (Z ⁻¹' T) := hT.preimage Z.continuous.measurable
  have hZsource : Z ⁻¹' T ⊆ φ.source := by
    intro x hx
    rw [hsource]
    change (q₀+J x).1 ∈ B
    rw [hq]
    exact hQB hx.1
  have hZheight (x : Space n) (hx : x ∈ Z ⁻¹' T) : ℓ (q₀+J x).1 ≤ t₁-ε := by
    rw [hq]
    exact hQheight (Z x).1 hx.1
  have he := henergy hZT hZsource hZheight
  dsimp only at he ⊢
  simp only [hq] at he
  rw [Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod S F]
  rw [← (flatProductCoordinates_measurePreserving bS bF e).setLIntegral_comp_preimage_emb
    Z.toHomeomorph.measurableEmbedding]
  convert he using 1
  apply setLIntegral_congr_fun hZT
  intro x hx
  have hvert : inner ℝ (f (WithLp.toLp 2 ((Z x).2,(1:ℝ)))) (bE (Sum.inr ())) = 1 := by
    simp only [bE,flatProductFiberBasis_last,f.inner_map_map]
    simp [WithLp.prod_inner_apply]
  have hpos := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hB hKfib hzero
    (hQB hx.1) bS.toBasis bE (hvert.trans_ne one_ne_zero)
  exact ENNReal.ofReal_mul (by
    unfold tubeAreaDensity
    exact mul_nonneg (Real.rpow_nonneg hpos.1.det_pos.le _) (Real.rpow_nonneg hpos.2.det_pos.le _))

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
/-!
The first missing differential identity in `sections/area.tex`, Stationarity:
the cofactor of an actual Hessian is divergence-free.  The proof below uses
multilinearity of the determinant and symmetry of second derivatives (Piola).
-/

/- The determinant, as a continuous map multilinear in its rows. -/
/- Exchanging two independently replaced rows reverses the determinant. -/
/- Expand one determinant row in the coordinate vectors. -/
/- Symmetric coefficients contract to zero with an alternating pair of rows. -/
/- The algebraic cancellation underlying the Piola identity. -/

/- Rows of the derivative of a list of scalar functions, in fixed directions. -/
/- Differentiate a cofactor by differentiating each of its unfrozen rows. -/
/- Piola's identity in fixed directions; it uses only equality of mixed partials. -/

/- Smoothness through order three suffices for the cofactor cancellation. -/
/- For an invertible Hessian, the manuscript's definition is exactly the adjugate. -/
/- The Hessian cofactor is symmetric under the standing positivity hypothesis. -/
/- Both divergences of the actual coefficient matrix vanish on the original domain. -/

/- The frozen coordinate Hessian has smooth entries at every interior smooth point. -/
/- Determinants of the actual Hessian are smooth, by row multilinearity. -/
/- Polynomial cofactor entries are smooth even before invertibility is used. -/
/- Smoothness of U on its actual open domain, with no extension hypothesis. -/
/- The real determinant weight has its original exponent throughout the proof. -/

/- A fixed-direction derivative, used only as notation for the actual Fréchet derivative. -/
/- The differential part of the double integration by parts. Both zero
cofactor divergences are used; they will be supplied by the proved Piola identity. -/

/- The exact maximal-graph operator is the double divergence of its variational coefficient. -/

/- Integrability uses continuity only on a compact set containing the support. -/
/- Compact support of the test function removes any global regularity requirement
on the coefficient. This is the integration-by-parts form used on the original Ω. -/
/- Two integrations by parts, without an artificial globally smooth coefficient. -/
/- Global smoothness of a fixed-direction derivative. -/
/- The weak double-divergence formula with precisely a compactly supported test. -/

/- Graph-direction stationarity for the source's equation and actual coefficient.
All regularity of `u` is needed only on the original open domain. -/
/- The density of affine area in the original graph coordinates. -/
/- The variation coefficient has exactly the exponent in the manuscript. -/
/- `wU` is not a surrogate for the affine-area coefficient. -/
/- The source's first-variation integral, over its original open domain. -/

/- Jacobi's formula without assuming invertibility of the varied matrix. -/
/- Pointwise first variation of the actual affine-area density. -/

/- Away from topological support the test is locally zero, so no extension
of a smooth coefficient across the original boundary is necessary. -/
/- Commuting fixed-direction differentiation with evaluation of a derivative. -/
/- Symmetry of the second derivative in fixed directions. -/
/- The support-plane height `ν(o-X)` in original graph coordinates. -/
/- Smoothness holds only locally; the eventual zero argument handles tests. -/
/- The derivative of the radial gradient, including its moving vector argument. -/
/- The cancellation `D Z = H(x-o)` with no coordinate or global extension assumption. -/
/- The exact second derivative of the support-plane height. -/

/- The coordinate version used in the trace of the cap test. -/
/- Jacobi's formula in arbitrary fixed directions, for the actual entries. -/
/- Smoothness of the area density on the original domain. -/
/- The exact differential of the affine area coefficient. -/
/- Trace of the identity, in the entry convention used in the manuscript. -/
/- Weighted radial trace, avoiding a logarithm at points outside the domain. -/
/- Expansion in the frozen Euclidean coordinate vectors. -/
/- Linear functionals are recovered exactly by coordinates. -/
/- The radial vector derivative is the sum of its coordinate derivatives. -/
/- A second derivative product rule on the actual open domain. -/
/- Scalar composition by its actual one-dimensional derivative. -/
/- The second chain rule used by a cap test. -/
/- Restriction of an arbitrary ambient affine function to the original graph. -/
/- Coordinate pairing equals the ordinary matrix-vector contraction. -/
/- Symmetry of the covector contraction, with the literal matrix coefficients. -/
/- Exact inverse contraction for a radial vector and a covector. -/
/- The radial support gradient cancels exactly against the inverse Hessian. -/
/- Product trace in coordinates. -/
/- Chain trace in coordinates. -/
/- Positivity fixes the inverse-Hessian symmetry employed in a cap test. -/
/- Pointwise first-variation integrand of the source cap test. -/
/- Cancellation of the affine coefficients in the first variation. -/
/- The actual coordinate functional through the Euclidean-space equivalence. -/
/- A smooth compact test makes a merely locally smooth coefficient globally smooth. -/
/- Integral of a derivative of a smooth compactly supported scalar field. -/
/- Radial integration by parts with a compact test and no global extension of `f`.
This formulation gives integrability as well as the identity. -/
/- Zero-extension of a compactly supported local test is genuinely smooth on the
ambient coordinate space; no extension theorem for the graph is needed. -/
/- Hessians depend only on the germ of a function, also with the total derivative
convention at points outside the domain. -/
/- The actual first-variation density is integrable for a compact local test. -/
/- The cap identity in the original graph coordinates (source `area.tex`,
Lemma Cap identity). The source assumes compact support of all three displayed
scalar compositions; this proof in fact only needs the first support condition.
The measure here is precisely affine area density times Lebesgue measure. -/

/- Weighted arithmetic-geometric mean for the eigenvalues, with the unused
weight placed at 1. This is the determinant-power supporting inequality at I. -/
/- Congruence by the inverse positive square root converts the determinant
ratio and the mixed trace to the same positive semidefinite matrix. -/
/- Concavity in its precise tangent form, for all exponents in [0,1/n]. -/

/- On an open set the Hessian is additive; no extension outside that set is used. -/
/- The actual determinant density obeys its supporting-hyperplane inequality. -/
/- Density differences for a compactly supported perturbation really are
integrable, although each area on an unbounded domain could be infinite. -/
/- Local maximization of graph affine area: the integrated form used in
`bounds.tex:99–126`. It is deduced from the PDE, not assumed as stability. -/
/- The affine pullback uses the continuous map associated with the actual
matrix, so its determinant and nonsingularity have their usual meanings. -/
/- First derivative of composition with an affine base change. -/
/- The Hessian chain rule, retaining the exact order Bᵀ H B. -/
/- Multiplying heights by a scalar multiplies the actual Hessian by it. -/
/- Nonsingular congruence and positive scalar multiplication preserve strict
ellipticity. The condition on B is exactly invertibility, not orthogonality. -/
/- Exact determinant normalization used for rescaled sections. -/
/- The trace contraction is invariant under simultaneous congruence, with the
exact scalar ratio. This is the algebra behind covariance of the affine PDE. -/
/- The classical PDE is equivalent to the inverse-Hessian trace formulation
wherever its coefficients are the actual positive-definite Hessian. -/
/- Change of base variables, positive vertical scaling, and arbitrary affine
height correction. This includes the normalization of sections in rigidity. -/
/- The actual determinant weight transforms by its exact positive constant. -/
/- Hessians are local, including their inner derivative. -/
/- Exact, classical affine-maximal PDE covariance for section normalization.
No transformed PDE is assumed: it follows from the original one by the actual
Hessian and determinant chain rules. -/

/- The conormal for the genuine variation (x+t a(x),u(x)+t beta(x)),
written in its first jets, is (-q(t),1). -/
/- The second form for that conormal. H,B are the Hessians of u,beta;
C k is the Hessian of the kth horizontal displacement. -/

/- The actual first derivative of the horizontal component, in graph coordinates. -/
/- The graph's normal component of an arbitrary parametrized velocity. -/
/- The vertical velocity reconstructed from its normal part and horizontal part. -/
/- Actual affine-area density of the variation, in its exact graph jets. -/

/- The tangential part of the exact parametrized first-variation density is
an ordinary divergence; the remaining part is the genuine graph variation. -/

/- Every compact smooth parametric velocity has a genuinely smooth compact
normal graph component, without extending the original graph smoothly. -/
/- The exact pointwise first variation under every compact smooth parametric
velocity is integrable and has zero integral. The density uses the actual
varying conormal and horizontal Jacobian. -/

/- The augmented tangent frame, with its transverse column last. -/
/- The literal second form with a conormal frozen at the point in question. -/
/- Source (affine-area), using a fixed ambient volume basis. -/
/- Full ambient affine covariance, not restricted to fiber-preserving maps. -/

/- The abstract conormal formula is exactly the literal graph-variation density. -/

/- The literal arbitrary affine image of a parametrized graph variation. -/
/- Stationarity is genuinely preserved by every ambient affine transformation.
The integrand is the derivative of the actual transformed parametric density.
No equation for the affine image is assumed. -/

/- At a critical point the Hessian chain rule has no second derivative of the
coordinate change. Here it is proved for the actual Fréchet derivatives. -/

/- Exact density change of variables; its Jacobian has exponent one. -/

/- Invariance under positive rescaling of the conormal and reciprocal scaling
of the transverse vector. Both are actual multilinear expressions. -/
/- A tangent vector can be added to the transverse column without changing
its affine volume. -/

/- Differentiation over a fixed compact set from smoothness in a neighbourhood
of the zero-parameter slice. The uniform bound is obtained by compactness. -/

/- Actual differentiation of the compact affine-area functional, not just
an integrated pointwise derivative. -/
/- The compact affine-area functional of every arbitrary affine image is
stationary. All derivatives and integrals are the literal geometric density. -/

/- The stationarity functional in any smooth nonsingular injective coordinate
chart. The change of variables uses the literal Lebesgue Jacobian, and positivity
for the full parameter family is derived uniformly from the original Hessian. -/

/- Push a compactly supported smooth local velocity through a genuine smooth
coordinate inverse and extend by zero. Smoothness at the chart boundary is
proved, not an extra assumption on the transported velocity. -/
/- Every compact smooth ambient velocity in a local chart is a genuine
compact smooth graph velocity. This removes the extension requirement from
the coordinate stationarity theorem. -/

/- The literal affine area is independent of both allowed choices of
conormal and transverse vector. All transversality and orientation properties
are explicit; no intrinsic-area object is postulated. -/

/- The ambient conormal/transverse choices in the local chart stationarity
functional may be replaced by any other inward normalized choices. -/

/- Literal affine area is stationary for every compact smooth local ambient
variation, with any continuous inward normalized conormal/transverse choices.
The equation on the original graph, not an ambient stationary axiom, is used. -/

/- The graph projection of a smooth immersed parametrization of a graph
has nonsingular derivative. This is the differential input to the local
chart used in the support-coordinate stationarity calculation. -/

/- Local stationarity on an arbitrary immersed parametrization of the actual
solution graph. The smooth inverse chart is produced by the inverse function
theorem, not included among the hypotheses. -/

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

/- The actual second-jet affine-area density in the base and orthonormal
angular directions; the transverse column is (0,-e). -/

/- Literal Jacobi first variation of the tube density, including empty
angular matrices. This is the integrand needed in source (tube-euler). -/

/- Both matrices in the actual tube area formula are positive definite,
including an empty angular matrix. This is derived from the original graph,
not imposed as an additional curvature assumption. -/
/- Source tube-area, for the literal supremum/Gauss parametrization of the
original affine epigraph under an arbitrary ambient affine isomorphism. -/

/- In a flat normal chart the final normal coordinate is one, and the
transverse column is the fixed negative final basis vector. -/
/- Literal flat-normal-chart area density. No sphere measure change is
required to obtain the local variational equation in these coordinates. -/

/- Positivity of the flat-normal-chart Hessian blocks follows from the actual
strictly convex affine epigraph, not from a surrogate support-function class. -/

/- A flat normal parametrization of the actual affine-epigraph boundary is
smooth and immersed; it lies on the original solution graph. The local graph
inverse is therefore available without a geometric chart hypothesis. -/

/- Literal local affine stationarity in any ambient vector coordinates.
The reference volume basis is transported exactly, not replaced by a
coordinate-free area axiom. -/

/- The literal support conormal is inward relative to the original solution
 graph, even after a general ambient affine change of variables. -/

/- The literal PDE supplies stationarity on every actual flat-normal support
chart. The chart inverse and conormal orientation are derived, not assumed. -/

end AffineBernstein

end

end OAI
