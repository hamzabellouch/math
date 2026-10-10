import Mathlib
import OAI.Analysis.AffineBernstein.ActualBaseMinors
import OAI.Analysis.AffineBernstein.ActualLogMeasure
import OAI.Analysis.AffineBernstein.MassIntegral

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The literal spherical affine area is bounded in terms of the actual weighted
sigma density, by Holder and the actual fiber support height. -/
theorem affineEpigraph_area_le_sigma {n k : ℕ} (hn : 1 ≤ n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Q, ∀ y : E, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) :
    let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    let μ := (volume.restrict Q).prod (volume : Measure E).toSphere
    (∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
      ENNReal.ofReal ((tubeBaseMatrix H (s,v) b).det ^ (1/((n:ℝ)+2)) *
        (tubeAngularDensity H (s,v) bE)^(1-1/((n:ℝ)+2))) ∂volume.toSphere) ≤
    ENNReal.ofReal (M^((n:ℝ)/((n:ℝ)+2))) *
      (∫⁻ q, ENNReal.ofReal (tubeMeasureDensity n H b bE (q.1,q.2) *
        tubeLogMassWeight H (q.1,q.2)) ∂μ)^(2/((n:ℝ)+2)) *
      (∫⁻ q, ENNReal.ofReal (tubeAngularDensity H (q.1,q.2) bE) ∂μ)^(1-2/((n:ℝ)+2)) := by
  let H := fun q : Space k × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let μ := (volume.restrict Q).prod (volume : Measure E).toSphere
  let B := fun q : Space k × Metric.sphere (0:E) 1 => (tubeBaseMatrix H (q.1,q.2) b).det
  let A := fun q : Space k × Metric.sphere (0:E) 1 => tubeAngularDensity H (q.1,q.2) bE
  have hmap : Continuous (fun q : Space k × Metric.sphere (0:E) 1 => (q.1,(q.2:E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have he (e : Metric.sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using e.property
  have he0 (e : Metric.sphere (0:E) 1) : (e:E) ≠ 0 := Metric.ne_of_mem_sphere e.property one_ne_zero
  have hj (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) : ContDiffAt ℝ ∞ H (q.1,q.2) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2)).1
  have hpq (q : Space k × Metric.sphere (0:E) 1) (hq : q.1 ∈ Q) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero (hQD hq) (he0 q.2) b bE
  have haemeas {F : Space k × E → ℝ}
      (hF : ∀ q : Space k × Metric.sphere (0:E) 1, q.1 ∈ Q → ContinuousAt F (q.1,q.2)) :
      AEMeasurable (fun q : Space k × Metric.sphere (0:E) 1 => F (q.1,q.2)) μ := by
    change AEMeasurable _ ((volume.restrict Q).prod (volume : Measure E).toSphere)
    rw [Measure.restrict_prod_eq_prod_univ]
    apply ContinuousOn.aemeasurable _ (hQ.prod MeasurableSet.univ)
    intro q hq
    exact ((hF q hq.1).comp (f := fun z : Space k × Metric.sphere (0:E) 1 => (z.1,(z.2:E)))
      (x := q) hmap.continuousAt).continuousWithinAt
  have hHae := haemeas (F := H) (fun q hq => (hj q hq).continuousAt)
  have hBae : AEMeasurable B μ := haemeas (F := fun z => (tubeBaseMatrix H z b).det) (fun q hq =>
    (((continuousDetRows (ι := Fin k)).contDiff.contDiffAt.comp (q.1,(q.2:E))
      (contDiffAt_tubeBaseMatrix (hj q hq) b))).continuousAt)
  have hAae : AEMeasurable A μ := haemeas (F := fun z => tubeAngularDensity H z bE) (fun q hq =>
    (contDiffAt_tubeAngularDensity (hj q hq) bE).continuousAt)
  have hqa : ∀ᵐ q ∂μ, q.1 ∈ Q := by
    change ∀ᵐ q ∂(volume.restrict Q).prod (volume : Measure E).toSphere, q.1 ∈ Q
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (μ := volume.prod (volume : Measure E).toSphere)
      (hQ.prod MeasurableSet.univ)] with q hq
    exact hq.1
  have hholder := lintegral_tube_area_le_mass hn hHae hBae hAae
    (hqa.mono fun q hq => (hpq q hq).2.2)
    (hqa.mono fun q hq => (hpq q hq).1.det_pos)
    (hqa.mono fun q hq => (hpq q hq).2.1) hM
    (hqa.mono fun q hq => (le_abs_self _).trans
      (homogeneousSupport_abs_le_of_radius (hK q.1 (hQD hq))
      ⟨0,interior_subset (hzero q.1 (hQD hq))⟩ (he q.2) (hbound q.1 hq)))
  have hareaMeas : AEMeasurable (fun q => ENNReal.ofReal
      (B q ^ (1/((n:ℝ)+2)) * A q ^ (1-1/((n:ℝ)+2)))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hBae.pow_const (1/((n:ℝ)+2))).mul (hAae.pow_const (1-1/((n:ℝ)+2))))
  dsimp only
  change (∫⁻ s in Q, ∫⁻ v : Metric.sphere (0:E) 1,
    ENNReal.ofReal (B (s,v) ^ (1/((n:ℝ)+2)) * A (s,v) ^ (1-1/((n:ℝ)+2))) ∂volume.toSphere) ≤ _
  rw [← lintegral_prod _ hareaMeas]
  refine hholder.trans ?_
  apply mul_le_mul_left
  apply mul_le_mul_right
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono_ae
  filter_upwards [hqa] with q hq
  apply ENNReal.ofReal_le_ofReal
  have hw : 1 ≤ tubeLogMassWeight H (q.1,q.2) := by
    change 1 ≤ 1+∑ i : Fin k, _
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      tubeBasePair_nonneg b (hpq q hq).2.2.le (hpq q hq).1 _)
  change tubeMeasureDensity n H b bE (q.1,q.2) ≤ _
  exact le_mul_of_one_le_right (tubeMeasureCoefficient_pos (hpq q hq).2.2
    (hpq q hq).1.det_pos (hpq q hq).2.1).le hw

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

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

/- The exact quadratics used in the positive-cap comparison. -/

/- A genuine compact smooth convex-cap replacement, with no stationarity or
area conclusion assumed. This supplies source bounds.tex:88–110. -/

/- Local weak maximization and a smooth convex replacement give the cap
comparison on its actual open base. -/
/- The graph-coordinate positive cap estimate, with a quantitative uniform
constant. The original PDE, not an area lower bound, is the hypothesis. -/
/- Uniform nonvanishing in uniformly bounded graph caps, exactly the smooth
comparison portion of bounds.tex:88–126. No assumptions on boundary regularity
or uniform Hessian bounds enter. -/

/- A bounded cap quantitatively separates a unit recession direction from
its horizontal hyperplane. This is the ray argument in bounds.tex:45–59. -/
/- The normalized vertical has uniformly bounded norm. -/
/- Compactness of a closed graph sublevel follows from compactness of the
entire epigraph cap, without a boundary regularity hypothesis. -/
/- The ambient ball supplies the graph's base ball at the center's height. -/
/- A cap radius bounds distances to the center in its base. -/

/- A shear does not change height and straightens an upward vector. -/
/- The induced invertible horizontal map of a triangular ambient affine map. -/

/- The manuscript's epigraph; the domain is not silently replaced by all of space. -/
/- The affine image is literally the epigraph of the derived graph; no new
solution or geometric stationary surrogate is assumed. -/

/- Affine area of the actual cap, in the original global graph chart.
The determinant exponent is the one proved for the literal parametric density. -/
/- The true cap integral is identical in the sheared graph coordinates. -/

end AffineBernstein

end

end OAI
