import Mathlib

namespace OAI

/-!
# Polynomial growth and conditional exhaustion

The model is the complex vector space `Fin n → ℂ`. A Kähler metric is specified
by a smooth real Riemannian metric and its torsion-free metric connection, with
the canonical complex structure parallel. Completeness refers to the Riemannian
length distance.

Polynomial radial growth, forward smallness and an inverse-ball inclusion force
an open image containing zero to fill complex space. Constructing the maps and
deriving these bounds from a Kähler metric remain outside this formalization;
the Kähler uniformization theorem is not proved here.
-/

open scoped Manifold ContDiff Bundle
open Set
noncomputable section
namespace KahlerUniformization

/-- Complex Euclidean space of complex dimension `n`. -/
abbrev ComplexSpace (n : ℕ) := Fin n → ℂ
abbrev complexModel (n : ℕ) := 𝓘(ℂ, ComplexSpace n)
abbrev realModel (n : ℕ) := 𝓘(ℝ, ComplexSpace n)

/-- Holomorphic transition functions are smooth over the real numbers. -/
instance underlyingRealManifold {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexSpace n) M]
    [IsManifold (complexModel n) ∞ M] :
    IsManifold (realModel n) ∞ M := by
  have hle : contDiffGroupoid ∞ (complexModel n) ≤
      contDiffGroupoid ∞ (realModel n) := by
    apply groupoid_of_pregroupoid_le
    intro f s hfs
    change ContDiffOn ℝ ∞ _ _
    simpa only [contDiffPregroupoid, complexModel, realModel, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
      preimage_id_eq, range_id, inter_univ] using hfs.restrict_scalars ℝ
  let : HasGroupoid M (contDiffGroupoid ∞ (realModel n)) :=
    hasGroupoid_of_le (G₁ := contDiffGroupoid ∞ (complexModel n)) inferInstance hle
  exact IsManifold.mk' (realModel n) ∞ M

section GeometricDefinitions
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexSpace n) M]
    [IsManifold (complexModel n) ∞ M]

abbrev RealTangent (x : M) := TangentSpace (realModel n) x

/-- The canonical almost complex structure on the underlying real tangent
bundle: multiplication by `i` in holomorphic tangent coordinates. -/
def complexStructure (x : M) (v : RealTangent (n := n) x) : RealTangent (n := n) x :=
  fun i ↦ Complex.I * v i

omit [IsManifold (complexModel n) ∞ M] in
@[simp] lemma complexStructure_sq (x : M) (v : RealTangent (n := n) x) :
    complexStructure (n := n) x (complexStructure (n := n) x v) = -v := by
  funext i
  change Complex.I * (Complex.I * v i) = -(v i)
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- A positive definite smooth real inner product on each tangent space. -/
abbrev SmoothMetric := Bundle.ContMDiffRiemannianMetric (realModel n) ∞
    (ComplexSpace n) (RealTangent (n := n) : M → Type _)

abbrev Connection := CovariantDerivative (realModel n) (ComplexSpace n)
    (RealTangent (n := n) : M → Type _)

/-- A smooth Kähler metric, in the torsion-free metric-connection formulation.
No topology, flow, coordinate-map, or uniformization conclusions occur among
these fields. -/
structure SmoothKahlerMetric where
  metric : SmoothMetric (n := n) (M := M)
  connection : Connection (n := n) (M := M)
  smooth_connection : CovariantDerivative.ContMDiffCovariantDerivative connection ∞
  torsion_free : connection.torsion = 0
  hermitian : ∀ (x : M) (v w : RealTangent (n := n) x),
    metric.inner x (complexStructure (n := n) x v) (complexStructure (n := n) x w) =
      metric.inner x v w
  metric_compatible : ∀ (σ τ : (x : M) → RealTangent (n := n) x)
    (x : M) (v : RealTangent (n := n) x),
    MDifferentiableAt (realModel n) (realModel n).tangent
      (fun y ↦ (⟨y, σ y⟩ : TangentBundle (realModel n) M)) x →
    MDifferentiableAt (realModel n) (realModel n).tangent
      (fun y ↦ (⟨y, τ y⟩ : TangentBundle (realModel n) M)) x →
    mfderiv (realModel n) 𝓘(ℝ) (fun y ↦ metric.inner y (σ y) (τ y)) x v =
      metric.inner x (connection σ x v) (τ x) +
        metric.inner x (σ x) (connection τ x v)
  parallel_complexStructure : ∀ (σ : (x : M) → RealTangent (n := n) x)
    (x : M) (v : RealTangent (n := n) x),
    MDifferentiableAt (realModel n) (realModel n).tangent
      (fun y ↦ (⟨y, σ y⟩ : TangentBundle (realModel n) M)) x →
    connection (fun y ↦ complexStructure (n := n) y (σ y)) x v =
      complexStructure (n := n) x (connection σ x v)

namespace SmoothKahlerMetric
variable (g : SmoothKahlerMetric (n := n) (M := M))

/-- The curvature operator
`R(u,v)w = ∇_U ∇_V W - ∇_V ∇_U W - ∇_[U,V] W`, using local smooth
extensions at `x`. This is the convention where `g(R(u,v)v,u)` is the
sectional-curvature numerator. -/
def curvature (x : M) (u v w : RealTangent (n := n) x) : RealTangent (n := n) x :=
  let U := FiberBundle.extend (ComplexSpace n) u
  let V := FiberBundle.extend (ComplexSpace n) v
  let W := FiberBundle.extend (ComplexSpace n) w
  g.connection (fun y ↦ g.connection W y (V y)) x u -
    g.connection (fun y ↦ g.connection W y (U y)) x v -
    g.connection W x (VectorField.mlieBracket (realModel n) U V x)

/-- The real Riemannian curvature with all indices lowered using `g`. -/
def rm (x : M) (u v w z : RealTangent (n := n) x) : ℝ :=
  g.metric.inner x (g.curvature x u v w) z

/-- Pointwise strict positivity, for every pair of real **metric-unit** vectors.
There is no uniform lower bound or upper curvature bound in this definition. -/
def PositiveHolomorphicBisectionalCurvature : Prop :=
  ∀ (x : M) (u v : RealTangent (n := n) x),
    g.metric.inner x u u = 1 → g.metric.inner x v v = 1 →
    0 < g.rm x u v v u +
      g.rm x u (complexStructure (n := n) x v) (complexStructure (n := n) x v) u

/-- Completeness of the Riemannian length distance, not that of a chart norm. -/
def IsComplete [T2Space M] : Prop :=
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (realModel n)
  letI : Bundle.RiemannianBundle (RealTangent (n := n) : M → Type _) :=
    ⟨g.metric.toContinuousRiemannianMetric.toRiemannianMetric⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (realModel n) M
  CompleteSpace M

/-- The fundamental form of a Hermitian metric is skew-symmetric. -/
lemma inner_complexStructure_swap (x : M) (u v : RealTangent (n := n) x) :
    g.metric.inner x (complexStructure (n := n) x u) v =
      -g.metric.inner x u (complexStructure (n := n) x v) := by
  have h := g.hermitian x u (complexStructure (n := n) x v)
  rw [complexStructure_sq] at h
  simpa only [map_neg, neg_neg] using congrArg Neg.neg h

@[simp] lemma curvature_self (x : M) (u w : RealTangent (n := n) x) :
    g.curvature x u u w = 0 := by
  simp [curvature]

@[simp] lemma rm_self (x : M) (u w z : RealTangent (n := n) x) :
    g.rm x u u w z = 0 := by
  simp [rm]

/-- Strict bisectional positivity in particular implies positive holomorphic
sectional curvature with the chosen curvature sign convention. -/
lemma holomorphicSectional_pos
    (h : g.PositiveHolomorphicBisectionalCurvature)
    (x : M) (u : RealTangent (n := n) x) (hu : g.metric.inner x u u = 1) :
    0 < g.rm x u (complexStructure (n := n) x u) (complexStructure (n := n) x u) u := by
  simpa only [rm_self, zero_add] using h x u u hu hu

end SmoothKahlerMetric
end GeometricDefinitions

/-! ## Polynomial radial growth -/

open Polynomial Metric Filter
open scoped Polynomial Topology

/-- Exterior maximum-modulus bound for a complex polynomial. -/
theorem polynomial_norm_bound_exterior (p : ℂ[X]) (m : ℕ) (hm : p.natDegree ≤ m)
    (C : ℝ) (hC : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖p.eval z‖ ≤ C)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖p.eval z‖ ≤ ‖z‖ ^ m * C := by
  have reflect_id (w : ℂ) (hw : w ≠ 0) :
      (p.reflect m).eval w⁻¹ * w ^ m = p.eval w := by
    let : Invertible w := invertibleOfNonzero hw
    simpa only [invOf_eq_inv, eval₂_id] using
      Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) w m p hm
  have hboundary : ∀ w ∈ frontier (ball (0 : ℂ) 1), ‖(p.reflect m).eval w‖ ≤ C := by
    intro w hw
    have hwnorm : ‖w‖ = 1 := by
      simpa only [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere, dist_zero_right] using hw
    have hwne : w ≠ 0 := by
      intro hwzero
      simp only [hwzero, norm_zero, zero_ne_one] at hwnorm
    have hid := congrArg norm (reflect_id w⁻¹ (inv_ne_zero hwne))
    simp only [inv_inv, norm_mul, norm_pow, norm_inv, hwnorm, inv_one, one_pow, mul_one] at hid
    rw [hid]
    exact hC _ (by rw [norm_inv, hwnorm, inv_one])
  have hreflect : ‖(p.reflect m).eval z⁻¹‖ ≤ C := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (p.reflect m).differentiable.diffContOnCl hboundary
    rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right, norm_inv]
    exact inv_le_one_of_one_le₀ hz
  have hzne : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hz)
  calc
    ‖p.eval z‖ = ‖(p.reflect m).eval z⁻¹‖ * ‖z‖ ^ m := by
      rw [← reflect_id z hzne, norm_mul, norm_pow]
    _ ≤ C * ‖z‖ ^ m := mul_le_mul_of_nonneg_right hreflect (pow_nonneg (norm_nonneg z) m)
    _ = ‖z‖ ^ m * C := mul_comm _ _

/-- Restriction of a multivariable polynomial to a complex line through zero. -/
def polynomialOnLine {ι : Type*} (p : MvPolynomial ι ℂ) (v : ι → ℂ) : ℂ[X] :=
  p.eval₂ Polynomial.C (fun i ↦ Polynomial.C (v i) * Polynomial.X)

lemma polynomialOnLine_eval {ι : Type*} (p : MvPolynomial ι ℂ) (v : ι → ℂ) (t : ℂ) :
    (polynomialOnLine p v).eval t = MvPolynomial.eval (t • v) p := by
  unfold polynomialOnLine
  change (Polynomial.evalRingHom t) _ = _
  rw [MvPolynomial.hom_eval₂]
  have hring : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext c
    simp
  simp only [hring, Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, MvPolynomial.eval₂_id]
  congr 2
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

lemma polynomialOnLine_natDegree_le {ι : Type*} (p : MvPolynomial ι ℂ) (v : ι → ℂ) :
    (polynomialOnLine p v).natDegree ≤ p.totalDegree := by
  classical
  unfold polynomialOnLine
  conv_lhs => rw [p.as_sum]
  rw [MvPolynomial.eval₂_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.eval₂_monomial]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans _ (MvPolynomial.le_totalDegree hd)
  apply Finset.sum_le_sum
  intro i hi
  apply Polynomial.natDegree_pow_le.trans
  have hlinear : (Polynomial.C (v i) * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  simpa only [mul_one] using Nat.mul_le_mul_left (d i) hlinear

/-- Radial growth bound for a multivariable complex polynomial. -/
theorem mvPolynomial_radial_growth {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℂ) (m : ℕ) (hm : p.totalDegree ≤ m)
    {r R C : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hC : ∀ z : ι → ℂ, ‖z‖ ≤ r → ‖MvPolynomial.eval z p‖ ≤ C)
    (z : ι → ℂ) (hz : ‖z‖ ≤ R) :
    ‖MvPolynomial.eval z p‖ ≤ (R / r) ^ m * C := by
  let v : ι → ℂ := (↑(r / R) : ℂ) • z
  let t : ℂ := ↑(R / r)
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hratio : 1 ≤ R / r := (one_le_div hr).mpr hrR
  have htnorm : ‖t‖ = R / r := Complex.norm_of_nonneg (div_nonneg hR.le hr.le)
  have hv : ‖v‖ ≤ r := by
    calc
      ‖v‖ = (r / R) * ‖z‖ := by
        rw [norm_smul, Complex.norm_of_nonneg (div_nonneg hr.le hR.le)]
      _ ≤ (r / R) * R := mul_le_mul_of_nonneg_left hz (div_nonneg hr.le hR.le)
      _ = r := div_mul_cancel₀ _ (ne_of_gt hR)
  have hunit : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖(polynomialOnLine p v).eval w‖ ≤ C := by
    intro w hw
    rw [polynomialOnLine_eval]
    apply hC
    calc
      ‖w • v‖ = ‖w‖ * ‖v‖ := norm_smul w v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg v)
      _ ≤ r := by simpa only [one_mul] using hv
  have htv : t • v = z := by
    dsimp [v, t]
    rw [smul_smul]
    have hcancel : R / r * (r / R) = 1 := by field_simp
    rw [hcancel, one_smul]
  have h := polynomial_norm_bound_exterior (polynomialOnLine p v) m
    ((polynomialOnLine_natDegree_le _ _).trans hm) C hunit t (by rwa [htnorm])
  rwa [polynomialOnLine_eval, htv, htnorm] at h

/-- The polynomial growth estimate for vector-valued multivariable polynomials.
Here the finite-dimensional norm is the standard supremum norm on coordinate tuples. -/
theorem polynomial_map_radial_growth {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : κ → MvPolynomial ι ℂ) (m : ℕ) (hm : ∀ i, (P i).totalDegree ≤ m)
    {r R C : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ z : ι → ℂ, ‖z‖ ≤ r → ‖fun i ↦ MvPolynomial.eval z (P i)‖ ≤ C)
    (z : ι → ℂ) (hz : ‖z‖ ≤ R) :
    ‖fun i ↦ MvPolynomial.eval z (P i)‖ ≤ (R / r) ^ m * C := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (pow_nonneg (div_nonneg (hr.trans_le hrR).le hr.le) _) hC)).mpr
  intro i
  apply mvPolynomial_radial_growth (P i) m (hm i) hr hrR _ z hz
  intro w hw
  exact (norm_le_pi_norm (fun j ↦ MvPolynomial.eval w (P j)) i).trans (hbound w hw)

/-! ## Conditional image exhaustion -/

open Filter
open scoped Topology

/-- The image-exhaustion step: exponentially small forward maps, an inverse-ball
inclusion, and radial growth bounds along an unbounded subsequence force an open
image containing the origin to be the whole space. The hypotheses on `G` are
analytic inputs, not consequences of curvature proved in this file. -/
theorem image_eq_univ_of_exponential_bounds
    {E : Type*} [NormedAddCommGroup E]
    {Ω : Set E} (hΩ : IsOpen Ω) (hzero : (0 : E) ∈ Ω)
    (a b D : ℝ) (hD : 0 ≤ D) (hab : b < a)
    (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) (G : ℕ → E → E)
    (forward : ∀ r : ℝ, 0 < r → (∀ z : E, ‖z‖ ≤ r → z ∈ Ω) →
      ∀ᶠ k in atTop, ∀ z : E, ‖z‖ ≤ r → ‖G k z‖ ≤ Real.exp (-a * s k))
    (growth : ∃ᶠ k in atTop, ∀ (r R C : ℝ), 0 < r → r ≤ R → 0 ≤ C →
      (∀ z : E, ‖z‖ ≤ r → ‖G k z‖ ≤ C) →
      ∀ z : E, ‖z‖ ≤ R →
        ‖G k z‖ ≤ Real.exp (D * s k * Real.log (R / r)) * C)
    (inverse_ball : ∀ᶠ k in atTop, ∀ z : E,
      ‖G k z‖ < Real.exp (-b * s k) → z ∈ Ω) :
    Ω = univ := by
  let ε : ℝ := (a - b) / (D + 1)
  have hden : 0 < D + 1 := by linarith
  have hε : 0 < ε := div_pos (sub_pos.mpr hab) hden
  let q : ℝ := Real.exp ε
  have hq : 1 < q := Real.one_lt_exp_iff.mpr hε
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hmargin : D * Real.log q < a - b := by
    have heq : (D + 1) * ε = a - b := mul_div_cancel₀ _ (ne_of_gt hden)
    have hlt : D * ε < (D + 1) * ε :=
      mul_lt_mul_of_pos_right (lt_add_one D) hε
    simpa only [q, Real.log_exp, heq] using hlt
  have expand : ∀ r : ℝ, 0 < r →
      (∀ z : E, ‖z‖ ≤ r → z ∈ Ω) → ∀ z : E, ‖z‖ ≤ q * r → z ∈ Ω := by
    intro r hr hball
    obtain ⟨k, hkgrowth, hkpos, hkforward, hkinverse⟩ :=
      (growth.and_eventually ((hs.eventually_gt_atTop 0).and
        ((forward r hr hball).and inverse_ball))).exists
    intro z hz
    apply hkinverse z
    have hbound := hkgrowth r (q * r) (Real.exp (-a * s k)) hr
      (by nlinarith) (le_of_lt (Real.exp_pos _)) hkforward z hz
    calc
      ‖G k z‖ ≤ Real.exp (D * s k * Real.log ((q * r) / r)) *
          Real.exp (-a * s k) := hbound
      _ = Real.exp ((D * Real.log q - a) * s k) := by
        rw [mul_div_cancel_right₀ q (ne_of_gt hr), ← Real.exp_add]
        congr 1
        ring
      _ < Real.exp (-b * s k) := by
        apply Real.exp_lt_exp.mpr
        exact mul_lt_mul_of_pos_right (by linarith) hkpos
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.mp hΩ 0 hzero
  have hstart : ∀ z : E, ‖z‖ ≤ δ / 2 → z ∈ Ω := by
    intro z hz
    apply hδball
    simpa only [Metric.mem_ball, dist_zero_right] using (lt_of_le_of_lt hz (by linarith : δ / 2 < δ))
  have hball : ∀ j : ℕ, ∀ z : E, ‖z‖ ≤ (δ / 2) * q ^ j → z ∈ Ω := by
    intro j
    induction j with
    | zero => simpa only [pow_zero, mul_one] using hstart
    | succ j ih =>
      have hrad : 0 < (δ / 2) * q ^ j := mul_pos (by linarith) (pow_pos hqpos j)
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        expand ((δ / 2) * q ^ j) hrad ih
  apply Set.eq_univ_of_forall
  intro z
  have ht : Tendsto (fun j : ℕ ↦ (δ / 2) * q ^ j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hq).const_mul_atTop (by linarith)
  obtain ⟨j, hj⟩ := (ht.eventually_gt_atTop ‖z‖).exists
  exact hball j z hj.le

/-- Evaluation of a vector polynomial on complex affine space. -/
def evalPolynomialMap {n : ℕ} (P : Fin n → MvPolynomial (Fin n) ℂ)
    (z : Fin n → ℂ) : Fin n → ℂ := fun i ↦ MvPolynomial.eval z (P i)

/-- The surjectivity endgame with actual polynomial maps rather than an
assumed growth estimate. The forward degree bound is required only along
an unbounded subsequence, expressed by `Filter.Frequently`. In particular no
degree bound for inverse maps is required. Construction of these maps and
estimates from a Kähler metric is not part of this lemma. -/
theorem image_eq_univ_of_polynomial_bounds
    {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) (hzero : (0 : Fin n → ℂ) ∈ Ω)
    (a b D : ℝ) (hD : 0 ≤ D) (hab : b < a)
    (s : ℕ → ℝ) (hs : Tendsto s atTop atTop)
    (P : ℕ → Fin n → MvPolynomial (Fin n) ℂ)
    (m : ℕ → ℕ) (hdegree : ∀ k i, (P k i).totalDegree ≤ m k)
    (hcost : ∃ᶠ k in atTop, (m k : ℝ) ≤ D * s k)
    (forward : ∀ r : ℝ, 0 < r → (∀ z : Fin n → ℂ, ‖z‖ ≤ r → z ∈ Ω) →
      ∀ᶠ k in atTop, ∀ z : Fin n → ℂ, ‖z‖ ≤ r →
        ‖evalPolynomialMap (P k) z‖ ≤ Real.exp (-a * s k))
    (inverse_ball : ∀ᶠ k in atTop, ∀ z : Fin n → ℂ,
      ‖evalPolynomialMap (P k) z‖ < Real.exp (-b * s k) → z ∈ Ω) :
    Ω = univ := by
  apply image_eq_univ_of_exponential_bounds hΩ hzero a b D hD hab s hs
    (fun k ↦ evalPolynomialMap (P k)) forward _ inverse_ball
  apply hcost.mono
  intro k hk r R C hr hrR hC hbound z hz
  have hratio : 1 ≤ R / r := (one_le_div hr).mpr hrR
  have hratio_pos : 0 < R / r := zero_lt_one.trans_le hratio
  calc
    ‖evalPolynomialMap (P k) z‖ ≤ (R / r) ^ m k * C :=
      polynomial_map_radial_growth (P k) (m k) (hdegree k) hr hrR hC hbound z hz
    _ = Real.exp ((m k : ℝ) * Real.log (R / r)) * C := by
      rw [Real.exp_nat_mul, Real.exp_log hratio_pos]
    _ ≤ Real.exp (D * s k * Real.log (R / r)) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hk (Real.log_nonneg hratio)

end KahlerUniformization

end

end OAI
