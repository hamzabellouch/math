import OAI.Geometry.ProjectionBodies.Model

namespace OAI

universe uι

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise

namespace PettyProjection.Spherical

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := sphere (0 : Space n) 1

def surface (n : ℕ) : Measure (Sphere n) :=
  (volume : Measure (Space n)).toSphere

def sigma (n : ℕ) : Measure (Sphere n) :=
  (surface n univ)⁻¹ • surface n

instance surface_finite (n : ℕ) : IsFiniteMeasure (surface n) := by
  unfold surface
  infer_instance

lemma surface_ne_zero (n : ℕ) [NeZero n] : surface n ≠ 0 := by
  exact Measure.toSphere_ne_zero _

instance sigma_probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (sigma n) := by
  constructor
  rw [sigma, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (Measure.measure_univ_ne_zero.mpr (surface_ne_zero n)) (measure_ne_top _ _)

instance surface_open_pos (n : ℕ) : (surface n).IsOpenPosMeasure := by
  unfold surface
  infer_instance

instance sigma_open_pos (n : ℕ) : (sigma n).IsOpenPosMeasure := by
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

/-- Spherical means in the probability normalization. -/
def mean {n : ℕ} (f : Sphere n → ℝ) : ℝ := ∫ u, f u ∂sigma n

lemma mean_const (n : ℕ) [NeZero n] (c : ℝ) : mean (fun _ : Sphere n => c) = c := by
  simp [mean]

instance sphere_compact (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Space n) 1)

lemma norm_coe {n : ℕ} (u : Sphere n) : ‖(u : Space n)‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using u.property

/-- Continuous functions are put into the actual spherical L² space. -/
abbrev H (n : ℕ) := Lp ℝ 2 (sigma n)

def toH (n : ℕ) [NeZero n] : C(Sphere n, ℝ) →L[ℝ] H n :=
  ContinuousMap.toLp 2 (sigma n) ℝ

/-- Restrictions of ambient coordinate quadratics. Their span contains the
constants on the unit sphere and all degree-two spherical harmonics. -/
def coordinateProduct (n : ℕ) (i j : Fin n) : C(Sphere n, ℝ) where
  toFun u := (u : Space n) i * (u : Space n) j
  continuous_toFun := by fun_prop

def lowSpace (n : ℕ) [NeZero n] : Submodule ℝ (H n) :=
  Submodule.span ℝ (Set.range fun ij : Fin n × Fin n =>
    toH n (coordinateProduct n ij.1 ij.2))

instance lowSpace_finite (n : ℕ) [NeZero n] : FiniteDimensional ℝ (lowSpace n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The complement of the constants and the quadratics. For even input this
is exactly the even tail of degree at least four. -/
def Q (n : ℕ) [NeZero n] : H n →L[ℝ] H n :=
  (lowSpace n)ᗮ.starProjection

lemma sum_coordinateProduct (n : ℕ) :
    ∑ i : Fin n, coordinateProduct n i i = ContinuousMap.const (Sphere n) 1 := by
  ext u
  have h := EuclideanSpace.real_norm_sq_eq (u : Space n)
  rw [norm_coe, one_pow] at h
  simpa [coordinateProduct, sq] using h.symm

lemma constant_mem_lowSpace (n : ℕ) [NeZero n] (c : ℝ) :
    toH n (ContinuousMap.const (Sphere n) c) ∈ lowSpace n := by
  have h1 : toH n (ContinuousMap.const (Sphere n) 1) ∈ lowSpace n := by
    rw [← sum_coordinateProduct, map_sum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.subset_span ⟨(i, i), rfl⟩
  have hf : ContinuousMap.const (Sphere n) c =
      c • ContinuousMap.const (Sphere n) (1 : ℝ) := by ext; simp
  rw [hf, map_smul]
  exact (lowSpace n).smul_mem c h1

lemma Q_eq_sub (n : ℕ) [NeZero n] (f : H n) :
    Q n f = f - (lowSpace n).starProjection f :=
  Submodule.starProjection_orthogonal_val f

lemma Q_constant (n : ℕ) [NeZero n] (c : ℝ) :
    Q n (toH n (ContinuousMap.const (Sphere n) c)) = 0 := by
  rw [Q_eq_sub, Submodule.starProjection_eq_self_iff.mpr (constant_mem_lowSpace n c),
    sub_self]

lemma norm_Q_le (n : ℕ) [NeZero n] (f : H n) : ‖Q n f‖ ≤ ‖f‖ :=
  (lowSpace n)ᗮ.norm_starProjection_apply_le f

lemma inner_toH (n : ℕ) [NeZero n] (f g : C(Sphere n, ℝ)) :
    ⟪toH n f, toH n g⟫ = mean (fun u => f u * g u) := by
  simpa [toH, mean, mul_comm] using ContinuousMap.inner_toLp (sigma n) f g

lemma norm_toH_sq (n : ℕ) [NeZero n] (f : C(Sphere n, ℝ)) :
    ‖toH n f‖ ^ 2 = mean (fun u => (f u) ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, inner_toH]
  simp [sq]

lemma norm_Q_le_centered (n : ℕ) [NeZero n] (f : C(Sphere n, ℝ)) (c : ℝ) :
    ‖Q n (toH n f)‖ ^ 2 ≤ mean (fun u => (f u - c) ^ 2) := by
  have h := norm_Q_le n (toH n (f - ContinuousMap.const (Sphere n) c))
  have hQ : Q n (toH n (f - ContinuousMap.const (Sphere n) c)) = Q n (toH n f) := by
    simp only [map_sub, Q_constant, sub_zero]
  rw [hQ] at h
  have hh := (sq_le_sq₀ (norm_nonneg (Q n (toH n f)))
    (norm_nonneg (toH n (f - ContinuousMap.const (Sphere n) c)))).mpr h
  simpa only [norm_toH_sq, ContinuousMap.sub_apply, ContinuousMap.const_apply] using hh

/-- Orthogonal changes of variables on the actual unit sphere. -/
def sphereMap {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) : Sphere n ≃ₜ Sphere n where
  toFun u := ⟨U u, by simpa only [mem_sphere, dist_zero_right, U.norm_map] using norm_coe u⟩
  invFun u := ⟨U.symm u, by simpa only [mem_sphere, dist_zero_right, U.symm.norm_map] using norm_coe u⟩
  left_inv u := by ext; simp
  right_inv u := by ext; simp
  continuous_toFun := (U.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk _

lemma cone_preimage {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) (s : Set (Sphere n)) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereMap U ⁻¹' s)) =
      U ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨r, hr, U u, ⟨sphereMap U u, hu, rfl⟩, by simp⟩
  · rintro ⟨r, hr, y, ⟨v, hv, rfl⟩, heq⟩
    refine ⟨r, hr, U.symm v, ⟨(sphereMap U).symm v, ?_, rfl⟩, ?_⟩
    · simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hv
    · have hh := congrArg U.symm heq
      simpa only [map_smul, U.symm_apply_apply] using hh

lemma surface_preserving {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) :
    MeasurePreserving (sphereMap U) (surface n) (surface n) := by
  refine ⟨(sphereMap U).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereMap U).measurable hs, surface,
    Measure.toSphere_apply' _ ((sphereMap U).measurable hs),
    Measure.toSphere_apply' _ hs, cone_preimage]
  rw [U.measurePreserving.measure_preimage_emb U.toHomeomorph.measurableEmbedding]

lemma sigma_preserving {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) :
    MeasurePreserving (sphereMap U) (sigma n) (sigma n) :=
  (surface_preserving U).smul_measure _

lemma mean_rotation {n : ℕ} (U : Space n ≃ₗᵢ[ℝ] Space n) (f : Sphere n → ℝ) :
    mean (fun u => f (sphereMap U u)) = mean f :=
  (sigma_preserving U).integral_comp (sphereMap U).measurableEmbedding f

local instance (n : ℕ) : CompleteSpace (Space n →L[ℝ] Space n) :=
  FiniteDimensional.complete ℝ _

local instance (n : ℕ) : NormedAlgebra ℚ (Space n →L[ℝ] Space n) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- Exponentiating an actual skew-adjoint operator produces rotations. -/
def rotation {n : ℕ} (T : Space n →L[ℝ] Space n) (hT : star T = -T) (t : ℝ) :
    Space n ≃ₗᵢ[ℝ] Space n :=
  Unitary.linearIsometryEquiv ⟨NormedSpace.exp (t • T),
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
      rw [skewAdjoint.mem_iff, star_smul, star_trivial, hT, smul_neg])⟩

lemma rotation_apply {n : ℕ} (T : Space n →L[ℝ] Space n) (hT : star T = -T)
    (t : ℝ) (x : Space n) : rotation T hT t x = NormedSpace.exp (t • T) x := rfl

lemma rotation_zero {n : ℕ} (T : Space n →L[ℝ] Space n) (hT : star T = -T)
    (x : Space n) : rotation T hT 0 x = x := by
  rw [rotation_apply]
  have hz : (0 : ℝ) • T = 0 := zero_smul ℝ T
  rw [hz, NormedSpace.exp_zero]
  rfl

lemma hasDerivAt_rotation {n : ℕ} (T : Space n →L[ℝ] Space n) (hT : star T = -T)
    (t : ℝ) (x : Space n) :
    HasDerivAt (fun s => rotation T hT s x) (T (rotation T hT t x)) t := by
  simpa only [mul_apply_eq_comp, map_zero, add_zero, rotation_apply] using
    (hasDerivAt_exp_smul_const' T t).clm_apply (hasDerivAt_const t x)

lemma continuous_integrable {n : ℕ} [NeZero n] {f : Sphere n → ℝ}
    (hf : Continuous f) : Integrable f (sigma n) := by
  simpa only [integrableOn_univ] using
    hf.continuousOn.integrableOn_compact (μ := sigma n) isCompact_univ

/-- Infinitesimal rotation invariance, with differentiation justified using
uniform derivative bounds on the compact sphere. This supplies spherical
integration by parts without postulating it as an interface. -/
lemma mean_fderiv_skew {n : ℕ} [NeZero n] (T : Space n →L[ℝ] Space n)
    (hT : star T = -T) (f : Space n → ℝ) (hf : ContDiff ℝ 1 f) :
    mean (fun u : Sphere n => fderiv ℝ f u (T u)) = 0 := by
  let df : C(Sphere n, Space n →L[ℝ] ℝ) :=
    ⟨fun u => fderiv ℝ f u, (hf.continuous_fderiv (by norm_num)).comp continuous_subtype_val⟩
  let F : ℝ → Sphere n → ℝ := fun t u => f (rotation T hT t u)
  let F' : ℝ → Sphere n → ℝ :=
    fun t u => fderiv ℝ f (rotation T hT t u) (T (rotation T hT t u))
  have hFc (t : ℝ) : Continuous (F t) :=
    hf.continuous.comp ((rotation T hT t).continuous.comp continuous_subtype_val)
  have hF'c (t : ℝ) : Continuous (F' t) := by
    exact ((hf.continuous_fderiv (by norm_num)).comp
      ((rotation T hT t).continuous.comp continuous_subtype_val)).clm_apply
      (T.continuous.comp ((rotation T hT t).continuous.comp continuous_subtype_val))
  have hbound (t : ℝ) (u : Sphere n) : ‖F' t u‖ ≤ ‖df‖ * ‖T‖ := by
    let v : Sphere n := sphereMap (rotation T hT t) u
    calc
      ‖F' t u‖ ≤ ‖fderiv ℝ f v‖ * ‖T v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖df‖ * (‖T‖ * ‖(v : Space n)‖) :=
        mul_le_mul (ContinuousMap.norm_coe_le_norm df v)
          (T.le_opNorm v) (norm_nonneg _) (norm_nonneg df)
      _ = ‖df‖ * ‖T‖ := by rw [norm_coe, mul_one]
  have hderiv (t : ℝ) (u : Sphere n) : HasDerivAt (fun s => F s u) (F' t u) t := by
    exact (hf.differentiable (by norm_num) (rotation T hT t u)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_rotation T hT t u)
  have hI := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sigma n) (x₀ := (0 : ℝ)) (s := univ) (F := F) (F' := F')
    (bound := fun _ => ‖df‖ * ‖T‖) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    (continuous_integrable (hFc 0)) (hF'c 0).aestronglyMeasurable
    (ae_of_all _ fun u t _ => hbound t u) (integrable_const _)
    (ae_of_all _ fun u t _ => hderiv t u)
  have hconst : (fun t => ∫ u, F t u ∂sigma n) = fun _ : ℝ => mean (fun u : Sphere n => f u) := by
    funext t
    exact mean_rotation (rotation T hT t) (fun u : Sphere n => f u)
  rw [hconst] at hI
  have hz := hI.2.unique (hasDerivAt_const (0 : ℝ) (mean (fun u : Sphere n => f u)))
  simpa only [F', rotation_zero, mean] using hz

/-- Derivative along an infinitesimal linear rotation. -/
def rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n) (f : Space n → ℝ) : Space n → ℝ :=
  fun x => fderiv ℝ f x (T x)

lemma continuous_rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (rotDeriv T f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply T.continuous

lemma contDiff_rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (rotDeriv T f) :=
  (hf.fderiv_right (by norm_num)).clm_apply T.contDiff

lemma rotDeriv_mul {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f g : Space n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Space n) :
    rotDeriv T (fun y => f y * g y) x =
      f x * rotDeriv T g x + g x * rotDeriv T f x := by
  simp only [rotDeriv, fderiv_fun_mul (hf x) (hg x), add_apply,
    smul_apply, smul_eq_mul]

/-- Genuine spherical integration by parts for each rotation generator. -/
lemma mean_rotDeriv_mul {n : ℕ} [NeZero n] (T : Space n →L[ℝ] Space n)
    (hT : star T = -T) {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    mean (fun u : Sphere n => f u * rotDeriv T g u) =
      - mean (fun u : Sphere n => g u * rotDeriv T f u) := by
  have h := mean_fderiv_skew T hT (fun x => f x * g x) (hf.mul hg)
  change mean (fun u : Sphere n => rotDeriv T (fun x => f x * g x) u) = 0 at h
  simp_rw [rotDeriv_mul T (hf.differentiable (by norm_num))
    (hg.differentiable (by norm_num))] at h
  have hi₁ := continuous_integrable
    ((hf.continuous.comp continuous_subtype_val).mul
      ((continuous_rotDeriv T hg).comp continuous_subtype_val))
  have hi₂ := continuous_integrable
    ((hg.continuous.comp continuous_subtype_val).mul
      ((continuous_rotDeriv T hf).comp continuous_subtype_val))
  change Integrable (fun u : Sphere n => f u * rotDeriv T g u) (sigma n) at hi₁
  change Integrable (fun u : Sphere n => g u * rotDeriv T f u) (sigma n) at hi₂
  rw [mean, integral_add hi₁ hi₂] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The standard skew generator in the i,j plane. -/
def generator (n : ℕ) (i j : Fin n) : Space n →L[ℝ] Space n :=
  InnerProductSpace.rankOne ℝ (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) -
    InnerProductSpace.rankOne ℝ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

lemma generator_skew (n : ℕ) (i j : Fin n) :
    star (generator n i j) = -generator n i j := by
  simp only [generator, ContinuousLinearMap.star_eq_adjoint, map_sub,
    InnerProductSpace.adjoint_rankOne, neg_sub]

lemma generator_apply {n : ℕ} (i j : Fin n) (x : Space n) :
    generator n i j x = x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1 := by
  simp [generator, EuclideanSpace.inner_single_left]

lemma generator_apply_coord {n : ℕ} (i j a : Fin n) (x : Space n) :
    (generator n i j x) a = x i * (if j = a then 1 else 0) -
      x j * (if i = a then 1 else 0) := by
  simp [generator_apply, PiLp.single_apply, eq_comm]

lemma generator_self {n : ℕ} (i : Fin n) : generator n i i = 0 := by
  simp [generator]

lemma generator_swap {n : ℕ} (i j : Fin n) : generator n j i = -generator n i j := by
  simp [generator, neg_sub]

/-- The Dirichlet form, expressed without local coordinates by rotations. -/
def energy {n : ℕ} (f g : Space n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
    mean (fun u : Sphere n => rotDeriv (generator n i j) f u *
      rotDeriv (generator n i j) g u)

/-- The spherical Laplacian expressed by its rotation generators. -/
def casimir {n : ℕ} (f : Space n → ℝ) : Space n → ℝ := fun x =>
  (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
    rotDeriv (generator n i j) (rotDeriv (generator n i j) f) x

lemma energy_symm {n : ℕ} (f g : Space n → ℝ) : energy f g = energy g f := by
  simp only [energy, mul_comm]

lemma energy_nonneg {n : ℕ} (f : Space n → ℝ) : 0 ≤ energy f f := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact integral_nonneg fun _ => mul_self_nonneg _

lemma mean_sum {n : ℕ} [NeZero n] {ι : Type uι} (s : Finset ι)
    {f : ι → Sphere n → ℝ} (hf : ∀ i ∈ s, Continuous (f i)) :
    mean (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, mean (f i) := by
  exact integral_finsetSum s fun i hi => continuous_integrable (hf i hi)

lemma mean_casimir {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    mean (fun u : Sphere n => f u * casimir g u) = -energy f g := by
  have hc (i j : Fin n) : Continuous (fun u : Sphere n =>
      f u * rotDeriv (generator n i j) (rotDeriv (generator n i j) g) u) :=
    (hf.continuous.comp continuous_subtype_val).mul
      ((continuous_rotDeriv _ (contDiff_rotDeriv _ hg)).comp continuous_subtype_val)
  have heq : (fun u : Sphere n => f u * casimir g u) =
      fun u : Sphere n => (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
        f u * rotDeriv (generator n i j) (rotDeriv (generator n i j) g) u := by
    funext u
    simp only [casimir, mul_left_comm (f u) (1 / 2 : ℝ), Finset.mul_sum]
  rw [heq, mean, integral_const_mul]
  change (1 / 2 : ℝ) * mean (fun u : Sphere n => ∑ i : Fin n, ∑ j : Fin n,
      f u * rotDeriv (generator n i j) (rotDeriv (generator n i j) g) u) = _
  rw [mean_sum _ (fun i _ => continuous_finsetSum _ fun j _ => hc i j)]
  rw [show -energy f g = (1 / 2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
      -mean (fun u : Sphere n => rotDeriv (generator n i j) f u *
        rotDeriv (generator n i j) g u) by
    simp [energy, Finset.sum_neg_distrib]]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mean_sum _ (fun j _ => hc i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [mean_rotDeriv_mul _ (generator_skew n i j) hf (contDiff_rotDeriv _ hg)]
  simp only [mul_comm]

/-- Ambient evaluation of a polynomial, using the Euclidean coordinates. -/
def polynomialFunction {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Space n → ℝ :=
  fun x => MvPolynomial.eval (fun i => x i) p

lemma polynomialFunction_contDiff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ⊤ (polynomialFunction p) := by
  unfold polynomialFunction
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const : ContDiff ℝ ⊤ (fun _ : Space n => c))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp =>
    have hi : ContDiff ℝ ⊤ (fun x : Space n => x i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hp.mul hi

/-- Polynomial rotation differentiation, a derivation preserving degree. -/
def polynomialRotation {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.X i * MvPolynomial.pderiv j p - MvPolynomial.X j * MvPolynomial.pderiv i p

lemma rotDeriv_add {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f g : Space n → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : Space n) :
    rotDeriv T (fun y => f y + g y) x = rotDeriv T f x + rotDeriv T g x := by
  simp only [rotDeriv, fderiv_fun_add (hf x) (hg x), add_apply]

lemma rotDeriv_const {n : ℕ} (T : Space n →L[ℝ] Space n) (c : ℝ) (x : Space n) :
    rotDeriv T (fun _ => c) x = 0 := by
  simp [rotDeriv]

lemma rotDeriv_coordinate {n : ℕ} (i j a : Fin n) (x : Space n) :
    rotDeriv (generator n i j) (fun y => y a) x =
      x i * (if j = a then 1 else 0) - x j * (if i = a then 1 else 0) := by
  change fderiv ℝ (EuclideanSpace.proj a) x (generator n i j x) = _
  rw [ContinuousLinearMap.fderiv]
  exact generator_apply_coord i j a x

lemma polynomialRotation_add {n : ℕ} (i j : Fin n) (p q : MvPolynomial (Fin n) ℝ) :
    polynomialRotation i j (p + q) = polynomialRotation i j p + polynomialRotation i j q := by
  simp only [polynomialRotation, map_add]
  ring

lemma polynomialRotation_mul {n : ℕ} (i j : Fin n) (p q : MvPolynomial (Fin n) ℝ) :
    polynomialRotation i j (p * q) =
      p * polynomialRotation i j q + q * polynomialRotation i j p := by
  simp only [polynomialRotation, MvPolynomial.pderiv_mul]
  ring

lemma polynomialRotation_C {n : ℕ} (i j : Fin n) (c : ℝ) :
    polynomialRotation i j (MvPolynomial.C c) = 0 := by
  simp [polynomialRotation]

lemma polynomialFunction_add {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    polynomialFunction (p + q) = fun x => polynomialFunction p x + polynomialFunction q x := by
  funext x
  exact MvPolynomial.eval_add

lemma polynomialFunction_mul {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    polynomialFunction (p * q) = fun x => polynomialFunction p x * polynomialFunction q x := by
  funext x
  exact MvPolynomial.eval_mul

lemma polynomialFunction_X {n : ℕ} (i : Fin n) :
    polynomialFunction (MvPolynomial.X i) = fun x : Space n => x i := by
  funext x
  exact MvPolynomial.eval_X _

lemma polynomialFunction_C {n : ℕ} (c : ℝ) :
    polynomialFunction (MvPolynomial.C c : MvPolynomial (Fin n) ℝ) = fun _ => c := by
  funext x
  exact MvPolynomial.eval_C _

/-- The formal polynomial generator agrees with actual differentiation. -/
lemma rotDeriv_polynomialFunction {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    rotDeriv (generator n i j) (polynomialFunction p) =
      polynomialFunction (polynomialRotation i j p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [polynomialFunction_C, polynomialRotation_C]
    funext x
    simp [rotDeriv_const, polynomialFunction]
  | add p q hp hq =>
    rw [polynomialFunction_add, polynomialRotation_add, polynomialFunction_add]
    funext x
    rw [rotDeriv_add _ ((polynomialFunction_contDiff p).differentiable (by norm_num))
      ((polynomialFunction_contDiff q).differentiable (by norm_num)), hp, hq]
  | mul_X p a hp =>
    rw [polynomialFunction_mul, polynomialRotation_mul, polynomialFunction_add,
      polynomialFunction_mul, polynomialFunction_mul]
    funext x
    rw [rotDeriv_mul _ ((polynomialFunction_contDiff p).differentiable (by norm_num))
      ((polynomialFunction_contDiff (MvPolynomial.X a)).differentiable (by norm_num)), hp]
    congr 1
    rw [polynomialFunction_X, rotDeriv_coordinate]
    by_cases hia : i = a <;> by_cases hja : j = a <;>
      simp [polynomialFunction, polynomialRotation, hia, hja, eq_comm]

open MvPolynomial

/-- Radius squared as an ambient polynomial. -/
def radiusPolynomial (n : ℕ) : MvPolynomial (Fin n) ℝ := ∑ i : Fin n, X i ^ 2

def eulerPolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, X i * pderiv i p

def laplacePolynomial {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, pderiv i (pderiv i p)

lemma polynomialRotation_twice {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    polynomialRotation i j (polynomialRotation i j p) =
      X i ^ 2 * pderiv j (pderiv j p) + X j ^ 2 * pderiv i (pderiv i p) -
      X i * X j * pderiv j (pderiv i p) - X i * X j * pderiv i (pderiv j p) -
      X i * pderiv i p - X j * pderiv j p +
      (if i = j then 2 * (X i * pderiv i p) else 0) := by
  by_cases h : i = j
  · subst j
    simp only [polynomialRotation, sub_self, map_zero, mul_zero, ite_true]
    ring
  · simp only [polynomialRotation, map_sub, MvPolynomial.pderiv_mul,
      pderiv_X, Pi.single_apply, h, Ne.symm h, ite_false, ite_true, one_mul, zero_mul]
    ring

lemma eulerPolynomial_twice {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    eulerPolynomial (eulerPolynomial p) = eulerPolynomial p +
      ∑ i : Fin n, ∑ j : Fin n, X i * X j * pderiv i (pderiv j p) := by
  have h (i : Fin n) : (∑ j : Fin n, X i *
      (pderiv i (X j) * pderiv j p + X j * pderiv i (pderiv j p))) =
      X i * pderiv i p + ∑ j : Fin n, X i * X j * pderiv i (pderiv j p) := by
    simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
    congr 1
    simp [pderiv_X, Pi.single_apply, eq_comm]
  simp only [eulerPolynomial, map_sum, MvPolynomial.pderiv_mul, Finset.mul_sum]
  simp_rw [h, Finset.sum_add_distrib]

lemma sum_polynomialRotation_twice {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, polynomialRotation i j (polynomialRotation i j p) =
      2 * (radiusPolynomial n * laplacePolynomial p) -
      2 * eulerPolynomial (eulerPolynomial p) -
      2 * ((n : MvPolynomial (Fin n) ℝ) - 2) * eulerPolynomial p := by
  have hA : (∑ i : Fin n, ∑ j : Fin n, X i ^ 2 * pderiv j (pderiv j p)) =
      radiusPolynomial n * laplacePolynomial p := by
    rw [radiusPolynomial, laplacePolynomial, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hB : (∑ i : Fin n, ∑ j : Fin n, X j ^ 2 * pderiv i (pderiv i p)) =
      radiusPolynomial n * laplacePolynomial p := by
    rw [Finset.sum_comm]
    exact hA
  have hC : (∑ i : Fin n, ∑ j : Fin n, X i * X j * pderiv j (pderiv i p)) =
      ∑ i : Fin n, ∑ j : Fin n, X i * X j * pderiv i (pderiv j p) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (X j) (X i)]
  have hD : (∑ i : Fin n, ∑ j : Fin n, X i * pderiv i p) =
      (n : MvPolynomial (Fin n) ℝ) * eulerPolynomial p := by
    simp [eulerPolynomial, nsmul_eq_mul, Finset.mul_sum]
  have hE : (∑ i : Fin n, ∑ j : Fin n, X j * pderiv j p) =
      (n : MvPolynomial (Fin n) ℝ) * eulerPolynomial p := by
    rw [Finset.sum_comm]
    exact hD
  have hF : (∑ i : Fin n, ∑ j : Fin n,
      if i = j then 2 * (X i * pderiv i p) else 0) = 2 * eulerPolynomial p := by
    simp [eulerPolynomial, Finset.mul_sum]
  simp only [polynomialRotation_twice, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hA, hB, hC, hD, hE, hF, eulerPolynomial_twice]
  ring

/-- The spherical Laplace eigenvalues. -/
def eigenvalue (n d : ℕ) : ℝ := (d : ℝ) * ((d : ℝ) + n - 2)

lemma eulerPolynomial_nsmul {n : ℕ} (d : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    eulerPolynomial (d • p) = d • eulerPolynomial p := by
  simp only [eulerPolynomial, map_nsmul]
  simp only [nsmul_eq_mul]
  simp_rw [mul_left_comm (X _) (d : MvPolynomial (Fin n) ℝ)]
  rw [← Finset.mul_sum]

lemma eulerPolynomial_homogeneous {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) : eulerPolynomial p = d • p :=
  hp.sum_X_mul_pderiv

lemma sum_polynomialRotation_homogeneous {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) :
    ∑ i : Fin n, ∑ j : Fin n, polynomialRotation i j (polynomialRotation i j p) =
      2 * (radiusPolynomial n * laplacePolynomial p - C (eigenvalue n d) * p) := by
  have he := eulerPolynomial_homogeneous hp
  have hee : eulerPolynomial (eulerPolynomial p) = d • (d • p) := by
    rw [he, eulerPolynomial_nsmul, he]
  rw [sum_polynomialRotation_twice, hee, he]
  simp only [nsmul_eq_mul, eigenvalue, map_mul, map_sub, map_add, map_natCast, map_ofNat]
  ring

lemma polynomialFunction_radius {n : ℕ} (x : Space n) :
    polynomialFunction (radiusPolynomial n) x = ‖x‖ ^ 2 := by
  unfold polynomialFunction radiusPolynomial
  simp only [map_sum, map_pow, eval_X]
  exact (EuclideanSpace.real_norm_sq_eq x).symm

/-- Polar Laplacian identity, derived from finite rotation sums and Euler's
identity rather than assumed as a spherical calculus interface. -/
lemma casimir_polynomialFunction {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (x : Space n) :
    casimir (polynomialFunction p) x =
      ‖x‖ ^ 2 * polynomialFunction (laplacePolynomial p) x -
        eigenvalue n d * polynomialFunction p x := by
  have hs := congrArg (MvPolynomial.eval (fun i => x i))
    (sum_polynomialRotation_homogeneous hp)
  simp only [map_sum, map_mul, map_sub, eval_C, map_ofNat] at hs
  simp only [casimir, rotDeriv_polynomialFunction, polynomialFunction]
  rw [hs]
  have hr := polynomialFunction_radius x
  unfold polynomialFunction at hr
  rw [hr]
  ring

lemma casimir_harmonic {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hΔp : laplacePolynomial p = 0) (x : Space n) :
    casimir (polynomialFunction p) x = -eigenvalue n d * polynomialFunction p x := by
  rw [casimir_polynomialFunction hp, hΔp]
  simp [polynomialFunction]

lemma eigenvalue_strictMono {n : ℕ} (hn : 2 ≤ n) : StrictMono (eigenvalue n) := by
  intro d e hde
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hde' : (d : ℝ) < e := by exact_mod_cast hde
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  unfold eigenvalue
  nlinarith

/-- Distinct homogeneous harmonic degrees are orthogonal under actual
normalized surface measure. -/
lemma harmonic_orthogonal {n d e : ℕ} (hn : 2 ≤ n)
    {p q : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e)
    (hΔp : laplacePolynomial p = 0) (hΔq : laplacePolynomial q = 0) (hde : d ≠ e) :
    mean (fun u : Sphere n => polynomialFunction p u * polynomialFunction q u) = 0 := by
  have : NeZero n := ⟨by omega⟩
  have h₁ := mean_casimir (f := polynomialFunction p) (g := polynomialFunction q)
    ((polynomialFunction_contDiff p).of_le le_top) ((polynomialFunction_contDiff q).of_le le_top)
  have h₂ := mean_casimir (f := polynomialFunction q) (g := polynomialFunction p)
    ((polynomialFunction_contDiff q).of_le le_top) ((polynomialFunction_contDiff p).of_le le_top)
  simp_rw [casimir_harmonic hq hΔq, mul_left_comm (polynomialFunction p _) (-eigenvalue n e)] at h₁
  simp_rw [casimir_harmonic hp hΔp, mul_left_comm (polynomialFunction q _) (-eigenvalue n d),
    mul_comm (polynomialFunction q _) (polynomialFunction p _)] at h₂
  rw [mean, integral_const_mul] at h₁ h₂
  rw [energy_symm (polynomialFunction q) (polynomialFunction p)] at h₂
  have hne : eigenvalue n d ≠ eigenvalue n e := (eigenvalue_strictMono hn).injective.ne hde
  unfold mean
  have hz : (eigenvalue n d - eigenvalue n e) *
      (∫ u : Sphere n, polynomialFunction p u * polynomialFunction q u ∂sigma n) = 0 := by
    nlinarith [h₁, h₂]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

lemma laplacePolynomial_add {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (p + q) = laplacePolynomial p + laplacePolynomial q := by
  simp [laplacePolynomial, Finset.sum_add_distrib]

lemma laplacePolynomial_sub {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (p - q) = laplacePolynomial p - laplacePolynomial q := by
  simp [laplacePolynomial, Finset.sum_sub_distrib]

lemma laplacePolynomial_C_mul {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (C c * p) = C c * laplacePolynomial p := by
  simp [laplacePolynomial, Finset.mul_sum]

lemma laplacePolynomial_homogeneous {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) : (laplacePolynomial p).IsHomogeneous (d - 2) := by
  apply IsHomogeneous.sum
  intro i _
  convert hp.pderiv.pderiv using 1

lemma pderiv_radiusPolynomial {n : ℕ} (i : Fin n) :
    pderiv i (radiusPolynomial n) = 2 * X i := by
  simp [radiusPolynomial, pderiv_X, Pi.single_apply, eq_comm]

lemma radiusPolynomial_homogeneous (n : ℕ) : (radiusPolynomial n).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_X_pow i 2

lemma laplacePolynomial_radius_mul {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (radiusPolynomial n * p) =
      radiusPolynomial n * laplacePolynomial p + 4 * eulerPolynomial p + 2 * n * p := by
  have hd (i : Fin n) : pderiv i (pderiv i (radiusPolynomial n * p)) =
      radiusPolynomial n * pderiv i (pderiv i p) + 4 * (X i * pderiv i p) + 2 * p := by
    simp only [pderiv_mul, pderiv_radiusPolynomial, map_add, pderiv_X_self]
    have htwo : pderiv i (2 : MvPolynomial (Fin n) ℝ) = 0 := (pderiv i).map_natCast 2
    rw [htwo]
    ring
  simp only [laplacePolynomial, hd, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, eulerPolynomial]
  ring

lemma laplacePolynomial_radius_mul_homogeneous {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) :
    laplacePolynomial (radiusPolynomial n * p) =
      radiusPolynomial n * laplacePolynomial p + C (4 * (d : ℝ) + 2 * n) * p := by
  rw [laplacePolynomial_radius_mul, eulerPolynomial_homogeneous hp]
  simp only [nsmul_eq_mul, map_add, map_mul, map_ofNat, map_natCast]
  ring

/-- The nonzero radial coefficient in the finite Fischer decomposition. -/
def radialCoefficient (n l j : ℕ) : ℝ := 2 * (j + 1 : ℕ) * (2 * l + 2 * (j + 1 : ℕ) + n - 2)

lemma radialCoefficient_pos {n : ℕ} (hn : 2 ≤ n) (l j : ℕ) :
    0 < radialCoefficient n l j := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  unfold radialCoefficient
  push_cast
  apply mul_pos (by positivity)
  linarith

lemma radius_pow_mul_homogeneous {n l : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous l) (j : ℕ) :
    ((radiusPolynomial n) ^ j * p).IsHomogeneous (2 * j + l) :=
  ((radiusPolynomial_homogeneous n).pow j).mul hp

lemma laplacePolynomial_radial_harmonic {n l : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous l) (hΔp : laplacePolynomial p = 0) (j : ℕ) :
    laplacePolynomial (radiusPolynomial n ^ (j + 1) * p) =
      C (radialCoefficient n l j) * (radiusPolynomial n ^ j * p) := by
  have hr (a : ℕ) : radiusPolynomial n ^ (a + 1) * p =
      radiusPolynomial n * (radiusPolynomial n ^ a * p) := by rw [pow_succ']; ring
  induction j with
  | zero =>
      simp only [Nat.zero_add, pow_one, pow_zero, one_mul]
      rw [laplacePolynomial_radius_mul_homogeneous hp, hΔp, mul_zero, zero_add]
      congr 2
      simp only [radialCoefficient]
      ring
  | succ j ih =>
      rw [hr (j + 1), laplacePolynomial_radius_mul_homogeneous (radius_pow_mul_homogeneous hp (j + 1)), ih]
      rw [hr j]
      simp only [radialCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        map_mul, map_add, map_sub, map_ofNat, map_natCast]
      ring

lemma laplacePolynomial_smul {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    laplacePolynomial (c • p) = c • laplacePolynomial p := by
  simpa only [← C_mul'] using laplacePolynomial_C_mul c p

lemma laplacePolynomial_eq_zero_small {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hd : d < 2) : laplacePolynomial p = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have h₀ : (pderiv i p).IsHomogeneous 0 := by
    convert hp.pderiv using 1
    omega
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h₀
  rw [h₀, pderiv_C]

/-- Algebraic span of radius powers times homogeneous harmonics of fixed total degree. -/
def fischerSpan (n d : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  Submodule.span ℝ {q | ∃ j l p, 2 * j + l = d ∧ p.IsHomogeneous l ∧
    laplacePolynomial p = 0 ∧ q = radiusPolynomial n ^ j * p}

lemma fischerSpan_le_homogeneous (n d : ℕ) :
    fischerSpan n d ≤ homogeneousSubmodule (Fin n) ℝ d := by
  apply Submodule.span_le.mpr
  rintro q ⟨j, l, p, hd, hp, _, rfl⟩
  exact hd ▸ radius_pow_mul_homogeneous hp j

lemma harmonic_mem_fischerSpan {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hΔp : laplacePolynomial p = 0) : p ∈ fischerSpan n d := by
  exact Submodule.subset_span ⟨0, d, p, by omega, hp, hΔp, by simp⟩

lemma fischerSpan_laplace_preimage {n d : ℕ} (hn : 2 ≤ n) {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ fischerSpan n d) :
    ∃ q ∈ fischerSpan n (d + 2), laplacePolynomial q = p := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, l, p, hd, hhom, hΔ, rfl⟩ := hx
      refine ⟨(radialCoefficient n l j)⁻¹ • (radiusPolynomial n ^ (j + 1) * p), ?_, ?_⟩
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨j + 1, l, p, by omega, hhom, hΔ, rfl⟩
      · rw [laplacePolynomial_smul, laplacePolynomial_radial_harmonic hhom hΔ]
        rw [C_mul', smul_smul, inv_mul_cancel₀ (ne_of_gt (radialCoefficient_pos hn l j)), one_smul]
  | zero => exact ⟨0, Submodule.zero_mem _, by simp [laplacePolynomial]⟩
  | add x y _ _ hx hy =>
      obtain ⟨q, hq, hΔq⟩ := hx
      obtain ⟨r, hr, hΔr⟩ := hy
      exact ⟨q + r, Submodule.add_mem _ hq hr, by rw [laplacePolynomial_add, hΔq, hΔr]⟩
  | smul c x _ hx =>
      obtain ⟨q, hq, hΔq⟩ := hx
      exact ⟨c • q, Submodule.smul_mem _ c hq, by rw [laplacePolynomial_smul, hΔq]⟩

/-- Finite Fischer decomposition: the induction on the degree. -/
lemma homogeneous_mem_fischerSpan {n : ℕ} (hn : 2 ≤ n) (d : ℕ)
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d) : p ∈ fischerSpan n d := by
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
      by_cases hd : d < 2
      · exact harmonic_mem_fischerSpan hp (laplacePolynomial_eq_zero_small hp hd)
      · have hdp := ih (d - 2) (by omega) (laplacePolynomial_homogeneous hp)
        obtain ⟨q, hq, hΔq⟩ := fischerSpan_laplace_preimage hn hdp
        have hd' : d - 2 + 2 = d := by omega
        rw [hd'] at hq
        have hhomq := fischerSpan_le_homogeneous n d hq
        have hrem : p - q ∈ fischerSpan n d := harmonic_mem_fischerSpan (hp.sub hhomq)
          (by rw [laplacePolynomial_sub, hΔq, sub_self])
        simpa only [sub_add_cancel] using (fischerSpan n d).add_mem hrem hq

/-- Actual polynomial restrictions, as continuous functions on the sphere. -/
def polynomialRestriction (n : ℕ) : MvPolynomial (Fin n) ℝ →ₐ[ℝ] C(Sphere n, ℝ) where
  toFun p := ⟨fun u => polynomialFunction p u,
    (polynomialFunction_contDiff p).continuous.comp continuous_subtype_val⟩
  map_zero' := by
    ext u
    change MvPolynomial.eval (fun i => (u : Space n) i) 0 = 0
    exact map_zero _
  map_one' := by
    ext u
    change MvPolynomial.eval (fun i => (u : Space n) i) 1 = 1
    exact map_one _
  map_add' p q := by ext u; exact MvPolynomial.eval_add
  map_mul' p q := by ext u; exact MvPolynomial.eval_mul
  commutes' c := by ext u; exact MvPolynomial.eval_C _

lemma polynomialRestriction_apply {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (u : Sphere n) :
    polynomialRestriction n p u = polynomialFunction p u := rfl

lemma polynomialRestriction_radius (n : ℕ) : polynomialRestriction n (radiusPolynomial n) = 1 := by
  ext u
  change polynomialFunction (radiusPolynomial n) u = 1
  rw [polynomialFunction_radius, norm_coe, one_pow]

lemma polynomialRestriction_separates (n : ℕ) : (polynomialRestriction n).range.SeparatesPoints := by
  intro u v huv
  have h : ∃ i : Fin n, (u : Space n) i ≠ (v : Space n) i := by
    by_contra! h
    apply huv
    apply Subtype.ext
    exact PiLp.ext h
  obtain ⟨i, hi⟩ := h
  refine ⟨polynomialRestriction n (X i), ⟨polynomialRestriction n (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa only [polynomialRestriction_apply, polynomialFunction_X] using hi

lemma polynomialRestriction_dense (n : ℕ) : DenseRange (polynomialRestriction n) := by
  apply dense_iff_closure_eq.mpr
  change closure (↑(polynomialRestriction n).range : Set C(Sphere n, ℝ)) = univ
  rw [← Subalgebra.topologicalClosure_coe,
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (polynomialRestriction_separates n)]
  rfl

def polynomialL2 (n : ℕ) [NeZero n] : MvPolynomial (Fin n) ℝ →ₗ[ℝ] H n :=
  (toH n).toLinearMap.comp (polynomialRestriction n).toLinearMap

lemma polynomialL2_dense (n : ℕ) [NeZero n] : DenseRange (polynomialL2 n) :=
  (ContinuousMap.toLp_denseRange ℝ (sigma n) ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).comp
    (polynomialRestriction_dense n) (toH n).continuous

def laplaceLinear (n : ℕ) : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun := laplacePolynomial
  map_add' := laplacePolynomial_add
  map_smul' := laplacePolynomial_smul

def harmonicPolynomials (n d : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  homogeneousSubmodule (Fin n) ℝ d ⊓ (laplaceLinear n).ker

instance harmonicPolynomials_finite (n d : ℕ) : FiniteDimensional ℝ (harmonicPolynomials n d) := by
  have : FiniteDimensional ℝ (homogeneousSubmodule (Fin n) ℝ d) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin n) ℝ d)
  exact Submodule.finiteDimensional_of_le (show harmonicPolynomials n d ≤
    homogeneousSubmodule (Fin n) ℝ d from inf_le_left)

/-- The genuine homogeneous harmonic subspaces of spherical L². -/
def harmonicSpace (n d : ℕ) [NeZero n] : Submodule ℝ (H n) :=
  (harmonicPolynomials n d).map (polynomialL2 n)

instance harmonicSpace_finite (n d : ℕ) [NeZero n] : FiniteDimensional ℝ (harmonicSpace n d) := by
  apply Module.Finite.of_fg
  exact ((Submodule.fg_iff_finiteDimensional (harmonicPolynomials n d)).mpr inferInstance).map _

lemma harmonicSpace_orthogonal {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    OrthogonalFamily ℝ (fun d => harmonicSpace n d) (fun d => (harmonicSpace n d).subtypeₗᵢ) := by
  intro d e hde p q
  obtain ⟨P, hP, hPeq⟩ := p.property
  obtain ⟨Q, hQ, hQeq⟩ := q.property
  change ⟪(p : H n), (q : H n)⟫ = 0
  rw [← hPeq, ← hQeq]
  change ⟪toH n (polynomialRestriction n P), toH n (polynomialRestriction n Q)⟫ = 0
  rw [inner_toH]
  exact harmonic_orthogonal hn hP.1 hQ.1 hP.2 hQ.2 hde

lemma polynomialL2_mem_iSup_of_fischer {n d : ℕ} [NeZero n] {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ fischerSpan n d) : polynomialL2 n p ∈ ⨆ l, harmonicSpace n l := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, l, p, _, hhom, hΔ, rfl⟩ := hx
      have hr : polynomialL2 n (radiusPolynomial n ^ j * p) = polynomialL2 n p := by
        change toH n (polynomialRestriction n _) = toH n (polynomialRestriction n p)
        rw [map_mul, map_pow, polynomialRestriction_radius, one_pow, one_mul]
      rw [hr]
      exact Submodule.mem_iSup_of_mem l (Submodule.mem_map.mpr ⟨p, ⟨hhom, hΔ⟩, rfl⟩)
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using Submodule.add_mem _ hp hq
  | smul c p _ hp => simpa only [map_smul] using Submodule.smul_mem _ c hp

lemma polynomialL2_mem_iSup {n : ℕ} (hn : 2 ≤ n) [NeZero n] (p : MvPolynomial (Fin n) ℝ) :
    polynomialL2 n p ∈ ⨆ l, harmonicSpace n l := by
  rw [← sum_homogeneousComponent p, map_sum]
  apply Submodule.sum_mem
  intro d _
  exact polynomialL2_mem_iSup_of_fischer
    (homogeneous_mem_fischerSpan hn d (homogeneousComponent_isHomogeneous d p))

/-- Completeness under the actual measure, using Stone--Weierstrass and finite
Fischer decomposition, with no assumed spectral interface. -/
lemma harmonicSpace_total {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    (⨆ l, harmonicSpace n l).topologicalClosure = ⊤ := by
  apply SetLike.coe_injective
  rw [Submodule.topologicalClosure_coe, Submodule.top_coe]
  apply dense_iff_closure_eq.mp
  exact (polynomialL2_dense n).mono (by rintro _ ⟨p, rfl⟩; exact polynomialL2_mem_iSup hn p)

lemma energy_add_right {n : ℕ} [NeZero n] {f g h : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h) :
    energy f (fun x => g x + h x) = energy f g + energy f h := by
  unfold energy
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [rotDeriv_add _ (hg.differentiable (by norm_num))
    (hh.differentiable (by norm_num)), mul_add]
  exact integral_add
    (continuous_integrable (((continuous_rotDeriv _ hf).mul (continuous_rotDeriv _ hg)).comp
      continuous_subtype_val))
    (continuous_integrable (((continuous_rotDeriv _ hf).mul (continuous_rotDeriv _ hh)).comp
      continuous_subtype_val))

lemma energy_add_left {n : ℕ} [NeZero n] {f g h : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h) :
    energy (fun x => f x + g x) h = energy f h + energy g h := by
  simpa only [energy_symm] using energy_add_right hh hf hg

lemma rotDeriv_const_mul {n : ℕ} (T : Space n →L[ℝ] Space n)
    {f : Space n → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (x : Space n) :
    rotDeriv T (fun y => c * f y) x = c * rotDeriv T f x := by
  unfold rotDeriv
  rw [fderiv_const_mul (hf x) c]
  rfl

lemma energy_const_mul_right {n : ℕ} {f g : Space n → ℝ}
    (hg : Differentiable ℝ g) (c : ℝ) :
    energy f (fun x => c * g x) = c * energy f g := by
  simp only [energy, rotDeriv_const_mul _ hg c, mul_left_comm _ c, mean, integral_const_mul,
    ← Finset.mul_sum]

lemma energy_const_mul_left {n : ℕ} {f g : Space n → ℝ}
    (hf : Differentiable ℝ f) (c : ℝ) :
    energy (fun x => c * f x) g = c * energy f g := by
  simpa only [energy_symm] using energy_const_mul_right (f := g) hf c

lemma energy_sub_self {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    energy (fun x => f x - g x) (fun x => f x - g x) =
      energy f f - 2 * energy f g + energy g g := by
  have hsub : (fun x => f x - g x) = fun x => f x + (-1) * g x := by funext x; ring
  rw [hsub, energy_add_left hf (contDiff_const.mul hg) (hf.add (contDiff_const.mul hg)),
    energy_add_right hf hf (contDiff_const.mul hg),
    energy_const_mul_left (hg.differentiable (by norm_num)),
    energy_add_right hg hf (contDiff_const.mul hg),
    energy_const_mul_right (hg.differentiable (by norm_num)),
    energy_const_mul_right (hg.differentiable (by norm_num)), energy_symm g f]
  ring

lemma energy_zero_right {n : ℕ} (f : Space n → ℝ) : energy f (fun _ => 0) = 0 := by
  simp [energy, rotDeriv_const, mean]

lemma energy_finset_sum_right {n : ℕ} [NeZero n] {ι : Type uι} (s : Finset ι)
    {f : Space n → ℝ} {g : ι → Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ∀ i, ContDiff ℝ 1 (g i)) :
    energy f (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, energy f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [energy_zero_right]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [energy_add_right hf (hg a) (ContDiff.sum fun i _ => hg i), ih]

/-- Integration by parts against each genuine harmonic eigenfunction. -/
lemma energy_harmonic_right {n d : ℕ} [NeZero n] {f : Space n → ℝ}
    {p : MvPolynomial (Fin n) ℝ} (hf : ContDiff ℝ 1 f) (hp : p.IsHomogeneous d)
    (hΔp : laplacePolynomial p = 0) :
    energy f (polynomialFunction p) = eigenvalue n d *
      mean (fun u : Sphere n => f u * polynomialFunction p u) := by
  have h := mean_casimir hf ((polynomialFunction_contDiff p).of_le le_top)
  simp_rw [casimir_harmonic hp hΔp, mul_left_comm (f _) (-eigenvalue n d)] at h
  rw [mean, integral_const_mul] at h
  unfold mean
  linarith

lemma polynomialFunction_smul_argument {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (c : ℝ) (x : Space n) :
    polynomialFunction p (c • x) = c ^ d * polynomialFunction p x := by
  unfold polynomialFunction
  simp only [MvPolynomial.eval_eq, PiLp.smul_apply, smul_eq_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← hp.degree_eq_sum_deg_support ha]
  ring

lemma harmonicSpace_zero_constant {n : ℕ} [NeZero n] {v : H n} (hv : v ∈ harmonicSpace n 0) :
    ∃ c : ℝ, v = toH n (ContinuousMap.const (Sphere n) c) := by
  obtain ⟨p, hp, rfl⟩ := hv
  have hhom : p.IsHomogeneous 0 := hp.1
  rw [← totalDegree_zero_iff_isHomogeneous,
    totalDegree_eq_zero_iff_eq_C] at hhom
  refine ⟨p.coeff 0, ?_⟩
  rw [hhom]
  simp only [coeff_C]
  change toH n (polynomialRestriction n (C _)) = _
  congr 1
  ext u
  exact congrFun (polynomialFunction_C _) _

lemma constant_mem_harmonicSpace_zero (n : ℕ) [NeZero n] (c : ℝ) :
    toH n (ContinuousMap.const (Sphere n) c) ∈ harmonicSpace n 0 := by
  refine Submodule.mem_map.mpr ⟨C c, ⟨isHomogeneous_C _ _, ?_⟩, ?_⟩
  · simp [LinearMap.mem_ker, laplaceLinear, laplacePolynomial]
  · change toH n (polynomialRestriction n (C c)) = _
    congr 1
    ext u
    exact congrFun (polynomialFunction_C _) _

lemma harmonicSpace_zero_projection (n : ℕ) [NeZero n] (f : C(Sphere n, ℝ)) :
    (harmonicSpace n 0).starProjection (toH n f) =
      toH n (ContinuousMap.const (Sphere n) (mean f)) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (constant_mem_harmonicSpace_zero n _)
  intro v hv
  obtain ⟨c, rfl⟩ := harmonicSpace_zero_constant hv
  rw [← map_sub, inner_toH]
  change mean (fun u : Sphere n => (f u - mean f) * c) = 0
  unfold mean
  rw [integral_mul_const, integral_sub (continuous_integrable f.continuous)
    (integrable_const _)]
  simp

end PettyProjection.Spherical
end

end OAI
