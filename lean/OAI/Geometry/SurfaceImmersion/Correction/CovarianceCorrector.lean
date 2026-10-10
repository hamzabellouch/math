import Mathlib

namespace OAI

/-!
The covariance solve in paper 094-01, Section 6, equations
`covariance-equation` and `covariance-solve`. The averaging operator below is
the actual normalized Haar integral on the period circle. The finite linear
solve is proved invertible using constant positive speed and connectedness.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

abbrev Period := UnitAddCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Normalized average over one period. -/
def average (f : Period → E) : E := ∫ t, f t ∂AddCircle.haarAddCircle

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma integrable_of_continuous {f : Period → E} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hf.continuousOn.integrableOn_compact isCompact_univ

omit [CompleteSpace E] in
lemma average_add {f g : Period → E} (hf : Continuous f) (hg : Continuous g) :
    average (fun t => f t + g t) = average f + average g :=
  integral_add (integrable_of_continuous hf) (integrable_of_continuous hg)

omit [CompleteSpace E] in
lemma average_sub {f g : Period → E} (hf : Continuous f) (hg : Continuous g) :
    average (fun t => f t - g t) = average f - average g :=
  integral_sub (integrable_of_continuous hf) (integrable_of_continuous hg)

@[simp] lemma average_const (v : E) : average (fun _ : Period => v) = v := by
  simp [average]

omit [CompleteSpace E] in
lemma average_const_smul (c : ℝ) (f : Period → E) :
    average (fun t => c • f t) = c • average f := integral_smul c f

lemma average_smul_const (f : Period → ℝ) (v : E) :
    average (fun t => f t • v) = average f • v := integral_smul_const f v

lemma average_inner_right {f : Period → E} (hf : Continuous f) (m : E) :
    average (fun t => inner ℝ (f t) m) = inner ℝ (average f) m := by
  calc
    _ = average (fun t => inner ℝ m (f t)) := by
      congr 1
      funext t
      exact real_inner_comm _ _
    _ = inner ℝ m (average f) := by
      simpa only [average, innerSL_apply_apply] using
        (innerSL ℝ m).integral_comp_comm (integrable_of_continuous hf)
    _ = _ := real_inner_comm _ _

/-- The covariance operator applied to a vector. -/
def covariance (V : Period → E) (v m : E) : E :=
  average (fun t => inner ℝ (V t - v) m • (V t - v))

def correctedScalar (V : Period → E) (v : E) (q : ℝ)
    (r : Period → ℝ) (m : E) : Period → ℝ :=
  fun t => r t + inner ℝ (V t - v) m / q

def correctedVector (V : Period → E) (v : E) (q : ℝ)
    (r : Period → ℝ) (m : E) : Period → E :=
  fun t => q⁻¹ • (correctedScalar V v q r m t • V t - m)

def fluctuation (r : Period → ℝ) : Period → ℝ := fun t => r t - average r

lemma average_centered_inner {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) (m : E) :
    average (fun t => inner ℝ (V t - v) m) = 0 := by
  rw [average_inner_right (f := fun t => V t - v) (hV.sub continuous_const),
    average_sub (f := V) (g := fun _ => v) hV continuous_const,
    average_const, hv, sub_self, inner_zero_left]

lemma average_centered_tensor {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) (m : E) :
    average (fun t => inner ℝ (V t - v) m • V t) = covariance V v m := by
  have hi : Continuous (fun t => inner ℝ (V t - v) m) :=
    (hV.sub continuous_const).inner continuous_const
  calc
    _ = average (fun t => inner ℝ (V t - v) m • (V t - v) +
          inner ℝ (V t - v) m • v) := by
      congr 1
      funext t
      rw [← smul_add, sub_add_cancel]
    _ = covariance V v m + average (fun t => inner ℝ (V t - v) m • v) :=
      average_add (hi.smul (hV.sub continuous_const)) (hi.smul continuous_const)
    _ = covariance V v m := by
      rw [average_smul_const, average_centered_inner hV hv, zero_smul, add_zero]

theorem average_correctedScalar {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) {r : Period → ℝ} (hr : Continuous r)
    (hr0 : average r = 0) (q : ℝ) (m : E) :
    average (correctedScalar V v q r m) = 0 := by
  have hi : Continuous (fun t => inner ℝ (V t - v) m) :=
    (hV.sub continuous_const).inner continuous_const
  change average (fun t => r t + inner ℝ (V t - v) m * q⁻¹) = 0
  rw [average_add (f := r) (g := fun t => inner ℝ (V t - v) m * q⁻¹)
    hr (hi.mul continuous_const)]
  have he : average (fun t => inner ℝ (V t - v) m * q⁻¹) =
      q⁻¹ * average (fun t => inner ℝ (V t - v) m) := by
    simpa only [smul_eq_mul, mul_comm] using
      average_const_smul q⁻¹ (fun t => inner ℝ (V t - v) m)
  rw [he, average_centered_inner hV hv, hr0, mul_zero, add_zero]

theorem average_weighted_correctedScalar {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) {r : Period → ℝ} (hr : Continuous r)
    (q : ℝ) (m : E)
    (hsolve : m - q⁻¹ • covariance V v m = average (fun t => r t • V t)) :
    average (fun t => correctedScalar V v q r m t • V t) = m := by
  have hi : Continuous (fun t => inner ℝ (V t - v) m) :=
    (hV.sub continuous_const).inner continuous_const
  calc
    _ = average (fun t => r t • V t +
          q⁻¹ • (inner ℝ (V t - v) m • V t)) := by
      congr 1
      funext t
      simp only [correctedScalar, add_smul, div_eq_mul_inv, smul_smul]
      rw [mul_comm]
    _ = average (fun t => r t • V t) +
          q⁻¹ • average (fun t => inner ℝ (V t - v) m • V t) := by
      rw [average_add (f := fun t => r t • V t)
          (g := fun t => q⁻¹ • (inner ℝ (V t - v) m • V t))
          (hr.smul hV) (continuous_const.smul (hi.smul hV)),
        average_const_smul]
    _ = average (fun t => r t • V t) + q⁻¹ • covariance V v m := by
      rw [average_centered_tensor hV hv]
    _ = m := (sub_eq_iff_eq_add.mp hsolve).symm

theorem average_correctedVector {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) {r : Period → ℝ} (hr : Continuous r)
    (q : ℝ) (m : E)
    (hsolve : m - q⁻¹ • covariance V v m = average (fun t => r t • V t)) :
    average (correctedVector V v q r m) = 0 := by
  have hh : Continuous (correctedScalar V v q r m) :=
    hr.add (((hV.sub continuous_const).inner continuous_const).div_const q)
  change average (fun t => q⁻¹ • (correctedScalar V v q r m t • V t - m)) = 0
  rw [average_const_smul,
    average_sub (f := fun t => correctedScalar V v q r m t • V t)
      (g := fun _ => m) (hh.smul hV) continuous_const, average_const,
    average_weighted_correctedScalar hV hv hr q m hsolve, sub_self, smul_zero]

omit [CompleteSpace E] in
theorem corrected_projection (V : Period → E)
    (v : E) {r : Period → ℝ} (hr : Continuous r) (hr0 : average r = 0)
    {q : ℝ} (hq : q ≠ 0) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) (m : E) :
    fluctuation (fun t => inner ℝ (V t) (correctedVector V v q r m t)) = r := by
  have he : ∀ t, inner ℝ (V t) (correctedVector V v q r m t) =
      r t - inner ℝ v m / q := by
    intro t
    simp only [correctedVector, correctedScalar, inner_smul_right, inner_sub_right,
      inner_sub_left, hcircle t]
    field_simp [hq]
    ring
  have hav : average (fun t => inner ℝ (V t) (correctedVector V v q r m t)) =
      -inner ℝ v m / q := by
    simp_rw [he]
    rw [average_sub hr continuous_const, average_const, hr0]
    ring
  funext t
  rw [fluctuation, he, hav]
  ring

/-- The actual periodic covariance equation has a continuous zero-mean
solution as soon as the finite-dimensional covariance operator is onto.
In the manuscript, positivity of `Id - Σ/q` supplies precisely this last
linear algebra input. -/
theorem exists_covariance_corrector {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) {r : Period → ℝ} (hr : Continuous r)
    (hr0 : average r = 0) {q : ℝ} (hq : q ≠ 0)
    (hcircle : ∀ t, inner ℝ (V t) (V t) = q)
    (hsurj : Function.Surjective (fun m : E => m - q⁻¹ • covariance V v m)) :
    ∃ W : Period → E, Continuous W ∧ average W = 0 ∧
      fluctuation (fun t => inner ℝ (V t) (W t)) = r := by
  obtain ⟨m, hm⟩ := hsurj (average (fun t => r t • V t))
  refine ⟨correctedVector V v q r m, ?_,
    average_correctedVector hV hv hr q m hm,
    corrected_projection V v hr hr0 hq hcircle m⟩
  have hh : Continuous (correctedScalar V v q r m) :=
    hr.add (((hV.sub continuous_const).inner continuous_const).div_const q)
  exact continuous_const.smul ((hh.smul hV).sub continuous_const)

/-- A continuous scalar function on the period circle cannot switch between
the two roots of a fixed square without taking intermediate values. -/
theorem constant_of_constant_square {a : Period → ℝ} (ha : Continuous a)
    (hsq : ∀ t, a t ^ 2 = a 0 ^ 2) : a = fun _ => a 0 := by
  have hfinite : (Set.range a).Finite := by
    apply ((Set.finite_singleton (-a 0)).insert (a 0)).subset
    rintro _ ⟨t, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (sq_eq_sq_iff_eq_or_eq_neg.mp (hsq t))
  have hsub : (Set.range a).Subsingleton :=
    (isPreconnected_range ha).isDiscrete_iff_subsingleton.mp hfinite.isDiscrete
  funext t
  exact hsub ⟨t, rfl⟩ ⟨0, rfl⟩

/-- The covariance defines a linear operator on the orthogonal complement. -/
def covarianceLinearMap (V : Period → E) (hV : Continuous V) (v : E) : E →ₗ[ℝ] E where
  toFun := covariance V v
  map_add' m n := by
    change average (fun t => inner ℝ (V t - v) (m + n) • (V t - v)) = _
    simp_rw [inner_add_right, add_smul]
    exact average_add
      (((hV.sub continuous_const).inner continuous_const).smul (hV.sub continuous_const))
      (((hV.sub continuous_const).inner continuous_const).smul (hV.sub continuous_const))
  map_smul' c m := by
    change average (fun t => inner ℝ (V t - v) (c • m) • (V t - v)) = _
    simp_rw [inner_smul_right, mul_smul]
    exact average_const_smul c _

def meanOperator (V : Period → E) (hV : Continuous V) (v : E) (q : ℝ) : E →ₗ[ℝ] E :=
  LinearMap.id - q⁻¹ • covarianceLinearMap V hV v

omit [CompleteSpace E] in
@[simp] lemma meanOperator_apply (V : Period → E) (hV : Continuous V)
    (v : E) (q : ℝ) (m : E) :
    meanOperator V hV v q m = m - q⁻¹ • covariance V v m := rfl

theorem covariance_inner {V : Period → E} (hV : Continuous V) (v m : E) :
    inner ℝ (covariance V v m) m = average (fun t => (inner ℝ (V t - v) m) ^ 2) := by
  rw [covariance, ← average_inner_right
    (f := fun t => inner ℝ (V t - v) m • (V t - v))
    (((hV.sub continuous_const).inner continuous_const).smul (hV.sub continuous_const)) m]
  congr 1
  funext t
  rw [real_inner_smul_left, pow_two]

theorem average_centered_square {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) (m : E) :
    average (fun t => (inner ℝ (V t - v) m) ^ 2) =
      average (fun t => (inner ℝ (V t) m) ^ 2) - (inner ℝ v m) ^ 2 := by
  let a : Period → ℝ := fun t => inner ℝ (V t) m
  let c : ℝ := inner ℝ v m
  have ha : Continuous a := hV.inner continuous_const
  have hav : average a = c := (average_inner_right hV m).trans (congrArg (fun w => inner ℝ w m) hv)
  have he : (fun t => (inner ℝ (V t - v) m) ^ 2) =
      (fun t => a t ^ 2 - (2 * c) * a t + c ^ 2) := by
    funext t
    dsimp [a, c]
    rw [inner_sub_left]
    ring
  have hasq : Continuous (fun t => a t ^ 2) := by fun_prop
  have hscale : Continuous (fun t => (2 * c) * a t) := continuous_const.mul ha
  have hscaled : average (fun t => (2 * c) * a t) = (2 * c) * average a := by
    simpa only [smul_eq_mul] using average_const_smul (2 * c) a
  rw [he, average_add (f := fun t => a t ^ 2 - (2 * c) * a t)
      (g := fun _ => c ^ 2) (hasq.sub hscale) continuous_const,
    average_sub (f := fun t => a t ^ 2) (g := fun t => (2 * c) * a t)
      hasq hscale, hscaled, average_const, hav]
  change average (fun t => a t ^ 2) - (2 * c) * c + c ^ 2 =
    average (fun t => a t ^ 2) - c ^ 2
  ring

theorem meanOperator_kernel_trivial {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) {q : ℝ} (hq : 0 < q)
    (hcircle : ∀ t, inner ℝ (V t) (V t) = q)
    (m : E) (hm : meanOperator V hV v q m = 0) : m = 0 := by
  let a : Period → ℝ := fun t => inner ℝ (V t) m
  let c : ℝ := inner ℝ v m
  let gap : Period → ℝ := fun t => q * inner ℝ m m - a t ^ 2
  have ha : Continuous a := hV.inner continuous_const
  have hgap : Continuous gap := continuous_const.sub (ha.pow 2)
  have hgapnonneg : ∀ t, 0 ≤ gap t := by
    intro t
    have hcauchy := real_inner_mul_inner_self_le (V t) m
    rw [hcircle t] at hcauchy
    dsimp [gap, a]
    nlinarith only [hcauchy]
  have hmean : average gap = q * inner ℝ m m - average (fun t => a t ^ 2) := by
    exact (average_sub (f := fun _ => q * inner ℝ m m)
      (g := fun t => a t ^ 2) continuous_const (by fun_prop)).trans (by rw [average_const])
  have hkernel : inner ℝ (covariance V v m) m = q * inner ℝ m m := by
    have he := congrArg (fun w => inner ℝ w m) hm
    simp only [meanOperator_apply, inner_sub_left, real_inner_smul_left, inner_zero_left] at he
    have hi : q⁻¹ * inner ℝ (covariance V v m) m = inner ℝ m m := by linarith
    have he' := congrArg (fun x : ℝ => q * x) hi
    simpa only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] using he'
  have hvariance := (covariance_inner hV v m).trans (average_centered_square hV hv m)
  have hsum : average gap + c ^ 2 = 0 := by
    dsimp [c, a] at hmean ⊢
    linarith [hmean, hkernel, hvariance]
  have hnonneg : 0 ≤ average gap := integral_nonneg hgapnonneg
  have havzero : average gap = 0 := by nlinarith [sq_nonneg c]
  have hczero : c = 0 := by nlinarith [sq_nonneg c]
  have hae : gap =ᵐ[AddCircle.haarAddCircle] 0 :=
    (integral_eq_zero_iff_of_nonneg hgapnonneg (integrable_of_continuous hgap)).mp havzero
  have hgapzero : gap = 0 :=
    (hgap.ae_eq_iff_eq AddCircle.haarAddCircle continuous_zero).mp hae
  have hsq : ∀ t, a t ^ 2 = q * inner ℝ m m := by
    intro t
    have h := congrFun hgapzero t
    dsimp [gap] at h
    linarith
  have haconst : a = fun _ => a 0 :=
    constant_of_constant_square ha (fun t => (hsq t).trans (hsq 0).symm)
  have hav : average a = c :=
    (average_inner_right hV m).trans (congrArg (fun w => inner ℝ w m) hv)
  have ha0 : a 0 = 0 := by
    rw [haconst, average_const, hczero] at hav
    exact hav
  have hmm : inner ℝ m m = 0 := by
    have he := hsq 0
    rw [ha0, zero_pow (by decide : 2 ≠ 0)] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hq.ne'
  exact (inner_self_eq_zero.mp hmm)

theorem meanOperator_surjective [FiniteDimensional ℝ E]
    {V : Period → E} (hV : Continuous V) {v : E} (hv : average V = v)
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) :
    Function.Surjective (fun m : E => m - q⁻¹ • covariance V v m) := by
  have hinj : Function.Injective (meanOperator V hV v q) := by
    intro m n hmn
    apply sub_eq_zero.mp
    apply meanOperator_kernel_trivial hV hv hq hcircle
    rw [map_sub, hmn, sub_self]
  exact LinearMap.surjective_of_injective hinj

/-- The finite covariance solve, with its invertibility now proved from the
constant positive speed and connectedness of the periodic parameter space. -/
theorem exists_covariance_corrector_unconditional [FiniteDimensional ℝ E]
    {V : Period → E} (hV : Continuous V) {v : E} (hv : average V = v)
    {r : Period → ℝ} (hr : Continuous r) (hr0 : average r = 0)
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) :
    ∃ W : Period → E, Continuous W ∧ average W = 0 ∧
      fluctuation (fun t => inner ℝ (V t) (W t)) = r :=
  exists_covariance_corrector hV hv hr hr0 hq.ne' hcircle
    (meanOperator_surjective hV hv hq hcircle)

/-- Smooth periodic input gives a smooth periodic corrector. Smoothness here
is stated on the real lift, so no manifold structure on the quotient circle
is hidden in the statement. -/
theorem exists_smooth_covariance_corrector [FiniteDimensional ℝ E]
    {V : Period → E} (hV : Continuous V) {v : E} (hv : average V = v)
    {r : Period → ℝ} (hr : Continuous r) (hr0 : average r = 0)
    (hVsmooth : ContDiff ℝ ∞ (fun t : ℝ => V (t : Period)))
    (hrsmooth : ContDiff ℝ ∞ (fun t : ℝ => r (t : Period)))
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) :
    ∃ W : Period → E, Continuous W ∧
      ContDiff ℝ ∞ (fun t : ℝ => W (t : Period)) ∧ average W = 0 ∧
      fluctuation (fun t => inner ℝ (V t) (W t)) = r := by
  obtain ⟨m, hm⟩ := meanOperator_surjective hV hv hq hcircle
    (average (fun t => r t • V t))
  have hh : Continuous (correctedScalar V v q r m) :=
    hr.add (((hV.sub continuous_const).inner continuous_const).div_const q)
  refine ⟨correctedVector V v q r m,
    continuous_const.smul ((hh.smul hV).sub continuous_const), ?_,
    average_correctedVector hV hv hr q m hm,
    corrected_projection V v hr hr0 hq.ne' hcircle m⟩
  have hs : ContDiff ℝ ∞ (fun t : ℝ => correctedScalar V v q r m (t : Period)) :=
    hrsmooth.add (((hVsmooth.sub contDiff_const).inner ℝ contDiff_const).div_const q)
  exact contDiff_const.smul ((hs.smul hVsmooth).sub contDiff_const)

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
