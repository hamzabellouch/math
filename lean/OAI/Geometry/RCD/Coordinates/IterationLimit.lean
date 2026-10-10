import OAI.Geometry.RCD.Coordinates.MetricIteration
import OAI.Geometry.RCD.Coordinates.LimitChart

namespace OAI

/-!
# The metric iteration produces the limiting chart estimates

Finite-stage differential estimates imply geometric increment and Taylor
bounds. Pair geometry controls the original coordinates, the selected
scale, and the frozen metrics along each coordinate-value segment.
-/

open Filter Set
open scoped Topology ContDiff BigOperators

noncomputable section

namespace RegularPointCoordinates

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace AnalyticIterationData

theorem energy_le {Ω : Set E} {r0 T F B epsilon : ℝ}
    (d : AnalyticIterationData Ω r0 T F B epsilon) (i : ℕ) (x : E) (hx : x ∈ Ω) :
    d.energy i x ≤ epsilon := by
  exact (Finset.single_le_sum (fun j _ => d.energy_nonneg j x hx)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))).trans (d.energy_budget (i + 1) x hx)

/-- Increasing the permitted defect changes no maps or metrics. -/
def withLargerParameter {Ω : Set E} {r0 T F B epsilon delta : ℝ}
    (d : AnalyticIterationData Ω r0 T F B epsilon) (hr0 : 0 < r0)
    (hF : 0 ≤ F) (hB : 0 < B) (hed : epsilon ≤ delta) :
    AnalyticIterationData Ω r0 T F B delta where
  frozen := d.frozen
  correction := d.correction
  principal := d.principal
  mass := d.mass
  energy := d.energy
  frozen_mono := d.frozen_mono
  correction_smooth := d.correction_smooth
  energy_nonneg := d.energy_nonneg
  energy_budget := fun k x hx => (d.energy_budget k x hx).trans hed
  mass_nonneg := d.mass_nonneg
  principal_nonneg := d.principal_nonneg
  principal_le_mass := d.principal_le_mass
  mass_budget := d.mass_budget
  principal_budget := d.principal_budget
  value_bound := by
    intro i x hx
    have hr := iterationRadius_pos hr0 i
    exact (d.value_bound i x hx).trans (by gcongr)
  first_bound := by
    intro i x hx xi
    exact (d.first_bound i x hx xi).trans (by gcongr)
  second_bound := d.second_bound
  linear_bound := d.linear_bound
  correction_jets := by
    intro i x hx m
    exact (d.correction_jets i x hx m).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hed hF)
          (factorialMajorant_pos m).le) (jetCoefficientScale_pos hB m).le)

end AnalyticIterationData

/-- Only the second normalized jet is needed for the final pair estimate. -/
structure FiniteIterationControl {Ω : Set E} {r0 T F B epsilon : ℝ}
    (d : AnalyticIterationData Ω r0 T F B epsilon) : Prop where
  smooth : ∀ i x, x ∈ Ω → ∀ m : ℕ, ContDiffAt ℝ m (metricIterate d.correction i) x
  metric : ∀ i x, x ∈ Ω → ∀ xi,
    (4 * T)⁻¹ * ‖d.frozen i x xi‖ ^ 2 ≤ ‖fderiv ℝ (metricIterate d.correction i) x xi‖ ^ 2 ∧
    ‖fderiv ℝ (metricIterate d.correction i) x xi‖ ^ 2 ≤ (4 * T) * ‖d.frozen i x xi‖ ^ 2
  second_jet : ∀ i x, x ∈ Ω →
    ‖iteratedFDeriv ℝ 2 (normalizedCoordinates (iterationRadius r0 i)
      (d.frozen i x) x (metricIterate d.correction i)) 0‖ ≤ 8 * B

omit [CompleteSpace E] in
/-- Recover the actual second directional derivative from the normalized
second jet, without an ambient operator norm or condition-number loss. -/
theorem second_derivative_le_of_normalized_jet
    {h : E → E} {x : E} {r B : ℝ} (hr : 0 < r) (T : E ≃L[ℝ] E)
    (hh : ContDiffAt ℝ 2 h x)
    (hjet : ‖iteratedFDeriv ℝ 2 (normalizedCoordinates r T x h) 0‖ ≤ 8 * B)
    (xi : E) :
    ‖fderiv ℝ (fderiv ℝ h) x xi xi‖ ≤ 8 * B / r * ‖T xi‖ ^ 2 := by
  have ht := normalized_jet_apply T h x 0 r (by norm_num : 0 < (2 : ℕ))
    (by simpa using hh) (fun _ => T xi)
  have hfactor : r⁻¹ * r ^ 2 = r := by field_simp
  change iteratedFDeriv ℝ 2 (normalizedCoordinates r T x h) 0 (fun _ => T xi) = _ at ht
  simp only [map_zero, smul_zero, add_zero, ContinuousLinearEquiv.symm_apply_apply,
    hfactor, iteratedFDeriv_two_apply] at ht
  have hn : ‖iteratedFDeriv ℝ 2 (normalizedCoordinates r T x h) 0 (fun _ => T xi)‖ ≤
      8 * B * ‖T xi‖ ^ 2 := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ 2 (normalizedCoordinates r T x h) 0‖ * ‖T xi‖ ^ 2 := by
        simpa using (iteratedFDeriv ℝ 2 (normalizedCoordinates r T x h) 0).le_opNorm
          (fun _ => T xi)
      _ ≤ _ := mul_le_mul_of_nonneg_right hjet (sq_nonneg _)
  rw [iteratedFDeriv_two_apply, ht, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hn
  calc
    _ ≤ (8 * B * ‖T xi‖ ^ 2) / r := (le_div_iff₀ hr).mpr (by nlinarith)
    _ = _ := by ring

/-- The correction value and coercivity give a genuine geometric increment
bound for the recursively defined maps. -/
theorem metricIterate_step_le [FiniteDimensional ℝ E]
    {Ω : Set E} {r0 T F B epsilon : ℝ} (d : AnalyticIterationData Ω r0 T F B epsilon)
    (hT : 1 ≤ T) (hF : 0 ≤ F) (hepsilon : 0 ≤ epsilon) (hr0 : 0 < r0)
    (hc : FiniteIterationControl d) (i : ℕ) (x : E) (hx : x ∈ Ω) :
    dist (metricIterate d.correction i x) (metricIterate d.correction (i + 1) x) ≤
      (4 * T) * F * epsilon * iterationRadius r0 i := by
  have hA : 1 ≤ 4 * T := by linarith
  have hA0 : 0 ≤ 4 * T := by linarith
  obtain ⟨e, he, hinv⟩ := exists_equiv_inverseTranspose_bound
    (d.frozen i x) (fderiv ℝ (metricIterate d.correction i) x) hA
    (fun xi => (hc.metric i x hx xi).1)
  have hsqrt : Real.sqrt (4 * T) ≤ 4 * T := by
    nlinarith [Real.sq_sqrt hA0, Real.sqrt_nonneg (4 * T)]
  have henergy : Real.sqrt (d.energy i x) ≤ Real.sqrt epsilon :=
    Real.sqrt_le_sqrt (d.energy_le i x hx)
  have hr := iterationRadius_pos hr0 i
  rw [metricIterate_succ, dist_eq_norm]
  simp only [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  rw [← he, operatorInverseTranspose_equiv]
  calc
    _ ≤ Real.sqrt (4 * T) *
        ‖(d.frozen i x).symm.toContinuousLinearMap.adjoint (d.correction i x)‖ := hinv _
    _ ≤ Real.sqrt (4 * T) *
        (F * Real.sqrt epsilon * iterationRadius r0 i * Real.sqrt (d.energy i x)) :=
      mul_le_mul_of_nonneg_left (d.value_bound i x hx) (Real.sqrt_nonneg _)
    _ ≤ (4 * T) * (F * Real.sqrt epsilon * iterationRadius r0 i * Real.sqrt epsilon) := by
      gcongr
    _ = (4 * T) * F * (Real.sqrt epsilon * Real.sqrt epsilon) * iterationRadius r0 i := by ring
    _ = _ := by rw [Real.mul_self_sqrt hepsilon]

end Analytic

section Pairs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convenient non-sharp constant for converting metric squares to linear
separation.  It avoids introducing a square root into the final chart ratio. -/
theorem linear_comparison_of_frozen_metric
    (T : E ≃L[ℝ] E) (J : E →L[ℝ] E) {A G t : ℝ} (hA : 1 ≤ A) (hG : 1 ≤ G)
    (ht : 0 ≤ t) (w : E)
    (hmetric : ∀ xi, A⁻¹ * ‖T xi‖ ^ 2 ≤ ‖J xi‖ ^ 2 ∧
      ‖J xi‖ ^ 2 ≤ A * ‖T xi‖ ^ 2)
    (hlower : G⁻¹ * t ≤ ‖T w‖) (hupper : ‖T w‖ ≤ G * t) :
    (2 * (A * G))⁻¹ * t ≤ ‖J w‖ ∧ ‖J w‖ ≤ 2 * (A * G) * t := by
  have hA0 : 0 < A := by linarith
  have hG0 : 0 < G := by linarith
  have hsqrt : Real.sqrt A ≤ A := by
    nlinarith [Real.sq_sqrt hA0.le, Real.sqrt_nonneg A]
  have hlow := norm_le_sqrt_mul_of_metric_lower T J hA (fun xi => (hmetric xi).1) w
  have hlow' : ‖T w‖ ≤ A * ‖J w‖ :=
    hlow.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _))
  have hnorm : ‖J w‖ ≤ Real.sqrt A * ‖T w‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hA0.le] using (hmetric w).2
  have hnorm' : ‖J w‖ ≤ A * (G * t) := hnorm.trans
    ((mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hupper hA0.le))
  have ht' : t ≤ G * ‖T w‖ := by
    rw [← div_eq_inv_mul] at hlower
    exact (div_le_iff₀ hG0).mp hlower |>.trans_eq (mul_comm _ _)
  constructor
  · rw [← div_eq_inv_mul]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (A * G))).mpr
    have hh := ht'.trans (mul_le_mul_of_nonneg_left hlow' hG0.le)
    nlinarith [mul_nonneg hA0.le (mul_nonneg hG0.le (norm_nonneg (J w)))]
  · nlinarith [mul_nonneg hA0.le (mul_nonneg hG0.le ht)]

end Pairs

/-- The chart ratio and pair radius are fixed before the final smallness
parameter is chosen. -/
def iterationChartRatio (T G : ℝ) : ℝ := (4 * T) * G

def iterationPairMultiplier (T B G : ℝ) : ℝ :=
  64 * iterationChartRatio T G * B * G ^ 4

/-- A diameter restriction supplies the required dyadic pair scale. -/
theorem exists_iteration_pair_scale {r0 L t : ℝ} (hr0 : 0 < r0) (hL : 0 < L)
    (ht : 0 < t) (hdiam : L * t ≤ r0) :
    ∃ i, L * t ≤ iterationRadius r0 i ∧ iterationRadius r0 i ≤ 2 * L * t := by
  obtain ⟨i, hi, hi'⟩ := exists_dyadic_scale (div_pos (mul_pos hL ht) hr0)
    ((div_le_one hr0).mpr hdiam)
  have hri : iterationRadius r0 i = r0 * (1 / 2 : ℝ) ^ i := by
    unfold iterationRadius
    rw [one_div_pow]
    ring
  have hl := (div_le_iff₀ hr0).mp hi
  have hu' : (1 / 2 : ℝ) ^ i < (2 * L * t) / r0 := by convert hi' using 1; ring
  have hu := (lt_div_iff₀ hr0).mp hu'
  exact ⟨i, by rw [hri]; nlinarith, by rw [hri]; nlinarith⟩

/-- Raw geometric information about the original coordinates and frozen
metrics.  No derivative, increment, or Taylor estimate occurs here. -/
def IterationPairGeometry {X E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : X → E) (Ω : Set E) (frozen : ℕ → E → E ≃L[ℝ] E)
    (r0 T B G : ℝ) : Prop :=
  ∀ x z, x ≠ z → ∃ i,
    iterationPairMultiplier T B G * dist x z ≤ iterationRadius r0 i ∧
    iterationRadius r0 i ≤ 2 * iterationPairMultiplier T B G * dist x z ∧
    G⁻¹ * dist x z ≤ ‖frozen i (u x) (u z - u x)‖ ∧
    ‖frozen i (u x) (u z - u x)‖ ≤ G * dist x z ∧
    segment ℝ (u x) (u z) ⊆ Ω ∧
    ∀ y ∈ segment ℝ (u x) (u z),
      ‖frozen i y (u z - u x)‖ ≤ G * ‖frozen i (u x) (u z - u x)‖

/-- Uniform geometric estimates at comparable scales, together with a
diameter bound, construct the pair-selected data. -/
theorem iterationPairGeometry_of_all_scales {X E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : X → E) (Ω : Set E) (frozen : ℕ → E → E ≃L[ℝ] E)
    {r0 T B G : ℝ} (hr0 : 0 < r0) (hT : 1 ≤ T) (hB : 1 ≤ B) (hG : 1 ≤ G)
    (hdiam : ∀ x z : X, iterationPairMultiplier T B G * dist x z ≤ r0)
    (hgeometry : ∀ i x z, x ≠ z →
      iterationPairMultiplier T B G * dist x z ≤ iterationRadius r0 i →
      iterationRadius r0 i ≤ 2 * iterationPairMultiplier T B G * dist x z →
      G⁻¹ * dist x z ≤ ‖frozen i (u x) (u z - u x)‖ ∧
      ‖frozen i (u x) (u z - u x)‖ ≤ G * dist x z ∧
      segment ℝ (u x) (u z) ⊆ Ω ∧
      ∀ y ∈ segment ℝ (u x) (u z),
        ‖frozen i y (u z - u x)‖ ≤ G * ‖frozen i (u x) (u z - u x)‖) :
    IterationPairGeometry u Ω frozen r0 T B G := by
  intro x z hxz
  have hL : 0 < iterationPairMultiplier T B G := by
    unfold iterationPairMultiplier iterationChartRatio
    positivity
  obtain ⟨i, hi, hi'⟩ := exists_iteration_pair_scale hr0 hL (dist_pos.mpr hxz) (hdiam x z)
  exact ⟨i, hi, hi', hgeometry i x z hxz hi hi'⟩

section Limit

variable {X : Type*} [MetricSpace X] {n : ℕ}

/-- Analytic iteration bounds and pair geometry supply scale-selected Taylor
estimates for the limit. -/
theorem exists_limit_dist_bounds_of_analytic_iteration
    {Ω : Set (Euclidean n)} {r0 T F B G epsilon : ℝ}
    (d : AnalyticIterationData Ω r0 T F B epsilon)
    (hT : 1 ≤ T) (hF : 1 ≤ F) (hB : 1 ≤ B) (hG : 1 ≤ G)
    (hr0 : 0 < r0) (hepsilon : 0 ≤ epsilon) (hc : FiniteIterationControl d)
    (u : X → Euclidean n) (hu : ∀ x, u x ∈ Ω)
    (hgeometry : IterationPairGeometry u Ω d.frozen r0 T B G)
    (hsmall : 8 * (4 * T) * F * epsilon * iterationPairMultiplier T B G ≤
      (8 * iterationChartRatio T G)⁻¹) :
    ∃ H : X → Euclidean n,
      (∀ x, Tendsto (fun i => metricIterate d.correction i (u x)) atTop (𝓝 (H x))) ∧
      ∀ x z, (4 * iterationChartRatio T G)⁻¹ * dist x z ≤ dist (H x) (H z) ∧
        dist (H x) (H z) ≤ (4 * iterationChartRatio T G) * dist x z := by
  let q := iterationChartRatio T G
  let L := iterationPairMultiplier T B G
  let C := (4 * T) * F * epsilon * r0
  have hq : 1 ≤ q := by dsimp [q, iterationChartRatio]; nlinarith
  have hq0 : 0 < q := by linarith
  have hL : 0 < L := by dsimp [L, iterationPairMultiplier, iterationChartRatio]; positivity
  have hstep (i : ℕ) (x : X) :
      dist (metricIterate d.correction i (u x))
        (metricIterate d.correction (i + 1) (u x)) ≤ C * (1 / 2 : ℝ) ^ i := by
    have hi := metricIterate_step_le d hT (by linarith) hepsilon hr0 hc i (u x) (hu x)
    convert hi using 1
    dsimp [C, iterationRadius]
    rw [one_div_pow]
    ring
  apply exists_limit_dist_bounds_of_taylor u (metricIterate d.correction)
    (fun i => fderiv ℝ (metricIterate d.correction i))
    (fun i => fderiv ℝ (fderiv ℝ (metricIterate d.correction i))) hq hstep
  intro x z hxz
  obtain ⟨i, hscale, hscale', hlower, hupper, hsegment, hnear⟩ := hgeometry x z hxz
  let w := u z - u x
  let M := 8 * B / iterationRadius r0 i * G ^ 4 * (dist x z) ^ 2
  have hr := iterationRadius_pos hr0 i
  have hdist : 0 < dist x z := dist_pos.mpr hxz
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hlinear := linear_comparison_of_frozen_metric (d.frozen i (u x))
    (fderiv ℝ (metricIterate d.correction i) (u x)) (by linarith : 1 ≤ 4 * T)
    hG hdist.le w (hc.metric i (u x) (hu x)) hlower hupper
  refine ⟨i, M, hM, ?_, ?_, ?_, hlinear.1, hlinear.2, ?_, ?_⟩
  · intro y hy
    exact ((hc.smooth i y (hsegment hy) 1).differentiableAt (by norm_num)).hasFDerivAt
  · intro y hy
    exact (((hc.smooth i y (hsegment hy) 2).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  · intro y hy
    have hnorm : ‖d.frozen i y w‖ ≤ G ^ 2 * dist x z := by
      calc
        _ ≤ G * ‖d.frozen i (u x) w‖ := hnear y hy
        _ ≤ G * (G * dist x z) := mul_le_mul_of_nonneg_left hupper (by linarith)
        _ = _ := by ring
    calc
      _ ≤ 8 * B / iterationRadius r0 i * ‖d.frozen i y w‖ ^ 2 :=
        second_derivative_le_of_normalized_jet hr (d.frozen i y)
          (hc.smooth i y (hsegment hy) 2) (hc.second_jet i y (hsegment hy)) w
      _ ≤ 8 * B / iterationRadius r0 i * (G ^ 2 * dist x z) ^ 2 := by gcongr
      _ = M := by dsimp [M]; ring
  · have hcoeff : (8 * q)⁻¹ * L = 8 * B * G ^ 4 := by
      dsimp [L, iterationPairMultiplier]
      change (8 * q)⁻¹ * (64 * q * B * G ^ 4) = _
      field_simp
      ring
    change 8 * B / iterationRadius r0 i * G ^ 4 * dist x z ^ 2 ≤ (8 * q)⁻¹ * dist x z
    have heq : 8 * B / iterationRadius r0 i * G ^ 4 * dist x z ^ 2 =
        (8 * B * G ^ 4 * dist x z ^ 2) / iterationRadius r0 i := by ring
    rw [heq]
    apply (div_le_iff₀ hr).mpr
    calc
      _ = ((8 * q)⁻¹ * dist x z) * (L * dist x z) := by rw [← hcoeff]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)
  · have hrad : C * (1 / 2 : ℝ) ^ i = (4 * T) * F * epsilon * iterationRadius r0 i := by
      dsimp [C, iterationRadius]
      rw [one_div_pow]
      ring
    calc
      4 * C * (1 / 2 : ℝ) ^ i = 4 * (C * (1 / 2 : ℝ) ^ i) := by ring
      _ = 4 * ((4 * T) * F * epsilon * iterationRadius r0 i) := by rw [hrad]
      _ ≤ 4 * ((4 * T) * F * epsilon * (2 * L * dist x z)) := by
        gcongr
      _ = (8 * (4 * T) * F * epsilon * L) * dist x z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hdist.le

end Limit

section FinalChart

variable {X : Type*} [MetricSpace X] {n : ℕ}

/-- One small parameter controls the analytic iteration, Taylor errors, and
limiting tails; invariance of domain gives the open image. -/
theorem exists_analytic_iteration_limit_chart
    (hIOD : EuclideanInvarianceOfDomain n) {T F B G : ℝ}
    (hT : 1 ≤ T) (hF : 1 ≤ F) (hB : 1 ≤ B) (hG : 1 ≤ G) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ (p : X) (Ω : Set (Euclidean n)), IsOpen Ω →
      ∀ (U : Set X), IsOpen U → p ∈ U →
      ∀ (O : Set (Euclidean n)), IsOpen O → O ⊆ Ω → ∀ u : U ≃ₜ O,
      ∀ (r0 : ℝ), 0 < r0 → ∀ d : AnalyticIterationData Ω r0 T F B epsilon,
      IterationPairGeometry (fun x : U => (u x : Euclidean n)) Ω d.frozen r0 T B G →
      HasOpenBilipschitzChart n p := by
  obtain ⟨delta, hdelta, hdelta1, hcontrol⟩ :=
    exists_analytic_metric_iteration (E := Euclidean n) hT hF hB
  let q := iterationChartRatio T G
  let L := iterationPairMultiplier T B G
  have hq : 1 ≤ q := by dsimp [q, iterationChartRatio]; nlinarith
  have hq0 : 0 < q := by linarith
  have hA0 : 0 < 4 * T := by linarith
  have hF0 : 0 < F := by linarith
  have hL0 : 0 < L := by dsimp [L, iterationPairMultiplier, iterationChartRatio]; positivity
  let epsilon := min delta (64 * q * (4 * T) * F * L)⁻¹
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hed : epsilon ≤ delta := min_le_left _ _
  have hes : epsilon ≤ (64 * q * (4 * T) * F * L)⁻¹ := min_le_right _ _
  have hsmall : 8 * (4 * T) * F * epsilon * L ≤ (8 * q)⁻¹ := by
    calc
      _ ≤ 8 * (4 * T) * F * (64 * q * (4 * T) * F * L)⁻¹ * L := by gcongr
      _ = _ := by field_simp; ring
  refine ⟨epsilon, hepsilon, hed.trans hdelta1, ?_⟩
  intro p Ω hΩ U hU hp O hO hOΩ u r0 hr0 d hgeometry
  let d' := d.withLargerParameter hr0 (by linarith : 0 ≤ F) (by linarith : 0 < B) hed
  have hc : FiniteIterationControl d := by
    constructor
    · intro i x hx m
      exact (hcontrol Ω hΩ r0 hr0 d' i x hx).1 m
    · intro i x hx xi
      exact (hcontrol Ω hΩ r0 hr0 d' i x hx).2.1 xi
    · intro i x hx
      have hh := (hcontrol Ω hΩ r0 hr0 d' i x hx).2.2 2 (by norm_num)
      change ‖iteratedFDeriv ℝ 2 (normalizedCoordinates (iterationRadius r0 i)
        (d.frozen i x) x (metricIterate d.correction i)) 0‖ ≤
          B ^ (2 - 1) * ((2 : ℕ).factorial : ℝ) ^ 3 at hh
      norm_num at hh
      nlinarith
  obtain ⟨H, _, hbound⟩ := exists_limit_dist_bounds_of_analytic_iteration d hT hF hB hG
    hr0 hepsilon.le hc (fun x : U => (u x : Euclidean n)) (fun x => hOΩ (u x).property)
    hgeometry hsmall
  exact hasOpenBilipschitzChart_of_coordinates_and_bounds hIOD hU hp hO u
    (by change 1 ≤ 4 * q; linarith) hbound

end FinalChart

end RegularPointCoordinates

end

end OAI
