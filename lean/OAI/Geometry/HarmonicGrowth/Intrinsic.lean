import OAI.Geometry.HarmonicGrowth.PolarGeometry

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample

/-- The exact coordinate quadratic form used by path length. -/
def quadratic {n : ℕ} (g : SmoothMetric n) (x v : Space n) : ℝ :=
  ∑ i, ∑ j, g.coeff x i j * v i * v j

def speed {n : ℕ} (g : SmoothMetric n) (γ : ℝ → Space n) (t : ℝ) : ℝ :=
  Real.sqrt (quadratic g (γ t) (deriv γ t))

lemma speed_continuous {n : ℕ} (g : SmoothMetric n) {γ : ℝ → Space n}
    (hγ : ContDiff ℝ 1 γ) : Continuous (speed g γ) := by
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((g.smooth i j).continuous.comp hγ.continuous).mul
    ((continuous_apply i).comp hγ.continuous_deriv_one)).mul
      ((continuous_apply j).comp hγ.continuous_deriv_one)

lemma pathLength_nonneg {n : ℕ} (g : SmoothMetric n) (γ : ℝ → Space n) :
    0 ≤ pathLength g γ := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t _
  exact Real.sqrt_nonneg _

lemma pathLength_bddBelow {n : ℕ} (g : SmoothMetric n) (x y : Space n) :
    BddBelow {L : ℝ | ∃ γ : ℝ → Space n,
      ContDiff ℝ 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧ L = pathLength g γ} := by
  refine ⟨0, ?_⟩
  rintro L ⟨γ, _, _, _, rfl⟩
  exact pathLength_nonneg g γ

lemma line_smooth {n : ℕ} (x y : Space n) :
    ContDiff ℝ 1 (fun t : ℝ => x + t • (y-x)) := by fun_prop

lemma line_deriv {n : ℕ} (x y : Space n) (t : ℝ) :
    deriv (fun t : ℝ => x + t • (y-x)) t = y-x := by
  have h := ((hasDerivAt_id t).smul_const (y-x)).const_add x
  simpa using h.deriv

lemma pathLength_set_nonempty {n : ℕ} (g : SmoothMetric n) (x y : Space n) :
    {L : ℝ | ∃ γ : ℝ → Space n,
      ContDiff ℝ 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧ L = pathLength g γ}.Nonempty := by
  refine ⟨_, (fun t : ℝ => x + t • (y-x)), line_smooth x y, ?_, ?_, rfl⟩ <;> simp

lemma distance_nonneg {n : ℕ} (g : SmoothMetric n) (x y : Space n) :
    0 ≤ distance g x y := by
  apply le_csInf (pathLength_set_nonempty g x y)
  rintro L ⟨γ, _, _, _, rfl⟩
  exact pathLength_nonneg g γ

/-- Lower length comparison is proved for every admitted path. -/
lemma norm_sub_le_length {n : ℕ} (g : SmoothMetric n) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x v, a^2 * ‖v‖^2 ≤ quadratic g x v)
    {γ : ℝ → Space n} (hγ : ContDiff ℝ 1 γ) :
    ‖γ 1 - γ 0‖ ≤ pathLength g γ / a := by
  have hspeed : ∀ t, ‖deriv γ t‖ ≤ speed g γ t / a := by
    intro t
    apply (le_div_iff₀ ha).2
    rw [mul_comm]
    apply (Real.le_sqrt (by positivity) (by nlinarith [hlower (γ t) (deriv γ t)])).2
    nlinarith [hlower (γ t) (deriv γ t)]
  have hi := norm_sub_le_integral_of_norm_deriv_le_of_le (a := (0:ℝ)) (b := 1)
    (by norm_num) hγ.continuous.continuousOn
    (hγ.differentiable (by norm_num)).differentiableOn
    (Filter.Eventually.of_forall (fun t _ => hspeed t))
    (((speed_continuous g hγ).div_const a).intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_div, pathLength, speed, quadratic] using hi

lemma lower_distance {n : ℕ} (g : SmoothMetric n) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x v, a^2 * ‖v‖^2 ≤ quadratic g x v) (x y : Space n) :
    a * ‖y-x‖ ≤ distance g x y := by
  apply le_csInf (pathLength_set_nonempty g x y)
  rintro L ⟨γ, hγ, h0, h1, rfl⟩
  have h := (le_div_iff₀ ha).1 (norm_sub_le_length g ha hlower hγ)
  simpa only [h0, h1, mul_comm] using h

/-- Upper length comparison uses the genuine straight Cartesian path. -/
lemma upper_distance {n : ℕ} (g : SmoothMetric n) {b : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ x v, quadratic g x v ≤ b^2 * ‖v‖^2) (x y : Space n) :
    distance g x y ≤ b * ‖y-x‖ := by
  let γ : ℝ → Space n := fun t => x + t • (y-x)
  have hγ : ContDiff ℝ 1 γ := line_smooth x y
  have hd : ∀ t, deriv γ t = y-x := line_deriv x y
  have hpath : distance g x y ≤ pathLength g γ := by
    apply csInf_le (pathLength_bddBelow g x y)
    exact ⟨γ, hγ, by simp [γ], by simp [γ], rfl⟩
  apply hpath.trans
  have hspeed : ∀ t, speed g γ t ≤ b * ‖y-x‖ := by
    intro t
    unfold speed
    rw [hd t]
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    nlinarith [hupper (γ t) (y-x)]
  have hi := intervalIntegral.integral_mono (μ := volume) (a := (0:ℝ)) (b := 1) (by norm_num)
    (speed_continuous g hγ |>.intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1) hspeed
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul, pathLength, speed, quadratic] using hi

/-- Uniform equivalence with the Cartesian norm gives genuine intrinsic
completeness, with the exact sequence definition in the frozen target. -/
theorem complete_of_uniform_bounds {n : ℕ} (g : SmoothMetric n)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x v, a^2 * ‖v‖^2 ≤ quadratic g x v)
    (hupper : ∀ x v, quadratic g x v ≤ b^2 * ‖v‖^2) : Complete g := by
  intro z hz
  have hc : CauchySeq z := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := hz (a*ε) (mul_pos ha hε)
    refine ⟨N, ?_⟩
    intro p hp q hq
    have h := (lower_distance g ha hlower (z p) (z q)).trans_lt (hN p hp q hq)
    have hh := (mul_lt_mul_iff_right₀ ha).1 h
    simpa only [dist_eq_norm, norm_sub_rev] using hh
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, ?_⟩
  intro ε hε
  have he := (Metric.tendsto_atTop.1 hx) (ε/b) (div_pos hε hb)
  obtain ⟨N, hN⟩ := he
  refine ⟨N, ?_⟩
  intro p hp
  have hu := upper_distance g hb.le hupper (z p) x
  have hn : ‖x-z p‖ < ε/b := by
    simpa only [dist_eq_norm, norm_sub_rev] using hN p hp
  apply hu.trans_lt
  simpa only [mul_comm] using (lt_div_iff₀ hb).1 hn

end HarmonicCounterexample

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample
open Matrix Cartesian

lemma quadratic_eq_dot {n : ℕ} (g : SmoothMetric n) (x v : Space n) :
    quadratic g x v = v ⬝ᵥ (g.coeff x *ᵥ v) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_nonneg {n : ℕ} (g : SmoothMetric n) (x v : Space n) :
    0 ≤ quadratic g x v := by
  rw [quadratic_eq_dot]
  simpa only [star_trivial] using (g.positive x).posSemidef.dotProduct_mulVec_nonneg v

/-- Positivity and the exact radial eigenvector give the angular-gradient
bound. This is a quadratic-form Cauchy-Schwarz argument, not geodesic lore. -/
lemma radial_gram_bound {n : ℕ} (g : SmoothMetric n)
    (hrad : ∀ x, g.coeff x *ᵥ x = x) (x v : Space n) :
    (x ⬝ᵥ v)^2 ≤ squareRadius x * quadratic g x v := by
  by_cases hx : x = 0
  · simp [hx]
  have hs := squareRadius_pos hx
  have hsym : (g.coeff x)ᵀ = g.coeff x :=
    (Matrix.isHermitian_iff_isSymm.1 (g.positive x).isHermitian)
  have hcross : x ⬝ᵥ (g.coeff x *ᵥ v) = x ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, hrad]
  have hvx : v ⬝ᵥ x = x ⬝ᵥ v := dotProduct_comm _ _
  have hp := (g.positive x).posSemidef.dotProduct_mulVec_nonneg
    (v - ((x ⬝ᵥ v) / squareRadius x) • x)
  simp only [star_trivial, Matrix.mulVec_sub, Matrix.mulVec_smul,
    sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
    hrad x, hcross, hvx, smul_eq_mul] at hp
  change 0 ≤ v ⬝ᵥ (g.coeff x *ᵥ v) - (x ⬝ᵥ v / squareRadius x) * (x ⬝ᵥ v) -
    (x ⬝ᵥ v / squareRadius x) * (x ⬝ᵥ v -
      (x ⬝ᵥ v / squareRadius x) * squareRadius x) at hp
  rw [div_mul_cancel₀ _ hs.ne', sub_self, mul_zero, sub_zero] at hp
  rw [quadratic_eq_dot]
  have h := (mul_nonneg_iff_of_pos_right hs).2 hp
  field_simp at h
  nlinarith

lemma squareRadius_hasDerivAt {n : ℕ} {γ : ℝ → Space n} {γ' : Space n} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => squareRadius (γ s)) (2 * (γ t ⬝ᵥ γ')) t := by
  have hi i := hasDerivAt_pi.1 hγ i
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hi i).fun_mul (hi i))
  have he : 2 * (γ t ⬝ᵥ γ') = ∑ i, (γ' i * γ t i + γ t i * γ' i) := by
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact h

/-- Radius regularization removes the nondifferentiability at EVERY crossing
of the origin, so the lower distance estimate applies to all admitted paths. -/
lemma regularized_radius_length {n : ℕ} (g : SmoothMetric n)
    (hrad : ∀ x, g.coeff x *ᵥ x = x) {γ : ℝ → Space n}
    (hγ : ContDiff ℝ 1 γ) {ε : ℝ} (hε : 0 < ε) :
    |Real.sqrt (squareRadius (γ 1)+ε) - Real.sqrt (squareRadius (γ 0)+ε)| ≤
      pathLength g γ := by
  let f : ℝ → ℝ := fun t => Real.sqrt (squareRadius (γ t)+ε)
  have hp t : 0 < squareRadius (γ t) + ε := by linarith [squareRadius_nonneg (γ t)]
  have hd t : HasDerivAt f
      ((γ t ⬝ᵥ deriv γ t) / Real.sqrt (squareRadius (γ t)+ε)) t := by
    have h := ((squareRadius_hasDerivAt
      ((hγ.differentiable (by norm_num)) t).hasDerivAt).add_const ε).sqrt (hp t).ne'
    convert h using 1
    ring
  have hf : Continuous f := by
    exact Real.continuous_sqrt.comp ((squareRadius_smooth.continuous.comp hγ.continuous).add
      continuous_const)
  have hspeed t : ‖deriv f t‖ ≤ speed g γ t := by
    rw [(hd t).deriv, Real.norm_eq_abs]
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs, div_pow, Real.sq_sqrt (hp t).le]
    apply (div_le_iff₀ (hp t)).2
    have h := radial_gram_bound g hrad (γ t) (deriv γ t)
    have hq := quadratic_nonneg g (γ t) (deriv γ t)
    nlinarith
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le (a := (0:ℝ)) (b := 1)
    (by norm_num) hf.continuousOn (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall (fun t _ => hspeed t))
    ((speed_continuous g hγ).intervalIntegrable 0 1)
  simpa only [f, Real.norm_eq_abs, speed, quadratic, pathLength] using h

lemma radial_length_lower {n : ℕ} (g : SmoothMetric n)
    (hrad : ∀ x, g.coeff x *ᵥ x = x) {γ : ℝ → Space n}
    (hγ : ContDiff ℝ 1 γ) :
    |radius (γ 1)-radius (γ 0)| ≤ pathLength g γ := by
  have ht : Tendsto (fun ε : ℝ =>
      |Real.sqrt (squareRadius (γ 1)+ε) - Real.sqrt (squareRadius (γ 0)+ε)|)
      (𝓝[>] 0) (𝓝 |radius (γ 1)-radius (γ 0)|) := by
    have hc : Continuous (fun ε : ℝ =>
      |Real.sqrt (squareRadius (γ 1)+ε) - Real.sqrt (squareRadius (γ 0)+ε)|) := by
      fun_prop
    simpa only [add_zero, radius] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact regularized_radius_length g hrad hγ hε

lemma radius_le_distance {n : ℕ} (g : SmoothMetric n)
    (hrad : ∀ x, g.coeff x *ᵥ x = x) (x : Space n) :
    radius x ≤ distance g 0 x := by
  apply le_csInf (pathLength_set_nonempty g 0 x)
  rintro L ⟨γ, hγ, h0, h1, rfl⟩
  have h := radial_length_lower g hrad hγ
  simpa only [h0, h1, radius_zero, sub_zero, abs_of_nonneg (radius_nonneg x)] using h

lemma radial_line_length {n : ℕ} (g : SmoothMetric n)
    (hrad : ∀ x, g.coeff x *ᵥ x = x) (hzero : g.coeff 0 = 1) (x : Space n) :
    pathLength g (fun t : ℝ => t • x) = radius x := by
  have hd t : deriv (fun t : ℝ => t • x) t = x := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const x).deriv
  have he (t : ℝ) : quadratic g (t • x) x = squareRadius x := by
    rw [quadratic_eq_dot]
    by_cases ht : t = 0
    · simp [ht, hzero, squareRadius]
    · have h := hrad (t • x)
      rw [Matrix.mulVec_smul] at h
      have hm : g.coeff (t • x) *ᵥ x = x := (smul_right_injective _ ht) h
      rw [hm]
      rfl
  unfold pathLength
  change (∫ t in (0:ℝ)..1, Real.sqrt (quadratic g (t • x)
      (deriv (fun t : ℝ => t • x) t))) = radius x
  simp [hd, he, radius]

/-- Exact intrinsic radial distance for the smooth polar extension. -/
theorem distance_origin_eq_radius {n : ℕ} (g : SmoothMetric n)
    (hrad : ∀ x, g.coeff x *ᵥ x = x) (hzero : g.coeff 0 = 1) (x : Space n) :
    distance g 0 x = radius x := by
  apply le_antisymm _ (radius_le_distance g hrad x)
  rw [← radial_line_length g hrad hzero x]
  apply csInf_le (pathLength_bddBelow g 0 x)
  refine ⟨(fun t : ℝ => t • x), by fun_prop, by simp, by simp, rfl⟩

end HarmonicCounterexample

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample
open Cartesian MeasureTheory.Measure
open scoped Pointwise

lemma radius_smul {n : ℕ} (c : ℝ) (x : Space n) : radius (c • x) = |c| * radius x := by
  have hs : squareRadius (c • x) = c^2 * squareRadius x := by
    simp only [squareRadius, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [radius, hs, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rfl

def radialBall (n : ℕ) (R : ℝ) : Set (Space n) := {x | radius x < R}

lemma radialBall_measurable (n : ℕ) (R : ℝ) : MeasurableSet (radialBall n R) :=
  (isOpen_lt radius_continuous continuous_const).measurableSet

lemma omega_eq_radialBall (n : ℕ) : omega n = volume (radialBall n 1) := by
  unfold omega
  congr 1
  ext x
  have hr := radius_sq x
  have hp := radius_nonneg x
  simp only [radialBall, Set.mem_ofPred_eq]
  simp only [squareRadius, dotProduct, ← pow_two] at hr
  constructor <;> intro h <;> nlinarith

lemma omega_pos (n : ℕ) : 0 < omega n := by
  rw [omega_eq_radialBall]
  exact (isOpen_lt radius_continuous continuous_const).measure_pos volume
    ⟨0, by simp⟩

lemma omega_ne_top (n : ℕ) : omega n ≠ (∞ : ℝ≥0∞) := by
  rw [omega_eq_radialBall]
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono (show radialBall n 1 ⊆ {x | radius x ≤ 1} from
    fun x h => (show radius x < 1 from h).le))
  exact (radius_sublevel_compact 1).measure_lt_top

lemma radialBall_scale {n : ℕ} {R : ℝ} (hR : 0 < R) :
    radialBall n R = R • radialBall n 1 := by
  rw [← Set.preimage_smul_inv₀ hR.ne']
  ext x
  simp only [Set.mem_preimage, radialBall, Set.mem_ofPred_eq, radius_smul,
    abs_inv, abs_of_pos hR]
  rw [inv_mul_lt_iff₀ hR, mul_one]

lemma radialBall_volume {n : ℕ} {R : ℝ} (hR : 0 < R) :
    volume (radialBall n R) = omega n * ENNReal.ofReal (R^n) := by
  rw [radialBall_scale hR, addHaar_smul_of_nonneg volume hR.le, ← omega_eq_radialBall]
  simp only [Space, Module.finrank_pi, Fintype.card_fin]
  exact mul_comm _ _

lemma lintegral_comp_smul {n : ℕ} {R : ℝ} (hR : 0 < R)
    (f : Space n → ℝ≥0∞) :
    (∫⁻ x, f (R • x) ∂volume) = (ENNReal.ofReal (R^n))⁻¹ * ∫⁻ x, f x ∂volume := by
  let e : Space n ≃ᵐ Space n := (Homeomorph.smul (isUnit_iff_ne_zero.2 hR.ne').unit).toMeasurableEquiv
  change (∫⁻ x, f (e x) ∂volume) = _
  rw [← lintegral_map_equiv f e]
  change (∫⁻ y, f y ∂Measure.map (fun x : Space n => R • x) volume) = _
  rw [map_addHaar_smul volume hR.ne', lintegral_smul_measure]
  congr 1
  simp only [Space, Module.finrank_pi, Fintype.card_fin]
  rw [abs_of_pos (inv_pos.2 (pow_pos hR _)), ENNReal.ofReal_inv_of_pos (pow_pos hR _)]

/-- Change of variables is carried out on the actual Cartesian volume,
not an assumed polar volume formula. -/
lemma radial_integral_scale {n : ℕ} {R : ℝ} (hR : 0 < R)
    (f : Space n → ℝ≥0∞) :
    (∫⁻ x in radialBall n R, f x ∂volume) = ENNReal.ofReal (R^n) *
      ∫⁻ x in radialBall n 1, f (R • x) ∂volume := by
  have h := lintegral_comp_smul hR ((radialBall n R).indicator f)
  have he : (fun x => (radialBall n R).indicator f (R • x)) =
      (radialBall n 1).indicator (fun x => f (R • x)) := by
    ext x
    have hm : R • x ∈ radialBall n R ↔ x ∈ radialBall n 1 := by
      simp only [radialBall, Set.mem_ofPred_eq, radius_smul, abs_of_pos hR]
      rw [mul_lt_iff_lt_one_right hR]
    by_cases hx : x ∈ radialBall n 1
    · rw [Set.indicator_of_mem (hm.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (mt hm.1 hx), Set.indicator_of_notMem hx]
  rw [he, lintegral_indicator (radialBall_measurable n 1),
    lintegral_indicator (radialBall_measurable n R)] at h
  rw [h, ← mul_assoc, ENNReal.mul_inv_cancel
    (ENNReal.ofReal_ne_zero_iff.2 (pow_pos hR _)) ENNReal.ofReal_ne_top, one_mul]

lemma radial_integral_ratio {n : ℕ} {R : ℝ} (hR : 0 < R)
    (f : Space n → ℝ≥0∞) :
    (∫⁻ x in radialBall n R, f x ∂volume) / (omega n * ENNReal.ofReal (R^n)) =
      (∫⁻ x in radialBall n 1, f (R • x) ∂volume) / omega n := by
  rw [radial_integral_scale hR, mul_comm (omega n), ENNReal.mul_div_mul_left _ _
    (ENNReal.ofReal_ne_zero_iff.2 (pow_pos hR _)) ENNReal.ofReal_ne_top]

end HarmonicCounterexample

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff

namespace HarmonicCounterexample
open Cartesian

/-- A change-of-variables dominated convergence proof of the actual Cartesian
volume-ratio limit. The only exceptional ray is the null singleton at the origin. -/
theorem radial_integral_ratio_limit {n : ℕ} (hn : 0 < n)
    {f : Space n → ℝ≥0∞} (hf : Measurable f) {C A : ℝ≥0∞}
    (hC : C ≠ (∞ : ℝ≥0∞)) (hbound : ∀ x, f x ≤ C)
    (hlim : ∀ x ≠ 0, Tendsto (fun R : ℝ => f (R • x)) atTop (𝓝 A)) :
    Tendsto (fun R : ℝ => (∫⁻ x in radialBall n R, f x ∂volume) /
      (omega n * ENNReal.ofReal (R^n))) atTop (𝓝 A) := by
  have : NeZero n := ⟨hn.ne'⟩
  have hnull : ∀ᵐ x : Space n ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (0 : Space n))
  have hi := tendsto_lintegral_filter_of_dominated_convergence
    (μ := volume.restrict (radialBall n 1)) (fun _ : Space n => C)
    (F := fun R : ℝ => fun x : Space n => f (R • x)) (f := fun _ => A)
    (Eventually.of_forall fun R => hf.comp (continuous_const_smul R).measurable)
    (Eventually.of_forall fun R => Eventually.of_forall fun x => hbound (R • x))
    (by simpa only [lintegral_const, Measure.restrict_apply_univ,
      ← omega_eq_radialBall] using ENNReal.mul_ne_top hC (omega_ne_top n))
    ((ae_restrict_of_ae hnull).mono fun x hx => hlim x hx)
  simp only [lintegral_const, Measure.restrict_apply_univ, ← omega_eq_radialBall] at hi
  have hd := (ENNReal.continuous_div_const (omega n) (omega_pos n).ne').tendsto
    (A * omega n) |>.comp hi
  rw [ENNReal.mul_div_cancel_right (omega_pos n).ne' (omega_ne_top n)] at hd
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  exact (radial_integral_ratio hR f).symm

/-- Radial profiles converging along logarithmic radius converge on every
nonzero dilated ray, with no assertion at the origin. -/
lemma profile_scaling_limit {n : ℕ} {a : ℝ → ℝ} {A : ℝ}
    (ha : Tendsto a atTop (𝓝 A)) {x : Space n} (hx : x ≠ 0) :
    Tendsto (fun R : ℝ => a (logRadius (R • x))) atTop (𝓝 A) := by
  have hr : Tendsto (fun R : ℝ => R * radius x) atTop atTop :=
    tendsto_id.atTop_mul_const (radius_pos hx)
  have hl := ha.comp (Real.tendsto_log_atTop.comp hr)
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  simp only [Function.comp_apply, logRadius_eq_log_radius, radius_smul, abs_of_pos hR]

/-- Abstract geometric interface for the exact metric volume definition. -/
theorem metric_avr_of_density {n : ℕ} (hn : 0 < n) (g : SmoothMetric n)
    (hd : ∀ x, distance g 0 x = radius x) {A C : ℝ}
    (hA : 0 < A) (hA1 : A < 1)
    (hC : ∀ x, Real.sqrt (g.coeff x).det ≤ C)
    (hlim : ∀ x ≠ 0, Tendsto
      (fun R : ℝ => Real.sqrt (g.coeff (R • x)).det) atTop (𝓝 A)) :
    PositiveSubunitAVR g := by
  refine ⟨A, hA, hA1, ?_⟩
  have hm : Measurable (fun x => ENNReal.ofReal (Real.sqrt (g.coeff x).det)) := by
    apply ENNReal.continuous_ofReal.measurable.comp
    apply Real.continuous_sqrt.measurable.comp
    exact (continuous_pi fun i => continuous_pi fun j =>
      (g.smooth i j).continuous).matrix_det.measurable
  have hv := radial_integral_ratio_limit hn hm ENNReal.ofReal_ne_top
    (fun x => ENNReal.ofReal_le_ofReal (hC x)) (fun x hx => ENNReal.tendsto_ofReal (hlim x hx))
  simpa only [ballVolume, hd, radialBall] using hv

end HarmonicCounterexample

end

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Berger
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma det_one_add_rank_one (u v : ι → ℝ) :
    (1 + vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  have h : replicateCol Unit u * replicateRow Unit v = vecMulVec u v := by
    ext i j
    simp [Matrix.mul_apply, replicateCol, replicateRow, vecMulVec]
  rw [← h]
  exact det_one_add_replicateCol_mul_replicateRow u v

lemma det_one_add_scalar_projector {u : ι → ℝ} (hu : u ⬝ᵥ u = 1) (b : ℝ) :
    (1 + b • vecMulVec u u).det = 1 + b := by
  have h : b • vecMulVec u u = vecMulVec (b • u) u := by
    ext i j
    simp [vecMulVec, mul_assoc]
  rw [h, det_one_add_rank_one, dotProduct_smul, hu, smul_eq_mul, mul_one]

lemma tensor_factorization {u v : ι → ℝ} (huv : u ⬝ᵥ v = 0)
    {c : ℝ} (hc : c ≠ 0) (q : ℝ) :
    tensor u v c q = c • ((1 + (c⁻¹-1) • vecMulVec u u) *
      (1 + (q-1) • vecMulVec v v)) := by
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, huv]
  simp only [zero_smul, vecMulVec_zero, smul_zero, add_zero]
  ext i j
  simp only [tensor, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Exact volume density before the volume-normalizing choice c=a²q^(-1/m).
No orientation choice appears in the determinant. -/
theorem tensor_det {u v : ι → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    {c : ℝ} (hc : c ≠ 0) (q : ℝ) :
    (tensor u v c q).det = c ^ Fintype.card ι * c⁻¹ * q := by
  rw [tensor_factorization huv hc q, det_smul, det_mul,
    det_one_add_scalar_projector hu, det_one_add_scalar_projector hv]
  ring

/-- The source normalization keeps the angular volume unchanged by q. -/
def horizontalFactor (m : ℕ) (a q : ℝ) : ℝ := a^2 * q^((-1:ℝ)/(m:ℝ))

lemma horizontalFactor_pos (m : ℕ) {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    0 < horizontalFactor m a q :=
  mul_pos (sq_pos_of_pos ha) (Real.rpow_pos_of_pos hq _)

lemma horizontalFactor_normalization {m : ℕ} (hm : m ≠ 0)
    {a q : ℝ} (hq : 0 < q) :
    horizontalFactor m a q ^ m * q = a^(2*m) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [horizontalFactor, mul_pow, ← Real.rpow_mul_natCast hq.le]
  have he : (-1:ℝ)/(m:ℝ)*(m:ℝ) = -1 := div_mul_cancel₀ _ hm'
  rw [he, Real.rpow_neg_one, mul_assoc, inv_mul_cancel₀ hq.ne', mul_one, ← pow_mul]

/-- The determinant and square-root volume density in dimension m+1 are
exact, including every intermediate orientation and both signs of pulses. -/
theorem normalized_tensor_det {m : ℕ} (hm : m ≠ 0)
    {u v : Fin (m+1) → ℝ} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : u ⬝ᵥ v = 0) {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    (tensor u v (horizontalFactor m a q) q).det = a^(2*m) := by
  rw [tensor_det hu hv huv (horizontalFactor_pos m ha hq).ne', Fintype.card_fin,
    pow_succ, mul_assoc _ _ (horizontalFactor m a q)⁻¹,
    mul_inv_cancel₀ (horizontalFactor_pos m ha hq).ne', mul_one]
  exact horizontalFactor_normalization hm hq

lemma normalized_tensor_density {m : ℕ} (hm : m ≠ 0)
    {u v : Fin (m+1) → ℝ} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : u ⬝ᵥ v = 0) {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    Real.sqrt (tensor u v (horizontalFactor m a q) q).det = a^m := by
  rw [normalized_tensor_det hm hu hv huv ha hq, mul_comm 2 m, pow_mul,
    Real.sqrt_sq (pow_nonneg ha.le _)]

end HarmonicCounterexample.Berger

end

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Berger
lemma tensor_upper_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {u v : ι → ℝ}
    (hu : u ⬝ᵥ u=1) (hv : v ⬝ᵥ v=1) (huv : u ⬝ᵥ v=0)
    {c q H : ℝ} (h1 : 1≤H) (hc : c≤H) (hcq : c*q≤H) (w : ι → ℝ) :
    w ⬝ᵥ (tensor u v c q *ᵥ w) ≤ H*(w ⬝ᵥ w) := by
  rw [tensor_quadratic]
  have hb := two_vector_bessel hu hv huv w
  have h₁ := mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (u ⬝ᵥ w))
  have h₂ := mul_nonneg (sub_nonneg.2 hcq) (sq_nonneg (v ⬝ᵥ w))
  have h₃ := mul_nonneg (sub_nonneg.2 hc)
    (show 0 ≤ w ⬝ᵥ w-(u ⬝ᵥ w)^2-(v ⬝ᵥ w)^2 by linarith)
  nlinarith
end HarmonicCounterexample.Berger

end

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Construction
open Cartesian Berger
lemma scale_uniform_bounds {μ : ℝ} (hμ : 0≤μ) {q : ℝ → ℝ}
    (hq : ∀ t,q t ∈ Set.Icc (1/2:ℝ) 2) :
    ∃ L H : ℝ,0<L ∧ 0<H ∧ ∀ t,
      L≤horizontalScale μ q t ∧ horizontalScale μ q t≤H := by
  let L : ℝ := (Real.exp (-μ*Scale.total))^2*(2:ℝ)^(-1/15:ℝ)
  let H : ℝ := (1/2:ℝ)^(-1/15:ℝ)
  have hL : 0<L := mul_pos (sq_pos_of_pos (Real.exp_pos _)) (Real.rpow_pos_of_pos (by norm_num) _)
  have hH : 0<H := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨L,H,hL,hH,fun t => ⟨?_,?_⟩⟩
  · apply mul_le_mul
    · exact pow_le_pow_left₀ (Real.exp_pos _).le (Scale.profile_lower hμ t) 2
    · exact Real.rpow_le_rpow_of_nonpos (by linarith [(hq t).1]) (hq t).2 (by norm_num)
    · exact (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le
    · exact sq_nonneg _
  · calc
      horizontalScale μ q t ≤ 1*H := mul_le_mul
        (by nlinarith [Scale.profile_pos μ t,Scale.profile_le_one hμ t])
        (Real.rpow_le_rpow_of_nonpos (by norm_num) (hq t).1 (by norm_num))
        (Real.rpow_nonneg (by linarith [(hq t).1]) _) (by norm_num)
      _ = H := one_mul _
end HarmonicCounterexample.Construction

end

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ContDiff

namespace HarmonicCounterexample.Cartesian
open Berger
lemma squareRadius_le_norm {n : ℕ} (v : Space n) : squareRadius v ≤ n*‖v‖^2 := by
  calc
    squareRadius v = ∑ i : Fin n,(v i)^2 := by simp only [squareRadius,dotProduct,pow_two]
    _ ≤ ∑ i : Fin n,‖v‖^2 := Finset.sum_le_sum (fun i _ => by
      have hi : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v i)) (norm_nonneg v)).2 hi)
    _ = n*‖v‖^2 := by simp

lemma rawCoefficient_uniform_bounds {n : ℕ} (c q : ℝ → ℝ) (J : ℝ → ComplexStructure (Fin n))
    {L H : ℝ} (hL : 0<L) (hH : 0<H) (hc : ∀ t,L≤c t ∧ c t≤H)
    (hq : ∀ t,q t ∈ Set.Icc (1/2:ℝ) 2) :
    ∃ ell U : ℝ,0<ell ∧ 0<U ∧ ∀ x v : Space n,
      ell*‖v‖^2 ≤ v ⬝ᵥ (rawCoefficient c q J x *ᵥ v) ∧
      v ⬝ᵥ (rawCoefficient c q J x *ᵥ v) ≤ U*‖v‖^2 := by
  let ell := min 1 (L/2)
  let U := max 1 (2*H)
  have hell : 0<ell := lt_min (by norm_num) (by linarith)
  have hU : 0<U := lt_of_lt_of_le (by norm_num) (le_max_left 1 (2*H))
  refine ⟨ell,U*(n+1),hell,mul_pos hU (by positivity),fun x v => ?_⟩
  have hnorm : ‖v‖^2 ≤ squareRadius v := by
    have h := norm_le_radius v
    nlinarith [radius_sq v,radius_nonneg v,norm_nonneg v]
  have hpoint : ell*squareRadius v ≤ v ⬝ᵥ (rawCoefficient c q J x *ᵥ v) ∧
      v ⬝ᵥ (rawCoefficient c q J x *ᵥ v) ≤ U*squareRadius v := by
    by_cases hx : x=0
    · simp only [rawCoefficient,ite_eq_left hx,Matrix.one_mulVec]
      change ell*squareRadius v ≤ squareRadius v ∧ squareRadius v ≤ U*squareRadius v
      constructor
      · exact mul_le_of_le_one_left (squareRadius_nonneg v) (min_le_left _ _)
      · exact le_mul_of_one_le_left (squareRadius_nonneg v) (le_max_left _ _)
    · rw [rawCoefficient,ite_eq_right hx]
      have hcp : 0≤c (logRadius x) := hL.le.trans (hc _).1
      constructor
      · apply tensor_lower_bound (radialUnit_unit hx) (hopfUnit_unit _ hx) (radial_hopf_orthogonal _ _) (min_le_left _ _)
        · exact (min_le_right _ _).trans (by linarith [(hc (logRadius x)).1])
        · exact (min_le_right _ _).trans (by nlinarith [(hc (logRadius x)).1,(hq (logRadius x)).1])
      · apply tensor_upper_bound (radialUnit_unit hx) (hopfUnit_unit _ hx) (radial_hopf_orthogonal _ _) (le_max_left _ _)
        · exact (hc _).2.trans ((by linarith : H≤2*H).trans (le_max_right _ _))
        · exact (mul_le_mul_of_nonneg_left (hq _).2 hcp).trans
            ((by linarith [(hc (logRadius x)).2] : c (logRadius x)*2≤2*H).trans (le_max_right _ _))
  refine ⟨(mul_le_mul_of_nonneg_left hnorm hell.le).trans hpoint.1,?_⟩
  calc
    _ ≤ U*squareRadius v := hpoint.2
    _ ≤ U*(n*‖v‖^2) := mul_le_mul_of_nonneg_left (squareRadius_le_norm v) hU.le
    _ ≤ U*(n+1)*‖v‖^2 := by nlinarith [sq_nonneg ‖v‖]
end HarmonicCounterexample.Cartesian

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter Set Cartesian Berger Schedule AngularStream
open scoped Topology ContDiff

lemma rawCoefficient_density {μ : ℝ} {q : ℝ → ℝ} (hqp : ∀ t,0<q t)
    (J : ℝ → ComplexStructure (Fin 16)) (x : Space 16) (hx : x≠0) :
    Real.sqrt (rawCoefficient (horizontalScale μ q) q J x).det=
      (Scale.profile μ (logRadius x))^15 := by
  rw [rawCoefficient,ite_eq_right hx]
  exact normalized_tensor_density (m:=15) (by norm_num) (radialUnit_unit hx)
    (hopfUnit_unit _ hx) (radial_hopf_orthogonal _ _) (Scale.profile_pos μ _) (hqp _)

/-- Completeness, exact radial distance and positive subunit AVR for the actual
Cartesian tensor, with no ellipticity or volume conclusion left as a hypothesis. -/
theorem profile_metric_global {μ : ℝ} (hμ : 0≤μ)
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (hqb : ∀ t,q t ∈ Icc (1/2:ℝ) 2)
    (J : ℝ → ComplexStructure (Fin 16))
    (hJ : ∀ t,(∀ᶠ u in 𝓝 t,J u=J t) ∨ (∀ᶠ u in 𝓝 t,q u=1))
    (hc0 : ∀ t≤0,horizontalScale μ q t=1) (hq0 : ∀ t≤0,q t=1)
    (ha : Tendsto (Scale.profile μ) atTop (𝓝 a)) :
    let hqp : ∀ t,0<q t := fun t => lt_of_lt_of_le (by norm_num) (hqb t).1
    let g := bergerMetric (horizontalScale μ q) q J (horizontalScale_smooth hq hqp μ)
      hq (horizontalScale_pos hqp μ) hqp hJ hc0 hq0
    Complete g ∧ EuclideanNearOrigin g ∧ PositiveSubunitAVR g ∧
      ∀ x,distance g 0 x=radius x := by
  dsimp only
  let hqp : ∀ t,0<q t := fun t => lt_of_lt_of_le (by norm_num) (hqb t).1
  let g := bergerMetric (horizontalScale μ q) q J (horizontalScale_smooth hq hqp μ)
      hq (horizontalScale_pos hqp μ) hqp hJ hc0 hq0
  have he : EuclideanNearOrigin g := bergerMetric_euclidean _ _ _ _ _ _ _ _ _ _
  have hd : ∀ x,distance g 0 x=radius x := distance_origin_eq_radius g
    (rawCoefficient_radial _ _ _) (by simp [g,bergerMetric,rawCoefficient])
  have hc : Complete g := by
    obtain ⟨L,H,hL,hH,hb⟩ := scale_uniform_bounds hμ hqb
    obtain ⟨ell,U,hell,hU,h⟩ := rawCoefficient_uniform_bounds _ q J hL hH hb hqb
    apply complete_of_uniform_bounds g (Real.sqrt_pos.2 hell) (Real.sqrt_pos.2 hU)
    · intro x v
      rw [Real.sq_sqrt hell.le,quadratic_eq_dot]
      exact (h x v).1
    · intro x v
      rw [Real.sq_sqrt hU.le,quadratic_eq_dot]
      exact (h x v).2
  refine ⟨hc,he,?_,hd⟩
  apply metric_avr_of_density (C:=1) (by norm_num : 0<16) g hd
    (pow_pos a_pos 15) (pow_lt_one₀ a_pos.le a_lt_one (by norm_num : 15≠0))
  · intro x
    by_cases hx : x=0
    · subst x;simp [g,bergerMetric,rawCoefficient]
    · change Real.sqrt (rawCoefficient (horizontalScale μ q) q J x).det ≤ (1:ℝ)
      rw [rawCoefficient_density hqp J x hx]
      exact pow_le_one₀ (Scale.profile_pos μ _).le (Scale.profile_le_one hμ _)
  · intro x hx
    apply ((profile_scaling_limit ha hx).pow 15).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    exact (rawCoefficient_density hqp J (R • x) (smul_ne_zero hR.ne' hx)).symm

end HarmonicCounterexample.Construction

end

end OAI
