import OAI.Analysis.HenonEmden.UniformBounds

namespace OAI

section Energy
open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
namespace HenonLaneEmden

noncomputable def energyDensity {n : ℕ} (u : Space n → ℝ) (q B : ℝ) (x : Space n) : ℝ :=
  ‖x‖^B*(u x)^(q+1)

lemma measurable_energyDensity {n : ℕ} {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    Measurable (energyDensity u q B) := by
  unfold energyDensity
  exact (measurable_norm.pow_const B).mul (hu.measurable.pow_const (q+1))

lemma energyDensity_nonneg {n : ℕ} {u : Space n → ℝ} (hu : ∀ x, 0 ≤ u x)
    (q B : ℝ) (x : Space n) : 0 ≤ energyDensity u q B x :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (hu _) _)

lemma energyDensity_dilation {n : ℕ} {u : Space n → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ∀ x, 0 ≤ u x) (a q B : ℝ) (x : Space n) :
    energyDensity (dilation u a R) q B x =
      R^(a*(q+1)-B)*energyDensity u q B (R • x) := by
  unfold energyDensity dilation
  rw [Real.mul_rpow (Real.rpow_nonneg hR.le _) (hu _), ← Real.rpow_mul hR.le,
    norm_smul, Real.norm_eq_abs, abs_of_pos hR, Real.mul_rpow hR.le (norm_nonneg x),
    Real.rpow_sub hR]
  have hpower : R^B ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR B)
  field_simp

lemma lintegral_ball_comp_dilation {n : ℕ} {F : Space n → ℝ≥0∞} (hF : Measurable F)
    {R : ℝ} (hR : 0 < R) :
    (∫⁻ x in ball (0 : Space n) 1, F (R • x)) =
      ENNReal.ofReal (R^(-(n:ℝ))) * ∫⁻ y in ball (0 : Space n) R, F y := by
  have hpre : (fun x : Space n => R • x) ⁻¹' ball 0 R = ball 0 1 := by
    ext x
    simp only [mem_preimage, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    simpa only [mul_one] using (mul_lt_mul_iff_right₀ hR : R*‖x‖ < R*1 ↔ ‖x‖ < 1)
  have hmap := setLIntegral_map (μ := (volume : Measure (Space n)))
    (isOpen_ball (x := (0 : Space n)) (ε := R)).measurableSet hF
    (continuous_id.const_smul R).measurable
  change (∫⁻ y in ball (0 : Space n) R, F y ∂Measure.map (fun x : Space n => R • x) volume) =
    (∫⁻ x in (fun x : Space n => R • x) ⁻¹' ball 0 R, F (R • x)) at hmap
  rw [hpre, Measure.map_addHaar_smul volume (ne_of_gt hR), Measure.restrict_smul,
    lintegral_smul_measure] at hmap
  rw [← hmap]
  congr 2
  rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hR n)),
    Real.rpow_neg hR.le, Real.rpow_natCast]

lemma lintegral_energy_dilation {n : ℕ} {u : Space n → ℝ} (hu : Continuous u)
    (hupos : ∀ x, 0 ≤ u x) {R : ℝ} (hR : 0 < R) (a q B : ℝ) :
    (∫⁻ x in ball (0 : Space n) 1, ENNReal.ofReal (energyDensity (dilation u a R) q B x)) =
      ENNReal.ofReal (R^(a*(q+1)-B-(n:ℝ))) *
        ∫⁻ y in ball (0 : Space n) R, ENNReal.ofReal (energyDensity u q B y) := by
  simp_rw [energyDensity_dilation hR hupos a q B,
    ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
  rw [lintegral_const_mul _ (show Measurable (fun x : Space n =>
    ENNReal.ofReal (energyDensity u q B (R • x))) from
      ((measurable_energyDensity hu q B).comp (continuous_id.const_smul R).measurable).ennreal_ofReal),
    lintegral_ball_comp_dilation (measurable_energyDensity hu q B).ennreal_ofReal hR,
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
    ← Real.rpow_add hR]
  rfl

lemma energy_exponents {p q A B : ℝ} (hpq : 1 < p*q) :
    alpha p q A B*(q+1)-B = alpha p q A B+beta p q A B+2 ∧
    beta p q A B*(p+1)-A = alpha p q A B+beta p q A B+2 := by
  have hr := scaling_relations (A := A) (B := B) hpq
  constructor <;> nlinarith [hr.1,hr.2]

lemma energyDensity_eq_source_mul {n : ℕ} {u : Space n → ℝ}
    (hu : ∀ x, 0 < u x) (q B : ℝ) {x : Space n} (hx : x ≠ 0) :
    energyDensity u q B x = source u q B x * u x := by
  rw [energyDensity,source_off_zero _ _ _ hx,Real.rpow_add (hu x),Real.rpow_one,mul_assoc]

lemma IsSolution.energy_locallyIntegrable {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) :
    LocallyIntegrable (energyDensity u q B) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hi := (h.source_f_locallyIntegrable hn).mul_continuous h.continuous_u
  apply hi.congr
  filter_upwards [ae_iff.mpr (by simp : volume {x : Space n | ¬ x ≠ 0} = 0)] with x hx
  exact (energyDensity_eq_source_mul h.positive_u q B hx).symm

lemma IsSolution.energy_ball_pos {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) {R : ℝ} (hR : 0 < R) :
    0 < ∫⁻ x in ball (0:Space n) R, ENNReal.ofReal (energyDensity u q B x) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  apply (setLIntegral_pos_iff (measurable_energyDensity h.continuous_u q B).ennreal_ofReal).mpr
  have hs : ball (0:Space n) R \ {0} ⊆ Function.support (fun x => ENNReal.ofReal (energyDensity u q B x)) ∩ ball 0 R := by
    intro x hx
    refine ⟨?_,hx.1⟩
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx.2) _) (Real.rpow_pos_of_pos (h.positive_u x) _)
  apply lt_of_lt_of_le _ (measure_mono hs)
  rw [measure_sdiff_null (by simp)]
  exact Metric.measure_ball_pos volume _ hR

lemma IsSolution.energy_ball_finite {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (R : ℝ) :
    (∫⁻ x in ball (0:Space n) R, ENNReal.ofReal (energyDensity u q B x)) ≠ ⊤ := by
  exact (((h.energy_locallyIntegrable hn).integrableOn_isCompact (isCompact_closedBall _ R)).mono_set
    ball_subset_closedBall).lintegral_lt_top.ne

/-- The scaling obstruction.  With the strict hyperbola,
any putative solution has arbitrarily large unit-ball energy among its dilates. -/
lemma IsSolution.scaled_energy_unbounded {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hsub : Subcritical n p q A B) (C : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ ENNReal.ofReal C <
      ∫⁻ x in ball (0:Space n) 1,
        ENNReal.ofReal (energyDensity (dilation u (alpha p q A B) R) q B x) := by
  have hpq := h.product_gt_one hn hp hq
  let s := alpha p q A B+beta p q A B+2-(n:ℝ)
  have hs : 0 < s := subcritical_scaling_exponent hp hq hpq hsub
  let M := ∫⁻ x in ball (0:Space n) 1, ENNReal.ofReal (energyDensity u q B x)
  have hM : 0 < M.toReal := ENNReal.toReal_pos (ne_of_gt (h.energy_ball_pos hn (by norm_num)))
    (h.energy_ball_finite hn 1)
  have ht : Tendsto (fun R : ℝ => R^s*M.toReal) atTop atTop :=
    (tendsto_rpow_atTop hs).atTop_mul_const hM
  obtain ⟨R,hR,hRC⟩ := ((eventually_ge_atTop (1:ℝ)).and
    (ht.eventually (eventually_gt_atTop (max C 0)))).exists
  have hR0 : 0 < R := by linarith
  refine ⟨R,hR,?_⟩
  rw [lintegral_energy_dilation h.continuous_u (fun x => (h.positive_u x).le) hR0]
  have he : alpha p q A B*(q+1)-B-(n:ℝ) = s := by rw [(energy_exponents hpq).1]
  rw [he]
  have hm : M ≤ ∫⁻ x in ball (0:Space n) R, ENNReal.ofReal (energyDensity u q B x) :=
    lintegral_mono_set (ball_subset_ball hR)
  apply lt_of_lt_of_le _ (mul_le_mul_right hm (ENNReal.ofReal (R^s)))
  apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h.energy_ball_finite hn 1))).mp
  simpa only [ENNReal.toReal_ofReal',ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hR0.le _)] using hRC

end HenonLaneEmden
end Energy

end OAI
