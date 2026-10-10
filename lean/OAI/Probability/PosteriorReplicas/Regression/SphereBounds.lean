import OAI.Probability.PosteriorReplicas.Regression.SupportVolume

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unitBallLaw : Measure E :=
  ((volume : Measure E) (Metric.ball 0 1))⁻¹ • volume.restrict (Metric.closedBall 0 1)

def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

lemma unitBallLaw_closedBall (z : E) {r : ℝ} (hr : 0 < r) :
    unitBallLaw (Metric.closedBall z r) ≤ ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  have h0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have ht : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  calc
    _ ≤ ((volume : Measure E) (Metric.ball 0 1))⁻¹ * volume (Metric.closedBall z r) := by
      exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    _ = _ := by
      rw [Measure.addHaar_closedBall _ _ hr.le, mul_comm _ (_ * _), mul_assoc,
        ENNReal.mul_inv_cancel h0 ht, mul_one]

lemma unitBallLaw_local : HasLocalMassBound (unitBallLaw : Measure E)
    (Module.finrank ℝ E : ℝ) := by
  intro z _ r hr
  simpa only [Real.rpow_natCast] using unitBallLaw_closedBall z hr

lemma unitBallLaw_support : (unitBallLaw : Measure E).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, unitBallLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]
  simp

instance unitBallLaw_probability : IsProbabilityMeasure (unitBallLaw : Measure E) := by
  constructor
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw (E := E)) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

lemma sphereLaw_apply [Nontrivial E] {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hdt : (Module.finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hsub : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s) ⊆ Metric.closedBall (0 : E) 1 := by
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      (mem_sphere_zero_iff_norm.mp x.property), mul_one, Real.norm_eq_abs,
      abs_of_pos hr.1]
    exact hr.2.le
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ hs, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), unitBallLaw, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Set.inter_eq_left.mpr hsub]
  calc
    _ = ((volume : Measure E) (Metric.ball 0 1))⁻¹ *
      (((Module.finrank ℝ E : ℝ≥0∞))⁻¹ * (Module.finrank ℝ E)) *
      volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hd0 hdt, mul_one]

lemma sphereLaw_cap_raw [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) :
    sphereLaw {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) := by
  classical
  let L := (Submodule.span ℝ ({z} : Set E)).toAffineSubspace
  let : Nonempty L := ⟨⟨0, (Submodule.span ℝ ({z} : Set E)).zero_mem⟩⟩
  have hl : Module.finrank ℝ L.direction ≤ 1 := by
    dsimp only [L]
    rw [Submodule.toAffineSubspace_direction]
    simpa using (finrank_span_le_card (R := ℝ) ({z} : Set E))
  have hm : (Module.finrank ℝ L.direction : ℝ) + (Module.finrank ℝ E - 1 : ℕ) ≤
      (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (by omega : Module.finrank ℝ L.direction + (Module.finrank ℝ E - 1) ≤ Module.finrank ℝ E)
  have hsub : Set.Ioo (0 : ℝ) 1 •
      (Subtype.val '' {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r}) ⊆
      {t | Metric.infDist t L ≤ r} := by
    rintro _ ⟨c, hc, _, ⟨s, hs, rfl⟩, rfl⟩
    have hz : c • z ∈ L := Submodule.smul_mem _ c (Submodule.subset_span (by simp))
    exact (Metric.infDist_le_dist_of_mem hz).trans (by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc.1]
      exact (mul_le_mul_of_nonneg_left hs hc.1.le).trans (mul_le_of_le_one_left hr.le hc.2.le))
  rw [sphereLaw_apply (measurableSet_le (by fun_prop) measurable_const)]
  apply (measure_mono hsub).trans
  apply (unitBallLaw_local.affine_tube_pow unitBallLaw_support L _ hm hr hr1).trans
  simp only [Real.rpow_natCast]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hl)
    (by positivity)

end SphereBounds

open scoped Pointwise

end PosteriorRegression
end

end OAI
