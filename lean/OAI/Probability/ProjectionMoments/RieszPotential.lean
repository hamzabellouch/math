import OAI.Probability.ProjectionMoments.FrameMoments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_fixed_offset {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 ≤ K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m q : ℕ) (hq : 1 ≤ q) (hmargin : (q:ℝ)+m ≤ a)
    (ha : a ≤ Module.finrank ℝ E) (b : Label m) :
    (∫⁻ A : Fin m → E, (lowerDensity ν m (A,rowMap A z+b))^q
      ∂Measure.pi (fun _ => stdGaussian E))^(1/(q:ℝ)) ≤
      ENNReal.ofReal ((128:ℝ)^Module.finrank ℝ E * K * R^(a-m)) := by
  have hd : 1 ≤ Module.finrank ℝ E := by
    have hq' : 1 ≤ (q:ℝ) := by exact_mod_cast hq
    have hdd : (1:ℝ) ≤ Module.finrank ℝ E := by linarith [(show (0:ℝ) ≤ m from Nat.cast_nonneg m)]
    exact_mod_cast hdd
  have hm : m ≤ Module.finrank ℝ E := by
    exact_mod_cast (show (m:ℝ) ≤ Module.finrank ℝ E by linarith [(show (0:ℝ) ≤ q from Nat.cast_nonneg q)])
  rcases eq_or_lt_of_le hK with hK | hK
  · have hz := measure_eq_zero_of_allBall_zero (hK ▸ hν) z hR hs
    subst ν
    simp only [lowerDensity_zero,zero_pow (by omega : q ≠ 0),lintegral_zero]
    rw [ENNReal.zero_rpow_of_pos (by positivity : (0:ℝ) < 1/q)]
    exact bot_le
  · have hc : 1+ENNReal.ofReal ((3:ℝ)^Module.finrank ℝ E*(4:ℝ)^a)*(2:ℝ≥0∞)^(m+1) ≤
        (128:ℝ≥0∞)^Module.finrank ℝ E := by
      simpa only [NoiselessRegression.replicaConstant,Measure.dirac_apply_of_mem (Set.mem_univ (0:E))] using
        replicaConstant_real_le (ν := Measure.dirac (0:E)) (by simp) hd ha hm
    apply ennreal_root_bound (q := q) (by omega) (by positivity)
    have hh := lowerDensity_graph_moment_scaled hν hK z hR hs m q hmargin b
    apply hh.trans
    apply pow_le_pow_left'
    calc
      _ ≤ ENNReal.ofReal (K*R^(a-m))*(128:ℝ≥0∞)^Module.finrank ℝ E := mul_le_mul' le_rfl hc
      _ = _ := by
        rw [mul_comm]
        simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ (128:ℝ)^Module.finrank ℝ E),
          ENNReal.ofReal_mul hK.le,ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 128),
          ENNReal.ofReal_ofNat,mul_assoc]

lemma ambientSphereLaw_nullSingleton [Nontrivial E] (hd : 2 ≤ Module.finrank ℝ E) :
    NullSingletonClass (NoiselessRegression.ambientSphereLaw (E := E)) := by
  constructor
  intro z
  let C : ℝ := 3*4^Module.finrank ℝ E
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (C*r)) (𝓝 (0:ℝ)) (𝓝 0) := by
    have hc : Continuous (fun r : ℝ => ENNReal.ofReal (C*r)) := ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
    simpa only [mul_zero, ENNReal.ofReal_zero] using hc.tendsto (0:ℝ)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto (ht.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0:ℝ))] with r hr
  have hs : {z} ⊆ Metric.closedBall z r := Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self hr.le)
  apply (measure_mono hs).trans
  have hh := NoiselessRegression.ambientSphereLaw_closedBall (E := E) z hr 1 (by omega)
  simpa only [pow_one, ENNReal.ofReal_mul (show 0 ≤ C by positivity)] using hh

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop] lemma measurable_rieszKernel [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (α : ℝ) (z : E) : Measurable (rieszKernel α z) := by
  unfold rieszKernel
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rieszKernel_le_inverse_nat [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {α : ℝ} (hα : 0 ≤ α) {m : ℕ} (hm : α ≤ m)
    (z s : E) (hneq : s ≠ z) :
    rieszKernel α z s ≤ 1 + ENNReal.ofReal (‖s-z‖⁻¹^m) := by
  have hn : 0 < ‖s-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
  by_cases h1 : 1 ≤ ‖s-z‖
  · apply le_add_of_le_left
    simpa only [rieszKernel, ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_le
      (ENNReal.one_le_ofReal.mpr h1) (show -α ≤ 0 by linarith)
  · have hh := ENNReal.rpow_le_rpow_of_exponent_ge
      (show ENNReal.ofReal ‖s-z‖ ≤ 1 by exact ENNReal.ofReal_le_one.mpr (le_of_not_ge h1))
      (show -(m:ℝ) ≤ -α by linarith)
    have he : (ENNReal.ofReal ‖s-z‖)^(-(m:ℝ)) = ENNReal.ofReal (‖s-z‖⁻¹^m) := by
      rw [ENNReal.rpow_neg,ENNReal.rpow_natCast,ENNReal.ofReal_pow (inv_nonneg.mpr hn.le),
        ENNReal.ofReal_inv_of_pos hn,ENNReal.inv_pow]
    exact hh.trans (by rw [he]; exact le_add_left le_rfl)

lemma rieszPotential_finite [Nontrivial E] {α : ℝ} (hα : 0 ≤ α) {m : ℕ}
    (hm : α ≤ m) (hmd : m+1 ≤ Module.finrank ℝ E-1)
    {h : E → ℝ≥0∞} (h1 : ∀ s, h s ≤ 1) : rieszPotential α h < ∞ := by
  have hd : 2 ≤ Module.finrank ℝ E := by omega
  let := ambientSphereLaw_nullSingleton hd
  let C : ℝ≥0∞ := ENNReal.ofReal ((3:ℝ)*4^Module.finrank ℝ E)
  have hbound (z : E) : (∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) ≤
      2+C*(2:ℝ≥0∞)^(m+1) := by
    have hmom := NoiselessRegression.inverse_moment_of_tube_bound
      (NoiselessRegression.ambientSphereLaw (E := E)) (fun s => ‖s-z‖) m
      (by fun_prop) (fun _ => norm_nonneg _) C
      (fun r hr _ => by
        simpa only [Metric.closedBall, dist_eq_norm, C] using NoiselessRegression.ambientSphereLaw_closedBall z hr (m+1) hmd)
    have hcmp : ∀ᵐ s ∂NoiselessRegression.ambientSphereLaw,
        h s*rieszKernel α z s ≤ 1+ENNReal.ofReal (‖s-z‖⁻¹^m) := by
      filter_upwards [(NoiselessRegression.ambientSphereLaw (E := E)).ae_ne z] with s hs
      exact (mul_le_of_le_one_left' (h1 s)).trans (rieszKernel_le_inverse_nat hα hm z s hs)
    calc
      _ ≤ ∫⁻ s, 1+ENNReal.ofReal (‖s-z‖⁻¹^m) ∂NoiselessRegression.ambientSphereLaw := lintegral_mono_ae hcmp
      _ = 1+∫⁻ s, ENNReal.ofReal (‖s-z‖⁻¹^m) ∂NoiselessRegression.ambientSphereLaw := by
        rw [lintegral_add_left measurable_const]; simp
      _ ≤ 1+(1+C*2^(m+1)) := add_le_add le_rfl (by simpa only [measure_univ] using hmom)
      _ = _ := by ring
  exact (iSup_le hbound).trans_lt (by
    apply ENNReal.add_lt_top.mpr
    constructor
    · norm_num
    · exact ENNReal.mul_lt_top (show C < ∞ from ENNReal.ofReal_lt_top) (by finiteness))

lemma rieszPotential_ball_control [Nontrivial E] {α : ℝ} (hα : 0 ≤ α)
    {h : E → ℝ≥0∞} (hh : Measurable h) (z : E) {r : ℝ} (hr : 0 < r) :
    (NoiselessRegression.ambientSphereLaw.withDensity h) (Metric.closedBall z r) ≤
      rieszPotential α h * ENNReal.ofReal (r^α) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hrt : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hnorm (s : E) (hs : s ∈ Metric.closedBall z r) :
      1 ≤ ENNReal.ofReal (r^α) * rieszKernel α z s := by
    have hs' : ‖s-z‖ ≤ r := by simpa [dist_eq_norm] using hs
    have hb := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hs') hα
    rw [rieszKernel, ENNReal.rpow_neg, ← ENNReal.ofReal_rpow_of_pos hr]
    calc
      _ = (ENNReal.ofReal r)^α*((ENNReal.ofReal r)^α)⁻¹ :=
        (ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hr0) hrt)) (ENNReal.rpow_ne_top_of_nonneg hα hrt)).symm
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.inv_le_inv.mpr hb)
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  calc
    _ ≤ ∫⁻ s in Metric.closedBall z r, ENNReal.ofReal (r^α)*(h s*rieszKernel α z s)
        ∂NoiselessRegression.ambientSphereLaw := by
      apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
      intro s hs
      simpa only [mul_one,mul_left_comm] using mul_le_mul' le_rfl (hnorm s hs)
    _ ≤ ∫⁻ s, ENNReal.ofReal (r^α)*(h s*rieszKernel α z s)
        ∂NoiselessRegression.ambientSphereLaw := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (r^α)*(∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) :=
      lintegral_const_mul _ (hh.mul (measurable_rieszKernel α z))
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' (show _ ≤ rieszPotential α h from le_iSup (fun z => ∫⁻ s, h s*rieszKernel α z s ∂NoiselessRegression.ambientSphereLaw) z) le_rfl

end ProjectionMoments

end

end OAI
