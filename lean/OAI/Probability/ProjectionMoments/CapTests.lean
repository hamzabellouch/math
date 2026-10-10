import OAI.Probability.ProjectionMoments.Caps

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cap_mass_inv_bound [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ ≤
      ENNReal.ofReal ((r^(Module.finrank ℝ E-1))⁻¹ * (16:ℝ)^Module.finrank ℝ E) := by
  let p := NoiselessRegression.ambientSphereLaw (Metric.closedBall c r)
  let a := ENNReal.ofReal (r^(Module.finrank ℝ E-1))
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have h := mul_le_mul' (le_rfl : a⁻¹ ≤ a⁻¹) (sphere_cap_lower hc hr hr2)
  change a⁻¹*a ≤ a⁻¹ * (ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) * p) at h
  rw [ENNReal.inv_mul_cancel ha0 hat, ← mul_assoc] at h
  have hh : p⁻¹ ≤ a⁻¹ * ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) := by
    apply (ENNReal.mul_le_mul_iff_right (cap_mass_pos hc hr hr2) (measure_ne_top _ _)).mp
    change p*p⁻¹ ≤ p*(a⁻¹ * ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E))
    rw [ENNReal.mul_inv_cancel (cap_mass_pos hc hr hr2) (measure_ne_top _ _)]
    simpa only [mul_comm] using h
  simpa only [a, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.le _)),
    ENNReal.ofReal_inv_of_pos (pow_pos hr _)] using hh

lemma cap_ratio_algebra (d n : ℕ) {r ρ α : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hα : 2*α = n) :
    (r^n)⁻¹ * (16:ℝ)^d * (3*4^d*ρ^n) * (r/ρ)^α =
      3*64^d*(ρ/r)^α := by
  have hre : r^n = (r^α)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hr.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith
  have hρe : ρ^n = (ρ^α)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hρ.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith
  rw [hre,hρe,Real.div_rpow hr.le hρ.le, Real.div_rpow hρ.le hr.le]
  have hc : (16:ℝ)^d * 4^d = 64^d := by rw [← mul_pow]; norm_num
  field_simp [(Real.rpow_pos_of_pos hr α).ne', (Real.rpow_pos_of_pos hρ α).ne']
  nlinarith [hc]

lemma cap_cost_ratio [Nontrivial E] {c c' : E} (hc : ‖c‖ = 1)
    {r ρ α : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hρ : 0 < ρ)
    (hα : 2*α = (Module.finrank ℝ E-1:ℕ)) :
    (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ *
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c' ρ) * ENNReal.ofReal ((r/ρ)^α) ≤
        ENNReal.ofReal (3*64^Module.finrank ℝ E*(ρ/r)^α) := by
  have hu := NoiselessRegression.ambientSphereLaw_closedBall c' hρ (Module.finrank ℝ E-1) le_rfl
  have h := mul_le_mul' (mul_le_mul' (cap_mass_inv_bound hc hr hr2) hu)
    (le_rfl : ENNReal.ofReal ((r/ρ)^α) ≤ _)
  rw [← ENNReal.ofReal_mul (by positivity)] at hu
  apply le_trans (mul_le_mul' (mul_le_mul' (cap_mass_inv_bound hc hr hr2) hu) le_rfl)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    cap_ratio_algebra _ _ hr hρ hα]

lemma cap_small_scale_constant (d : ℕ) (hd : 1 ≤ d) {α ρ r t : ℝ}
    (hα0 : 0 ≤ α) (hαd : α ≤ d) (hr : 0 < r) (ht : 0 < t)
    (hρ : 0 ≤ ρ) (hρt : ρ ≤ 8*r*t) :
    3*64^d*(ρ/r)^α ≤ (2048:ℝ)^d*t^α := by
  have hratio : ρ/r ≤ 8*t := (div_le_iff₀ hr).mpr (by nlinarith)
  have h8 : (8:ℝ)^α ≤ (8:ℝ)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
  have h3 : (3:ℝ) ≤ 3^d := by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hd
  calc
    _ ≤ 3*64^d*(8*t)^α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg hρ hr.le) hratio hα0) (by positivity)
    _ = 3*64^d*8^α*t^α := by rw [Real.mul_rpow (by norm_num) ht.le]; ring
    _ ≤ 3^d*64^d*8^d*t^α := by rw [Real.rpow_natCast] at h8; gcongr
    _ = (1536:ℝ)^d*t^α := by rw [← mul_pow, ← mul_pow]; norm_num
    _ ≤ _ := by gcongr; norm_num

lemma weighted_cap_set_le [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r b : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (h : E → ℝ≥0∞)
    (hb : ∫⁻ x, h x ∂capMeasure c r ≤ ENNReal.ofReal b) :
    (NoiselessRegression.ambientSphereLaw.withDensity h) (Metric.closedBall c r) ≤
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) * ENNReal.ofReal b := by
  rw [capMeasure, lintegral_smul_measure, smul_eq_mul] at hb
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  exact (ENNReal.inv_mul_le_iff (cap_mass_pos hc hr hr2) (measure_ne_top _ _)).mp hb

def capTestMeasure (h : E → ℝ≥0∞) (c : E) (r : ℝ) : Measure E :=
  ((capMeasure c r).withDensity h).map (rescale c r)

lemma capTestMeasure_mass {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    capTestMeasure h c r Set.univ ≤ 1 := by
  have hp := hdual D.parent
  rw [D.parent_center,D.parent_radius,div_self hr.ne',Real.one_rpow,ENNReal.ofReal_one] at hp
  simpa only [capTestMeasure,Measure.map_apply (measurable_rescale c r) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hp

lemma capTestMeasure_finite {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    IsFiniteMeasure (capTestMeasure h c r) :=
  ⟨(capTestMeasure_mass hr D hdual).trans_lt (by simp)⟩

lemma capTestMeasure_support (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r) :
    (capTestMeasure h c r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  apply (ae_map_iff (measurable_rescale c r).aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
  filter_upwards [((capMeasure c r).withDensity h).support_mem_ae] with x hx
  have hx' := capMeasure_support c r ((withDensity_absolutelyContinuous (capMeasure c r) h).support_mono hx)
  change x ∈ rescale c r ⁻¹' Metric.closedBall 0 1
  rw [rescale_preimage_closedBall c 0 hr, dilate, smul_zero, zero_add, mul_one]
  exact hx'

lemma capTestMeasure_ball (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r) (b : E) (t : ℝ) :
    capTestMeasure h c r (Metric.closedBall b t) =
      (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ *
        (NoiselessRegression.ambientSphereLaw.withDensity h)
          (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) := by
  rw [capTestMeasure, Measure.map_apply (measurable_rescale c r) Metric.isClosed_closedBall.measurableSet,
    rescale_preimage_closedBall c b hr, capMeasure, withDensity_smul_measure,
    Measure.smul_apply, smul_eq_mul, ← restrict_withDensity Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]

lemma capTest_allBall [Nontrivial E] {h : E → ℝ≥0∞} {c : E} (hc : ‖c‖ = 1)
    {r α : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hα0 : 0 ≤ α)
    (hα : 2*α = (Module.finrank ℝ E-1:ℕ)) (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    AllBallMass (capTestMeasure h c r) ((2048:ℝ)^Module.finrank ℝ E) α := by
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
  have hαd : α ≤ Module.finrank ℝ E := by
    have hn : ((Module.finrank ℝ E-1:ℕ):ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Nat.sub_le (Module.finrank ℝ E) 1
    linarith
  intro b t ht
  by_cases ht4 : t ≤ 1/4
  · let ξ := NoiselessRegression.ambientSphereLaw.withDensity h
    let T := (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) ∩ Metric.sphere 0 1
    have he : ξ (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) = ξ T := by
      apply measure_congr
      filter_upwards [(withDensity_absolutelyContinuous NoiselessRegression.ambientSphereLaw h).ae_le
        (NoiselessRegression.ambientSphereLaw_ae_norm (E := E))] with x hx
      have hs : x ∈ Metric.sphere (0:E) 1 := by simpa using hx
      apply propext
      simp only [T, Set.mem_inter_iff, hs, and_true]
    rw [capTestMeasure_ball h c hr, he]
    by_cases hT : T.Nonempty
    · obtain ⟨s,hs⟩ := hT
      have hsn : ‖s‖ = 1 := by simpa using hs.2
      obtain ⟨i,hi1,hi2,hsi⟩ := D.cover s hsn t ht ht4
      have hsub : T ⊆ Metric.closedBall (D.center i) (D.radius i) := by
        intro x hx
        change dist x (D.center i) ≤ D.radius i
        have hxB : dist x (dilate c r b) ≤ r*t := hx.1.1
        have hsB : dist s (dilate c r b) ≤ r*t := hs.1.1
        calc
          _ ≤ dist x s + dist s (D.center i) := dist_triangle _ _ _
          _ ≤ (dist x (dilate c r b) + dist (dilate c r b) s) + D.radius i/2 :=
            add_le_add (dist_triangle _ _ _) hsi
          _ ≤ D.radius i := by rw [dist_comm (dilate c r b) s]; linarith
      apply (mul_le_mul' le_rfl (measure_mono hsub)).trans
      have htest := weighted_cap_set_le (D.center_norm i) (D.radius_pos i)
        ((D.radius_le i).trans hr2) h (hdual i)
      apply (mul_le_mul' le_rfl htest).trans
      rw [← mul_assoc]
      exact (cap_cost_ratio hc hr hr2 (D.radius_pos i) hα).trans
        (ENNReal.ofReal_le_ofReal (cap_small_scale_constant _ hd hα0 hαd hr ht (D.radius_pos i).le hi2.le))
    · rw [Set.not_nonempty_iff_eq_empty.mp hT, measure_empty, mul_zero]
      exact bot_le
  · apply (measure_mono (Set.subset_univ _)).trans ((capTestMeasure_mass hr D hdual).trans ?_)
    have h4t : 1 ≤ 4*t := by linarith
    have hpow : 1 ≤ (4*t)^α := Real.one_le_rpow h4t hα0
    have h4 : (4:ℝ)^α ≤ (2048:ℝ)^Module.finrank ℝ E := by
      calc
        _ ≤ (4:ℝ)^(Module.finrank ℝ E:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
        _ = (4:ℝ)^Module.finrank ℝ E := Real.rpow_natCast _ _
        _ ≤ _ := by gcongr; norm_num
    rw [Real.mul_rpow (by norm_num) ht.le] at hpow
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hpow.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg ht.le α)))

lemma rescaled_projection_ac {ν : Measure E} {k : ℕ} (A : Fin k → E) (c : E) {r : ℝ} (hr : 0 < r)
    (hν : ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (ν.map (rescale c r)).map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  let T : (Fin k → ℝ) → (Fin k → ℝ) := fun y => r⁻¹ • (y-coordinateMap A c)
  have hT : Measurable T := by fun_prop
  have hv : (volume : Measure (Fin k → ℝ)).map T ≪ volume := by
    have he : T = (fun y : Fin k → ℝ => r⁻¹ • y) ∘ (fun y => y + -coordinateMap A c) := by
      funext y; simp [T,sub_eq_add_neg]
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.IsAddRightInvariant.map_add_right_eq_self, Measure.map_addHaar_smul volume (inv_ne_zero hr.ne')]
    exact Measure.smul_absolutelyContinuous
  have hh := (hν.map hT).trans hv
  rw [Measure.map_map hT (by fun_prop)] at hh
  rw [Measure.map_map (by fun_prop) (measurable_rescale c r)]
  convert hh using 1
  congr 1
  funext s
  ext i
  simp [T, rescale, coordinateMap_apply, real_inner_smul_left, inner_sub_left]

lemma capTest_frame_ac [Nontrivial E] (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r)
    {k : ℕ} (hk : k+2 ≤ Module.finrank ℝ E) (A : Fin k → E) (hA : Orthonormal ℝ A) :
    (capTestMeasure h c r).map (rowMap A) ≪ (volume : Measure (Label k)) := by
  apply (rowMap_ac_iff _).mpr
  apply rescaled_projection_ac A c hr
  have hh := (((withDensity_absolutelyContinuous (capMeasure c r) h).trans (capMeasure_ac c r)).map
    (show Measurable (coordinateMap A) by fun_prop)).trans (sphere_frame_ac hk hA)
  exact hh

end ProjectionMoments

end

end OAI
