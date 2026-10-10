import OAI.Probability.LatticePassage.CalibrationMean
import OAI.Probability.LatticePassage.DirectionalConvergence

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Filter Topology Set
open scoped NNReal

lemma meanPassageSequence_neg (x : Vertex) (n : ℕ) :
    meanPassageSequence (-x) n = meanPassageSequence x n := by
  have he : scaleVertex n (-x) = -(scaleVertex n x) := by ext <;> simp [scaleVertex]
  unfold meanPassageSequence
  rw [he]
  have ht := mean_passageTime_translation (-(scaleVertex n x)) (scaleVertex n x) 0
  simp only [neg_add_cancel, add_zero] at ht
  rw [ht]
  apply integral_congr_ae
  filter_upwards [passageTime_properties] with ω hω
  exact hω.2.2.1 _ _

lemma directionalMeanConstant_neg (x : Vertex) : directionalMeanConstant (-x) = directionalMeanConstant x := by
  have h := meanPassageSequence_tendsto (-x)
  simp_rw [meanPassageSequence_neg] at h
  exact tendsto_nhds_unique h (meanPassageSequence_tendsto x)

lemma DirectionalCalibration.abs_meanHom_le {d : Vertex} (C : DirectionalCalibration d) (x : Vertex) :
    |C.meanHom x| ≤ directionalMeanConstant x := by
  apply abs_le.mpr
  have hp := C.meanHom_le_directionalMeanConstant x
  have hn := C.meanHom_le_directionalMeanConstant (-x)
  rw [map_neg, directionalMeanConstant_neg] at hn
  exact ⟨by linarith,hp⟩

lemma DirectionalCalibration.abs_meanHom_le_distance {d : Vertex} (C : DirectionalCalibration d) (x : Vertex) :
    |C.meanHom x| ≤ (latticeDistance 0 x : ℝ) :=
  (C.abs_meanHom_le x).trans ((directionalMeanConstant_le_mean x).trans (mean_passageTime_le_distance 0 x))

noncomputable def chosenCalibration (d : Vertex) : DirectionalCalibration d :=
  Classical.choice (exists_directionalCalibration d)

noncomputable def supportSeminorm (d : Vertex) : Seminorm ℝ Plane :=
  (normSeminorm ℝ ℝ).comp (chosenCalibration d).meanLinear

lemma supportSeminorm_apply (d : Vertex) (v : Plane) :
    supportSeminorm d v = |v.1*(chosenCalibration d).meanHom (1,0)+
      v.2*(chosenCalibration d).meanHom (0,1)| := rfl

lemma supportSeminorm_bound (d : Vertex) (v : Plane) : supportSeminorm d v ≤ 2*‖v‖ := by
  have h₁ : |(chosenCalibration d).meanHom (1,0)| ≤ 1 := by
    simpa [latticeDistance] using (chosenCalibration d).abs_meanHom_le_distance (1,0)
  have h₂ : |(chosenCalibration d).meanHom (0,1)| ≤ 1 := by
    simpa [latticeDistance] using (chosenCalibration d).abs_meanHom_le_distance (0,1)
  rw [supportSeminorm_apply]
  calc
    _ ≤ |v.1| * |(chosenCalibration d).meanHom (1,0)|+
        |v.2| * |(chosenCalibration d).meanHom (0,1)| := by
      simpa only [abs_mul] using abs_add_le (v.1*(chosenCalibration d).meanHom (1,0))
        (v.2*(chosenCalibration d).meanHom (0,1))
    _ ≤ |v.1|+|v.2| := by
      nlinarith [mul_le_mul_of_nonneg_left h₁ (abs_nonneg v.1),
        mul_le_mul_of_nonneg_left h₂ (abs_nonneg v.2)]
    _ ≤ 2*‖v‖ := by
      have hfst := norm_fst_le v
      have hsnd := norm_snd_le v
      simp only [Real.norm_eq_abs] at hfst hsnd
      linarith

lemma supportSeminorm_bddAbove : BddAbove (range supportSeminorm) := by
  refine ⟨(2 : ℝ≥0) • normSeminorm ℝ Plane, ?_⟩
  rintro _ ⟨d,rfl⟩ v
  exact supportSeminorm_bound d v

noncomputable def timeSeminorm : Seminorm ℝ Plane := ⨆ d : Vertex, supportSeminorm d

lemma timeSeminorm_bound (v : Plane) : timeSeminorm v ≤ 2*‖v‖ := by
  rw [timeSeminorm, Seminorm.iSup_apply supportSeminorm_bddAbove]
  exact ciSup_le (fun d => supportSeminorm_bound d v)

lemma timeSeminorm_continuous : Continuous timeSeminorm := by
  apply Seminorm.continuous_of_le (q := (2 : ℝ≥0) • normSeminorm ℝ Plane)
    (show Continuous (fun v : Plane => (2 : ℝ)*‖v‖) by fun_prop)
  exact timeSeminorm_bound

theorem timeSeminorm_embed (x : Vertex) : timeSeminorm (embed x) = directionalMeanConstant x := by
  have he (d : Vertex) : supportSeminorm d (embed x) = |(chosenCalibration d).meanHom x| := by
    change |(chosenCalibration d).meanLinear (embed x)| = _
    rw [(chosenCalibration d).meanLinear_embed]
  rw [timeSeminorm, Seminorm.iSup_apply supportSeminorm_bddAbove]
  apply le_antisymm
  · apply ciSup_le
    intro d
    rw [he]
    exact (chosenCalibration d).abs_meanHom_le x
  · have hb : BddAbove (range (fun d => supportSeminorm d (embed x))) :=
      ⟨2*‖embed x‖,by rintro _ ⟨d,rfl⟩; exact supportSeminorm_bound d (embed x)⟩
    have h := le_ciSup hb x
    rw [he, (chosenCalibration x).meanHom_direction, abs_of_nonneg (directionalMeanConstant_nonneg x)] at h
    exact h

lemma scaled_floor_tendsto (r : ℝ) :
    Tendsto (fun n : ℕ => (⌊(n+1 : ℝ)*r⌋ : ℝ)/(n+1)) atTop (𝓝 r) := by
  have hl : ∀ n : ℕ, r-1/(n+1 : ℝ) ≤ (⌊(n+1 : ℝ)*r⌋ : ℝ)/(n+1) := by
    intro n
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < n+1), sub_mul,
      div_mul_cancel₀ _ (by positivity : (n+1 : ℝ) ≠ 0)]
    linarith [Int.lt_floor_add_one ((n+1 : ℝ)*r)]
  have hu : ∀ n : ℕ, (⌊(n+1 : ℝ)*r⌋ : ℝ)/(n+1) ≤ r := by
    intro n
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr
    simpa only [mul_comm r] using Int.floor_le ((n+1 : ℝ)*r)
  have hlim := (tendsto_const_nhds (x := r) (f := atTop)).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hlim)
    tendsto_const_nhds hl hu

noncomputable def floorVertex (v : Plane) (n : ℕ) : Vertex := (⌊(n+1 : ℝ)*v.1⌋,⌊(n+1 : ℝ)*v.2⌋)

lemma floorVertex_scaled_tendsto (v : Plane) :
    Tendsto (fun n : ℕ => (1/(n+1 : ℝ)) • embed (floorVertex v n)) atTop (𝓝 v) := by
  have h := (scaled_floor_tendsto v.1).prodMk_nhds (scaled_floor_tendsto v.2)
  simpa only [floorVertex, embed, Prod.smul_mk, smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul, Prod.mk.eta] using h

lemma timeSeminorm_scaled_lattice_lower (x : Vertex) (a : ℝ) (ha : 0 ≤ a) :
    (log 2/20)*(|(a • embed x).1|+|(a • embed x).2|) ≤ timeSeminorm (a • embed x) := by
  have h := mul_le_mul_of_nonneg_left (directionalMeanConstant_linear_lower x) ha
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ha, timeSeminorm_embed]
  have he : (latticeDistance 0 x : ℝ) = |(x.1 : ℝ)|+|(x.2 : ℝ)| := by
    simp [latticeDistance]
  rw [he] at h
  simpa only [embed, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul, abs_of_nonneg ha,
    mul_add, mul_assoc, mul_left_comm] using h

theorem timeSeminorm_linear_lower (v : Plane) :
    (log 2/20)*(|v.1|+|v.2|) ≤ timeSeminorm v := by
  have h := floorVertex_scaled_tendsto v
  have hl := ((continuous_fst.tendsto v).comp h).abs.add (((continuous_snd.tendsto v).comp h).abs)
  apply le_of_tendsto_of_tendsto (hl.const_mul (log 2/20)) (timeSeminorm_continuous.tendsto v |>.comp h)
  exact Eventually.of_forall (fun n => timeSeminorm_scaled_lattice_lower (floorVertex v n) _ (by positivity))

noncomputable def actualTimeNorm : TimeNorm where
  seminorm := timeSeminorm
  definite v hv := by
    have h := timeSeminorm_linear_lower v
    rw [hv] at h
    have hc : 0 < log 2/20 := by positivity
    have hz : |v.1|+|v.2| = 0 := by nlinarith [abs_nonneg v.1,abs_nonneg v.2]
    have h₁ : v.1 = 0 := abs_eq_zero.mp (by linarith [abs_nonneg v.1,abs_nonneg v.2])
    have h₂ : v.2 = 0 := abs_eq_zero.mp (by linarith [abs_nonneg v.1,abs_nonneg v.2])
    exact Prod.ext h₁ h₂

theorem actualTimeNorm_hasTimeConstant : HasTimeConstant actualTimeNorm := by
  filter_upwards [passageTime_all_directions_tendsto] with ω hω
  intro x
  change Tendsto (fun n : ℕ => passageTime ω (0 : Vertex) (scaleVertex n x)/(n : ℝ))
    atTop (𝓝 (timeSeminorm (embed x)))
  rw [timeSeminorm_embed]
  exact hω x

theorem exists_timeNorm_hasTimeConstant : ∃ μ : TimeNorm, HasTimeConstant μ :=
  ⟨actualTimeNorm, actualTimeNorm_hasTimeConstant⟩

end CompanionFPP

end OAI
