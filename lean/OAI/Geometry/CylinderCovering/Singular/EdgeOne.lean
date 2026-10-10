import OAI.Geometry.CylinderCovering.Singular.EdgeOneDefinitions

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SingularEdgeOne

lemma edgeU_eq (p w l : ℝ) : edgeU p w l = fieldP p (2 * w) l / 4 := by
  unfold edgeU fieldP
  ring

lemma edgeV_eq (p w : ℝ) {l : ℝ} (hl : 0 < l) :
    edgeV p w l = fieldQ p (2 * w) l / 2 := by
  have hr : (2 * l) ^ (p - 1) = (2 * l) ^ (p - 2) * (2 * l) := by
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add_one (by positivity)]
  unfold edgeV fieldQ
  rw [hr]
  field_simp

lemma ceiling_rescaling (p w c : ℝ) :
    c ^ 2 * ceiling p (2 * w) = (4 * c) ^ 2 * edgeCeiling p w := by
  unfold ceiling edgeCeiling
  ring

lemma physical_speed_rescaling (p w c : ℝ) {l : ℝ} (hl : 0 < l) :
    (4 * c) ^ 2 * (edgeU p w l ^ 2 + (1 / 2 : ℝ) * edgeV p w l ^ 2) =
      c ^ 2 * (fieldP p (2 * w) l ^ 2 + 2 * fieldQ p (2 * w) l ^ 2) := by
  rw [edgeU_eq, edgeV_eq p w hl]
  ring

lemma physical_height_square : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma physical_speed_rescaling_sqrt (p w c : ℝ) {l : ℝ} (hl : 0 < l) :
    (4 * c) ^ 2 *
      (edgeU p w l ^ 2 + (1 / Real.sqrt 2 : ℝ) ^ 2 * edgeV p w l ^ 2) =
      c ^ 2 * (fieldP p (2 * w) l ^ 2 + 2 * fieldQ p (2 * w) l ^ 2) := by
  rw [physical_height_square]
  exact physical_speed_rescaling p w c hl

lemma edgeCeiling_level (p w : ℝ) : edgeCeiling p w = w ^ 2 * edgeU p w (1 / 2) := by
  have hpow : (2 * (1 / 2 : ℝ)) ^ (p - 1) = 1 := by norm_num
  rw [edgeCeiling, edgeU, hpow]
  ring

lemma coefficient_rescaling (p : ℝ) :
    coefficient p / 32 = (2 * p ^ 2 + 10 * p - 13) / (15360 * p) := by
  unfold coefficient
  ring

lemma edge_coefficient {p : ℝ} (hp : p ≠ 0) :
    edgeA p - edgeG p = (2 * p ^ 2 + 10 * p - 13) / (15360 * p) := by
  unfold edgeA edgeG
  field_simp
  ring

lemma edge_coefficient_eq_scaled {p : ℝ} (hp : p ≠ 0) :
    edgeA p - edgeG p = coefficient p / 32 := by
  rw [edge_coefficient hp, coefficient_rescaling]

lemma coefficient_at_one : coefficient 1 = -(1 / 480 : ℝ) := by
  norm_num [coefficient]

lemma edgeA_at_one : edgeA 1 = 16 / 15360 := by norm_num [edgeA]
lemma edgeG_at_one : edgeG 1 = 17 / 15360 := by norm_num [edgeG]

lemma edgeA_continuous : Continuous edgeA := by unfold edgeA; fun_prop
lemma edgeG_continuousAt {p : ℝ} (hp : p ≠ 0) : ContinuousAt edgeG p := by
  unfold edgeG
  fun_prop (disch := positivity)

lemma edgeA_limit : Tendsto edgeA (𝓝 1) (𝓝 (16 / 15360)) := by
  simpa only [edgeA_at_one] using edgeA_continuous.continuousAt.tendsto (x := (1 : ℝ))

lemma edgeG_limit : Tendsto edgeG (𝓝 1) (𝓝 (17 / 15360)) := by
  simpa only [edgeG_at_one] using (edgeG_continuousAt (by norm_num : (1 : ℝ) ≠ 0)).tendsto

lemma right_rpow_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun c : ℝ => c ^ q) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => c ^ q) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ q)) :=
    ((Real.continuous_rpow_const hq.le).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  simpa only [Real.zero_rpow hq.ne'] using h

lemma power_isLittleO_power {a b : ℝ} (hab : b < a) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun c : ℝ => c ^ a) (fun c : ℝ => c ^ b) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · apply (right_rpow_tendsto_zero (sub_pos.mpr hab)).congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact Real.rpow_sub hc a b
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact fun h => False.elim ((Real.rpow_pos_of_pos hc b).ne' h)

lemma scaled_cutoff_small {p gamma A : ℝ} (hA : 0 < A)
    (hpg : gamma * (2 - p) < 1) :
    Tendsto (fun c : ℝ => c * (A * c ^ gamma) ^ (p - 2)) (𝓝[>] 0) (𝓝 0) := by
  have he : 0 < 1 + gamma * (p - 2) := by nlinarith
  have ht := (right_rpow_tendsto_zero he).const_mul (A ^ (p - 2))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hc.le _),
    ← Real.rpow_mul hc.le, Real.rpow_add hc, Real.rpow_one]
  ring

lemma power_flexibleCutoff {p gamma alpha A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hg : 1 < gamma)
    (hpg : gamma * (2 - p) < 1) (ha : 2 < alpha) (ha3 : alpha < 3) :
    FlexibleCutoff p (fun c : ℝ => A * c ^ gamma) (fun c : ℝ => B * c ^ alpha) := by
  refine ⟨?_, ?_, scaled_cutoff_small hA hpg, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact ⟨mul_pos hA (Real.rpow_pos_of_pos hc _),
      mul_pos hB (Real.rpow_pos_of_pos hc _)⟩
  · simpa only [Real.rpow_one] using (power_isLittleO_power hg).const_mul_left A
  · simpa only [Real.rpow_two] using (power_isLittleO_power ha).const_mul_left B
  · have hcube := Asymptotics.IsLittleO.const_mul_right hB.ne' (power_isLittleO_power ha3)
    have he : (fun c : ℝ => c ^ (3 : ℝ)) = fun c : ℝ => c ^ (3 : ℕ) :=
      funext (fun c => Real.rpow_natCast c 3)
    rw [he] at hcube
    exact hcube

lemma flexibleCutoff_congr {p : ℝ} {rho padding rho' padding' : ℝ → ℝ}
    (h : FlexibleCutoff p rho padding)
    (hr : rho =ᶠ[𝓝[>] (0 : ℝ)] rho') (hq : padding =ᶠ[𝓝[>] (0 : ℝ)] padding') :
    FlexibleCutoff p rho' padding' := by
  rcases h with ⟨hpos, hrsmall, hderiv, hqsmall, hcube⟩
  refine ⟨?_, hrsmall.congr' hr EventuallyEq.rfl, ?_,
    hqsmall.congr' hq EventuallyEq.rfl, hcube.congr' EventuallyEq.rfl hq⟩
  · filter_upwards [hpos, hr, hq] with c hc hrc hqc
    simpa only [← hrc, ← hqc] using hc
  · apply hderiv.congr'
    filter_upwards [hr] with c hc
    rw [hc]

lemma edgeOne_flexibleCutoff {p beta : ℝ} (hb : 1 < beta)
    (hbp : beta * (2 - p) < 1) :
    FlexibleCutoff p (fun c : ℝ => (4 * c) ^ beta)
      (fun c : ℝ => (4 * c) ^ (5 / 2 : ℝ)) := by
  have h := power_flexibleCutoff (p := p) (gamma := beta) (alpha := (5 / 2 : ℝ))
    (A := (4 : ℝ) ^ beta) (B := (4 : ℝ) ^ (5 / 2 : ℝ))
    (by positivity) (by positivity) hb hbp (by norm_num) (by norm_num)
  apply flexibleCutoff_congr h
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hc.le).symm
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact (Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hc.le).symm

lemma flexibleCutoff_tip_small {p : ℝ} {rho padding : ℝ → ℝ}
    (h : FlexibleCutoff p rho padding) :
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun c : ℝ => rho c ^ 2) (fun c : ℝ => c ^ 2) :=
  h.2.1.pow (by norm_num)

lemma parameters_imply_cutoff_bound {p gamma : ℝ} (hp : p < 2)
    (hg : gamma < 1 / (2 - p)) : gamma * (2 - p) < 1 :=
  (lt_div_iff₀ (sub_pos.mpr hp)).mp hg

lemma lower_sweep_dictionary (p c x y t b : ℝ) {r : ℝ} (hr : 0 < r) :
    (y = b + c * x * fieldP p b r ∧ t = r + c * x * fieldQ p b r) ↔
      (y / 2 = b / 2 + (4 * c) * (x / 2) * edgeU p (b / 2) r ∧
        t = r + (4 * c) * (x / 2) * edgeV p (b / 2) r) := by
  rw [edgeU_eq, edgeV_eq p (b / 2) hr]
  norm_num only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  constructor <;> rintro ⟨hy, ht⟩ <;> constructor <;> nlinarith [hy, ht]

lemma upper_sweep_dictionary (p c x y t b : ℝ) {r : ℝ} (hr : 0 < r) :
    (x = b - c * y * fieldP p b r ∧ 1 - t = r - c * y * fieldQ p b r) ↔
      (x / 2 = b / 2 - (4 * c) * (y / 2) * edgeU p (b / 2) r ∧
        1 - t = r - (4 * c) * (y / 2) * edgeV p (b / 2) r) := by
  rw [edgeU_eq, edgeV_eq p (b / 2) hr]
  norm_num only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  constructor <;> rintro ⟨hx, ht⟩ <;> constructor <;> nlinarith [hx, ht]

lemma cone_dictionary (b r : ℝ) : |b / 2| ≤ r / 2 ↔ |b| ≤ r := by
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  constructor <;> intro h <;> linarith

lemma ceiling_dictionary (p b c r padding : ℝ) :
    (r ≤ 1 / 2 + c ^ 2 * ceiling p b + padding) ↔
      r ≤ 1 / 2 + (4 * c) ^ 2 * edgeCeiling p (b / 2) + padding := by
  have h := ceiling_rescaling p (b / 2) c
  simp only [show 2 * (b / 2) = b by ring] at h
  rw [h]

lemma edgeA_integral (p : ℝ) :
    (∫ w in (-1 / 4 : ℝ)..(1 / 4 : ℝ), edgeCeiling p w) = edgeA p := by
  have he : edgeCeiling p = fun w : ℝ => (2 - p) * w ^ 4 + (p / 16) * w ^ 2 := by
    funext w
    unfold edgeCeiling
    ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun w : ℝ => (2 - p) * w ^ 4)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun w : ℝ => (p / 16) * w ^ 2)).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  norm_num [edgeA]
  ring

lemma angularEnergy_integral (p : ℝ) :
    (∫ R in (-1 / 2 : ℝ)..(1 / 2 : ℝ), angularEnergy p R) =
      (2 - p) ^ 2 / 2560 + p * (2 - p) / 768 + p ^ 2 / 512 + 1 / 192 := by
  have he : angularEnergy p = fun R : ℝ =>
      (2 - p) ^ 2 / 32 * R ^ 4 + (p * (2 - p) / 64 + 1 / 16) * R ^ 2 + p ^ 2 / 512 := by
    funext R
    unfold angularEnergy
    ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun R : ℝ =>
      (2 - p) ^ 2 / 32 * R ^ 4 + (p * (2 - p) / 64 + 1 / 16) * R ^ 2)).intervalIntegrable _ _)
    intervalIntegrable_const,
    intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun R : ℝ => (2 - p) ^ 2 / 32 * R ^ 4)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun R : ℝ =>
        (p * (2 - p) / 64 + 1 / 16) * R ^ 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, intervalIntegral.integral_const]
  norm_num
  ring

lemma edgeEnergy_polar (p R : ℝ) {l : ℝ} (hl : 0 < l) :
    edgeEnergy p (l * R) l = (2 * l) ^ (2 * p - 2) * angularEnergy p R := by
  have hr : ((2 * l) ^ (p - 1)) ^ 2 = (2 * l) ^ (2 * p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * l)]
    congr 1
    ring
  unfold edgeEnergy edgeU edgeV angularEnergy
  rw [mul_div_cancel_left₀ R hl.ne']
  nlinarith [hr]

lemma edgeEnergy_slice_integral (p : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    (∫ w in (-l / 2)..(l / 2), edgeEnergy p w l) =
      l * (2 * l) ^ (2 * p - 2) *
        (∫ R in (-1 / 2 : ℝ)..(1 / 2 : ℝ), angularEnergy p R) := by
  by_cases hl0 : l = 0
  · subst l
    simp
  have hlp : 0 < l := lt_of_le_of_ne hl (Ne.symm hl0)
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (fun w : ℝ => edgeEnergy p w l) l
  simp only [smul_eq_mul] at hs
  have hleft : l * (-1 / 2 : ℝ) = -l / 2 := by ring
  have hright : l * (1 / 2 : ℝ) = l / 2 := by ring
  rw [hleft, hright] at hs
  rw [← hs]
  simp_rw [edgeEnergy_polar p _ hlp]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma edge_radial_integral {p : ℝ} (hp : 0 < p) :
    (∫ l in (0 : ℝ)..(1 / 2 : ℝ), l * (2 * l) ^ (2 * p - 2)) = 1 / (8 * p) := by
  have he : (∫ l in (0 : ℝ)..(1 / 2 : ℝ), l * (2 * l) ^ (2 * p - 2)) =
      (∫ l in (0 : ℝ)..(1 / 2 : ℝ), (2 * l) ^ (2 * p - 1) / 2) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro l hl
    have hlp : 0 < 2 * l := by linarith [hl.1]
    dsimp only
    rw [show 2 * p - 1 = (2 * p - 2) + 1 by ring, Real.rpow_add_one hlp.ne']
    ring
  rw [he, intervalIntegral.integral_div]
  have hs := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (fun l : ℝ => l ^ (2 * p - 1))
    (c := (2 : ℝ)) (by norm_num)
  norm_num only [mul_zero, show (2 : ℝ) * (1 / 2) = 1 by norm_num, smul_eq_mul] at hs
  rw [hs, integral_rpow (Or.inl (by linarith : -1 < 2 * p - 1))]
  rw [show 2 * p - 1 + 1 = 2 * p by ring, Real.one_rpow,
    Real.zero_rpow (by positivity : 2 * p ≠ 0)]
  field_simp
  ring

lemma edgeG_iterated_integral {p : ℝ} (hp : 0 < p) :
    (∫ l in (0 : ℝ)..(1 / 2 : ℝ),
      ∫ w in (-l / 2)..(l / 2), edgeEnergy p w l) = edgeG p := by
  have he : (∫ l in (0 : ℝ)..(1 / 2 : ℝ),
      ∫ w in (-l / 2)..(l / 2), edgeEnergy p w l) =
      (∫ l in (0 : ℝ)..(1 / 2 : ℝ),
        (l * (2 * l) ^ (2 * p - 2)) *
          (∫ R in (-1 / 2 : ℝ)..(1 / 2 : ℝ), angularEnergy p R)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro l hl
    exact edgeEnergy_slice_integral p hl.1.le
  rw [he, intervalIntegral.integral_mul_const, edge_radial_integral hp,
    angularEnergy_integral]
  unfold edgeG
  field_simp
  ring

lemma coefficient_neg {p : ℝ} (hp : 1 < p)
    (hpmax : p < (Real.sqrt 51 - 5) / 2) : coefficient p < 0 := by
  have hsq : (2 * p + 5) ^ 2 < 51 := calc
    (2 * p + 5) ^ 2 < (Real.sqrt 51) ^ 2 :=
      (sq_lt_sq₀ (by linarith) (Real.sqrt_nonneg 51)).2 (by linarith)
    _ = 51 := Real.sq_sqrt (by norm_num)
  have hnum : 2 * p ^ 2 + 10 * p - 13 < 0 := by nlinarith
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hnum)
    (by linarith : 0 < 30 * p)

lemma edge_coefficient_neg {p : ℝ} (hp : 1 < p)
    (hpmax : p < (Real.sqrt 51 - 5) / 2) : edgeA p - edgeG p < 0 := by
  rw [edge_coefficient_eq_scaled (by linarith : p ≠ 0)]
  exact div_neg_of_neg_of_pos (coefficient_neg hp hpmax) (by norm_num)

lemma four_rpow_five_halves : (4 : ℝ) ^ (5 / 2 : ℝ) = 32 := by
  rw [show (5 / 2 : ℝ) = 2 + (1 / 2) by norm_num,
    Real.rpow_add (by norm_num : (0 : ℝ) < 4), Real.rpow_two,
    ← Real.sqrt_eq_rpow]
  norm_num

lemma exact_padding_dictionary {k : ℝ} (hk : 0 ≤ k) :
    (k / 4) ^ (5 / 2 : ℝ) = k ^ (5 / 2 : ℝ) / 32 := by
  rw [Real.div_rpow hk (by norm_num), four_rpow_five_halves]

lemma exact_cutoff_dictionary {k : ℝ} (hk : 0 ≤ k) (gamma : ℝ) :
    (k / 4) ^ gamma = (4 : ℝ) ^ (-gamma) * k ^ gamma := by
  rw [Real.div_rpow hk (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  ring

end SingularEdgeOne

end

end OAI
