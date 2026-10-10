import OAI.Analysis.HenonEmden.PotentialContinuity

namespace OAI

universe uE

section CapGeometry

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal Pointwise
noncomputable section
namespace HenonLaneEmden.CapGeometry

/-- Radial bands in the positive-radius factor of polar coordinates. -/
def band (a b : ℝ) : Set (Ioi (0:ℝ)) := {r | a < r.1 ∧ r.1 < b}

lemma volumeIoiPow_band_bounds (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ENNReal.ofReal (a^k*(b-a)) ≤ volumeIoiPow k (band a b) ∧
    volumeIoiPow k (band a b) ≤ ENNReal.ofReal (b^k*(b-a)) := by
  have hband : MeasurableSet (band a b) := (measurable_subtype_coe measurableSet_Ioo)
  have he : Subtype.val '' band a b = Ioo a b := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩; exact hr
    · intro hx; exact ⟨⟨x,ha.trans_lt hx.1⟩,hx,rfl⟩
  rw [volumeIoiPow,withDensity_apply _ hband,
    setLIntegral_subtype measurableSet_Ioi _ (fun r : ℝ => ENNReal.ofReal (r^k)),he]
  have hconst (c : ℝ) (hc : 0 ≤ c) :
      (∫⁻ _ in Ioo a b, ENNReal.ofReal c) = ENNReal.ofReal (c*(b-a)) := by
    rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,← ENNReal.ofReal_mul hc]
  constructor
  · rw [← hconst (a^k) (pow_nonneg ha k)]
    apply setLIntegral_mono' measurableSet_Ioo
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha hx.1.le k)
  · rw [← hconst (b^k) (pow_nonneg (ha.trans hab) k)]
    apply setLIntegral_mono' measurableSet_Ioo
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (ha.trans hx.1.le) hx.2.le k)

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma polar_rectangle_le {S : Set (sphere (0:E) 1)} {I : Set (Ioi (0:ℝ))} {A : Set E}
    (hS : MeasurableSet S) (hI : MeasurableSet I) (hA : MeasurableSet A)
    (h : ∀ e ∈ S, ∀ r ∈ I, r.1 • e.1 ∈ A) :
    μ.toSphere S * volumeIoiPow (Module.finrank ℝ E-1) I ≤ μ A := by
  rw [← Measure.prod_prod]
  have he : μ A = ∫⁻ z : sphere (0:E) 1 × Ioi (0:ℝ), A.indicator (fun _ => (1:ℝ≥0∞))
      (z.2.1 • z.1.1) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
    rw [← Polar.lintegral_polar_prod μ,lintegral_indicator hA,lintegral_one,Measure.restrict_apply_univ]
  have hr : (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) (S ×ˢ I) =
      ∫⁻ z, (S ×ˢ I).indicator (fun _ => (1:ℝ≥0∞)) z
        ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
    rw [lintegral_indicator (hS.prod hI),lintegral_one,Measure.restrict_apply_univ]
  rw [he,hr]
  apply lintegral_mono
  intro z
  by_cases hz : z ∈ S ×ˢ I
  · simp only [indicator_of_mem hz,indicator_of_mem (h z.1 hz.1 z.2 hz.2),le_refl]
  · simp only [indicator_of_notMem hz,zero_le]

lemma measure_le_polar_rectangle {S : Set (sphere (0:E) 1)} {I : Set (Ioi (0:ℝ))} {A : Set E}
    (hS : MeasurableSet S) (hI : MeasurableSet I) (hA : MeasurableSet A)
    (h : ∀ e r, r.1 • e.1 ∈ A → e ∈ S ∧ r ∈ I) :
    μ A ≤ μ.toSphere S * volumeIoiPow (Module.finrank ℝ E-1) I := by
  rw [← Measure.prod_prod]
  have he : μ A = ∫⁻ z : sphere (0:E) 1 × Ioi (0:ℝ), A.indicator (fun _ => (1:ℝ≥0∞))
      (z.2.1 • z.1.1) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
    rw [← Polar.lintegral_polar_prod μ,lintegral_indicator hA,lintegral_one,Measure.restrict_apply_univ]
  have hr : (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1))) (S ×ˢ I) =
      ∫⁻ z, (S ×ˢ I).indicator (fun _ => (1:ℝ≥0∞)) z
        ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E-1)) := by
    rw [lintegral_indicator (hS.prod hI),lintegral_one,Measure.restrict_apply_univ]
  rw [he,hr]
  apply lintegral_mono
  intro z
  by_cases hz : z.2.1 • z.1.1 ∈ A
  · have hz' : z ∈ S ×ˢ I := h z.1 z.2 hz
    simp only [indicator_of_mem hz,indicator_of_mem hz',le_refl]
  · simp only [indicator_of_notMem hz,zero_le]

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma norm_unit (e : sphere (0:E) 1) : ‖(e:E)‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using e.2

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma polar_unit_distance (e θ : sphere (0:E) 1) {r : ℝ} (hr : 0 ≤ r) :
    |r-1| ≤ ‖r • (e:E) - (θ:E)‖ ∧
    dist e θ ≤ 2 * ‖r • (e:E) - (θ:E)‖ := by
  have hn : ‖r • (e:E)‖ = r := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,norm_unit,mul_one]
  have hab : |r-1| ≤ ‖r • (e:E) - (θ:E)‖ := by
    simpa only [hn,norm_unit] using abs_norm_sub_norm_le (r • (e:E)) (θ:E)
  refine ⟨hab,?_⟩
  have heq : ‖(e:E)-r • (e:E)‖ = |r-1| := by
    have hev : (e:E)-r • (e:E) = (1-r) • (e:E) := by rw [sub_smul,one_smul]
    rw [hev,norm_smul,Real.norm_eq_abs,norm_unit,mul_one,abs_sub_comm]
  have hh := dist_triangle (e:E) (r • (e:E)) (θ:E)
  simp only [dist_eq_norm] at hh
  rw [heq] at hh
  rw [Subtype.dist_eq,dist_eq_norm]
  linarith

lemma cap_lower_product (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    μ (ball (θ:E) (l/4)) ≤ μ.toSphere (ball θ l) *
      ENNReal.ofReal (2^(Module.finrank ℝ E-1)*l) := by
  have ha : 0 ≤ 1-l/4 := by linarith
  have hb : 1-l/4 ≤ 1+l/4 := by linarith
  have hgeom := measure_le_polar_rectangle μ (S := ball θ l)
    (I := band (1-l/4) (1+l/4)) measurableSet_ball
    (measurable_subtype_coe measurableSet_Ioo) measurableSet_ball (A := ball (θ:E) (l/4)) (by
      intro e r hr
      have hd : ‖r.1 • (e:E)-(θ:E)‖ < l/4 := by simpa only [mem_ball,dist_eq_norm] using hr
      have hh := polar_unit_distance e θ r.2.le
      constructor
      · change dist e θ < l
        linarith [hh.2]
      · change 1-l/4 < r.1 ∧ r.1 < 1+l/4
        have har : |r.1-1| < l/4 := hh.1.trans_lt hd
        obtain ⟨hlo,hhi⟩ := abs_lt.mp har
        constructor <;> linarith)
  apply hgeom.trans
  gcongr
  apply (volumeIoiPow_band_bounds _ ha hb).2.trans
  apply ENNReal.ofReal_le_ofReal
  have hp : (1+l/4)^(Module.finrank ℝ E-1) ≤ 2^(Module.finrank ℝ E-1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  calc
    (1+l/4)^(Module.finrank ℝ E-1)*((1+l/4)-(1-l/4)) =
        (1+l/4)^(Module.finrank ℝ E-1)*(l/2) := by ring
    _ ≤ 2^(Module.finrank ℝ E-1)*(l/2) := by gcongr
    _ ≤ _ := by gcongr; linarith

lemma cap_upper_product (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    μ.toSphere (ball θ l) * ENNReal.ofReal ((1/2:ℝ)^(Module.finrank ℝ E-1)*(l/2)) ≤
      μ (ball (θ:E) (2*l)) := by
  have ha : 0 ≤ 1-l/2 := by linarith
  have hb : 1-l/2 ≤ 1 := by linarith
  have hgeom := polar_rectangle_le μ (S := ball θ l)
    (I := band (1-l/2) 1) measurableSet_ball
    (measurable_subtype_coe measurableSet_Ioo) measurableSet_ball (A := ball (θ:E) (2*l)) (by
      intro e he r hr
      have hd : ‖(e:E)-(θ:E)‖ < l := by simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using he
      have hr1 : r.1 < 1 := hr.2
      have hrl : 1-l/2 < r.1 := hr.1
      have heq : ‖r.1 • (e:E)-(e:E)‖ = 1-r.1 := by
        have hev : r.1 • (e:E)-(e:E) = (r.1-1) • (e:E) := by rw [sub_smul,one_smul]
        rw [hev,norm_smul,Real.norm_eq_abs,norm_unit,mul_one,abs_of_neg (by linarith)]
        ring
      have hh := dist_triangle (r.1 • (e:E)) (e:E) (θ:E)
      simp only [dist_eq_norm] at hh
      rw [heq] at hh
      rw [mem_ball,dist_eq_norm]
      linarith)
  apply le_trans _ hgeom
  gcongr
  apply le_trans _ (volumeIoiPow_band_bounds _ ha hb).1
  apply ENNReal.ofReal_le_ofReal
  have hp : (1/2:ℝ)^(Module.finrank ℝ E-1) ≤ (1-l/2)^(Module.finrank ℝ E-1) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  have heq : 1-(1-l/2) = l/2 := by ring
  rw [heq]
  gcongr

lemma cap_real_bounds (θ : sphere (0:E) 1) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (μ (ball (0:E) 1)).toReal / (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) *
        l^(Module.finrank ℝ E-1) ≤ (μ.toSphere (ball θ l)).toReal ∧
    (μ.toSphere (ball θ l)).toReal ≤
      4^Module.finrank ℝ E * (μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1) := by
  have hn : Module.finrank ℝ E-1+1 = Module.finrank ℝ E :=
    Nat.sub_add_cancel (Module.finrank_pos : 0 < Module.finrank ℝ E)
  have hbf : μ (ball (0:E) 1) ≠ ⊤ := (isBounded_ball.measure_lt_top (μ := μ)).ne
  have hcf : μ.toSphere (ball θ l) ≠ ⊤ := measure_ne_top _ _
  have hlo := cap_lower_product μ θ hl hl1
  rw [μ.addHaar_ball _ (by positivity)] at hlo
  have hlor := ENNReal.toReal_mono (ENNReal.mul_ne_top hcf ENNReal.ofReal_ne_top) hlo
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (show 0 ≤ (l/4)^Module.finrank ℝ E by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ (2:ℝ)^(Module.finrank ℝ E-1)*l by positivity)] at hlor
  have hhi := cap_upper_product μ θ hl hl1
  rw [μ.addHaar_ball _ (by positivity)] at hhi
  have hhir := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbf) hhi
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ (2*l)^Module.finrank ℝ E by positivity),
    ENNReal.toReal_ofReal (show 0 ≤ (1/2:ℝ)^(Module.finrank ℝ E-1)*(l/2) by positivity)] at hhir
  have hlpow : l^Module.finrank ℝ E = l^(Module.finrank ℝ E-1)*l := by
    nth_rw 1 [← hn]; rw [pow_succ]
  have h2pow : (2:ℝ)^Module.finrank ℝ E = 2^(Module.finrank ℝ E-1)*2 := by
    nth_rw 1 [← hn]; rw [pow_succ]
  have h4pow : (4:ℝ)^Module.finrank ℝ E = (2^Module.finrank ℝ E)^2 := by
    rw [← pow_mul, mul_comm _ 2,pow_mul]; norm_num
  constructor
  · rw [div_pow,hlpow] at hlor
    have h4 : (0:ℝ) < 4^Module.finrank ℝ E := by positivity
    have h2 : (0:ℝ) < 2^(Module.finrank ℝ E-1) := by positivity
    have hs : (μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1) * l ≤
        (μ.toSphere (ball θ l)).toReal * (2^(Module.finrank ℝ E-1)*l) * 4^Module.finrank ℝ E := by
      apply (div_le_iff₀ h4).mp
      simpa only [div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hlor
    have hh : (μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1) ≤
        (μ.toSphere (ball θ l)).toReal * (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) := by
      apply (mul_le_mul_iff_left₀ hl).mp
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hs
    calc
      _ = ((μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1)) /
          (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) := by ring
      _ ≤ _ := (div_le_iff₀ (mul_pos h4 h2)).mpr hh
  · apply (mul_le_mul_iff_left₀ (show 0 < (1/2:ℝ)^(Module.finrank ℝ E-1)*(l/2) by positivity)).mp
    calc
      _ ≤ (2*l)^Module.finrank ℝ E * (μ (ball (0:E) 1)).toReal := hhir
      _ = (4^Module.finrank ℝ E * (μ (ball (0:E) 1)).toReal * l^(Module.finrank ℝ E-1)) *
          ((1/2:ℝ)^(Module.finrank ℝ E-1)*(l/2)) := by
        rw [mul_pow,hlpow,h4pow,h2pow,div_pow]
        field_simp
        ring

omit [BorelSpace E] [Nontrivial E] in
lemma cap_constants_pos :
    0 < (μ (ball (0:E) 1)).toReal / (4^Module.finrank ℝ E * 2^(Module.finrank ℝ E-1)) ∧
    0 < (4:ℝ)^Module.finrank ℝ E * (μ (ball (0:E) 1)).toReal := by
  have hp : 0 < (μ (ball (0:E) 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 (by norm_num)))
      (isBounded_ball.measure_lt_top (μ := μ)).ne
  constructor <;> positivity

end HenonLaneEmden.CapGeometry
end
end CapGeometry

end OAI
