import OAI.Geometry.TranslativeCovering.CapAffinity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapCost
open MeasureTheory SphericalLaw CapGeometry CapAffinity
open scoped ENNReal NNReal

noncomputable def rate {n : ℕ} (e : Sphere n) (t : ℝ) : ℝ≥0 :=
  ⟨((σ n).real (cap e.val t))⁻¹, inv_nonneg.mpr measureReal_nonneg⟩
noncomputable def intensity {n : ℕ} (e : Sphere n) (t : ℝ) : Measure (Sphere n) :=
  rate e t • σ n

instance intensity_finite {n : ℕ} [NeZero n] (e : Sphere n) (t : ℝ) :
    IsFiniteMeasure (intensity e t) := inferInstanceAs (IsFiniteMeasure (rate e t • σ n))
instance intensity_null {n : ℕ} [Fact (2 ≤ n)] (e : Sphere n) (t : ℝ) :
    NullSingletonClass (intensity e t) := ⟨by intro u; simp [intensity]⟩

lemma intensity_real {n : ℕ} (e : Sphere n) (t : ℝ) (E : Set (Sphere n)) :
    (intensity e t).real E = (σ n).real E/(σ n).real (cap e.val t) := by
  change (((rate e t : ℝ≥0∞)*(σ n) E).toReal) = _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  change ((σ n).real (cap e.val t))⁻¹ * (σ n).real E = _
  ring

lemma cap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (cap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (cap_positive e ht)) (measure_ne_top _ _)

lemma halfcap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (halfcap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (halfcap_positive e ht)) (measure_ne_top _ _)

lemma intensity_cap {n : ℕ} [NeZero n] (e f : Sphere n) {t s : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (hs : 0 ≤ s) :
    (intensity e t).real (cap f.val s) =
      (σ n).real (halfcap f.val s)/(σ n).real (halfcap f.val t) := by
  rw [intensity_real]
  have heq : (σ n).real (cap e.val t) = (σ n).real (cap f.val t) :=
    congrArg ENNReal.toReal (cap_equal_norm ((mem_sphere_zero_iff_norm.mp e.property).trans
      (mem_sphere_zero_iff_norm.mp f.property).symm) t)
  rw [heq,cap_mass f ht,cap_mass f hs]
  field_simp [(halfcap_real_pos f ht1).ne']

lemma log_decrease {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (htu : t ≤ u)
    (_hls : l ≤ s) (hsu : s ≤ u) :
    Real.log ((σ n).real (halfcap e.val t))-Real.log ((σ n).real (halfcap e.val s)) ≤
      (n:ℝ)*(1/l+1/(1-u^2))*max (s-t) 0 := by
  have htpos := halfcap_real_pos e (htu.trans_lt hu)
  have hspos := halfcap_real_pos e (hsu.trans_lt hu)
  have hA : 0 ≤ 1/l+1/(1-u^2) := by
    have hu0 := hl.trans_le (hlt.trans htu)
    have hh : 0 < 1-u^2 := by nlinarith
    positivity
  by_cases hts : t ≤ s
  · rw [max_eq_left (sub_nonneg.mpr hts)]
    have hh := (halfcap_ratio e hl hu hlt hts hsu).1
    have hlo := Real.log_le_log (Real.exp_pos _) hh
    rw [Real.log_exp,Real.log_div hspos.ne' htpos.ne'] at hlo
    have hmul := mul_nonneg hA (sub_nonneg.mpr hts)
    nlinarith
  · rw [max_eq_right (by linarith : s-t ≤ 0),mul_zero]
    have hm : (σ n).real (halfcap e.val t) ≤ (σ n).real (halfcap e.val s) :=
      CapOverlap.cap_antimono e (le_of_not_ge hts)
    exact sub_nonpos.mpr (Real.log_le_log htpos hm)

lemma clipped_cost {n : ℕ} [NeZero n] (e f : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (htu : t ≤ u)
    (hls : l ≤ s) (hsu : s ≤ u) :
    -Real.log (min ((intensity e t).real (cap f.val s)) (1/2)) ≤
      Real.log 2+(n:ℝ)*(1/l+1/(1-u^2))*max (s-t) 0 := by
  have htpos := halfcap_real_pos f (htu.trans_lt hu)
  have hspos := halfcap_real_pos f (hsu.trans_lt hu)
  rw [intensity_cap e f (hl.trans_le hlt).le (htu.trans_lt hu) (hl.trans_le hls).le]
  have hbound := log_decrease f hl hu hlt htu hls hsu
  have hA : 0 ≤ (n:ℝ)*(1/l+1/(1-u^2))*max (s-t) 0 := by
    have hu0 := hl.trans_le (hlt.trans htu)
    have hh : 0 < 1-u^2 := by nlinarith
    positivity
  by_cases hsmall : (σ n).real (halfcap f.val s)/(σ n).real (halfcap f.val t) ≤ 1/2
  · rw [min_eq_left hsmall, Real.log_div hspos.ne' htpos.ne']
    linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  · rw [min_eq_right (le_of_not_ge hsmall),Real.log_div one_ne_zero (by norm_num),Real.log_one]
    linarith

lemma raw_upper {n : ℕ} [NeZero n] (e f : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (htu : t ≤ u)
    (hls : l ≤ s) (hsu : s ≤ u) :
    (intensity e t).real (cap f.val s) ≤
      Real.exp ((n:ℝ)*(1/l+1/(1-u^2))*max (t-s) 0) := by
  rw [intensity_cap e f (hl.trans_le hlt).le (htu.trans_lt hu) (hl.trans_le hls).le]
  apply (Real.log_le_iff_le_exp (div_pos (halfcap_real_pos f (hsu.trans_lt hu))
    (halfcap_real_pos f (htu.trans_lt hu)))).mp
  rw [Real.log_div (halfcap_real_pos f (hsu.trans_lt hu)).ne'
    (halfcap_real_pos f (htu.trans_lt hu)).ne']
  exact log_decrease f hl hu hls hsu hlt htu

end CapCost

end OAI
