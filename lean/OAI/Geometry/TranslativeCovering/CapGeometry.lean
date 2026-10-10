import OAI.Geometry.TranslativeCovering.ConeStretch

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

namespace CapGeometry
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
open SphericalLaw

def halfcap {n : ℕ} (x : Space n) (t : ℝ) : Set (Sphere n) :=
  {u | t < inner ℝ u.val x}

lemma halfcap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (halfcap x t) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

lemma halfcap_measurable {n : ℕ} (x : Space n) (t : ℝ) : MeasurableSet (halfcap x t) :=
  (halfcap_open x t).measurableSet

lemma halfcap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (halfcap u.val t) := by
  apply positive_open _ (halfcap_open _ _) ⟨u, ?_⟩
  change t < inner ℝ u.val u.val
  simpa only [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp u.property, one_pow] using ht

lemma halfcap_equal_norm {n : ℕ} {x y : Space n} (hxy : ‖x‖ = ‖y‖) (t : ℝ) :
    σ n (halfcap x t) = σ n (halfcap y t) := by
  let e := (Submodule.span ℝ ({x-y} : Set (Space n)))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hp : act e ⁻¹' halfcap y t = halfcap x t := by
    ext u
    change (t < inner ℝ (e u.val) y) ↔ (t < inner ℝ u.val x)
    rw [← he, e.inner_map_map]
  rw [← hp]
  exact invariant e _ (halfcap_measurable _ _)

noncomputable def axis {n : ℕ} (i : Fin n) : Sphere n :=
  ⟨EuclideanSpace.basisFun (Fin n) ℝ i, by simp⟩

lemma axis_inner {n : ℕ} (i : Fin n) (x : Space n) :
    inner ℝ x (axis i).val = x i := EuclideanSpace.inner_basisFun_real (Fin n) x i

lemma cone_eq {n : ℕ} (i : Fin n) (t : ℝ) :
    ConeStretch.cone i t 1 = Ioo (0 : ℝ) 1 • ((↑) '' halfcap (axis i).val t) := by
  ext x
  constructor
  · intro hx
    let u : Sphere n := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hx.1), inv_mul_cancel₀ hx.1.ne']⟩
    refine ⟨‖x‖, ⟨hx.1, hx.2.1⟩, u.val, ⟨u, ?_, rfl⟩, ?_⟩
    · change t < inner ℝ (‖x‖⁻¹ • x) (axis i).val
      rw [inner_smul_left, map_inv₀, conj_trivial, axis_inner]
      have hh := mul_lt_mul_of_pos_left hx.2.2 (inv_pos.mpr hx.1)
      simpa only [← mul_assoc, mul_left_comm ‖x‖⁻¹ t, inv_mul_cancel₀ hx.1.ne', mul_one] using hh
    · dsimp [u]
      simp [smul_smul, hx.1.ne']
  · rintro ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩
    have hun : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
    change 0 < ‖r • u.val‖ ∧ ‖r • u.val‖ < 1 ∧ t*‖r • u.val‖ < (r • u.val) i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hun, mul_one]
    refine ⟨hr.1, hr.2, ?_⟩
    change t < inner ℝ u.val (axis i).val at hu
    rw [axis_inner] at hu
    simpa only [PiLp.smul_apply, smul_eq_mul, mul_comm t] using mul_lt_mul_of_pos_left hu hr.1

lemma halfcap_eq_cone {n : ℕ} (i : Fin n) (t : ℝ) :
    σ n (halfcap (axis i).val t) =
      (((volume : Measure (Space n)).toSphere univ)⁻¹ * n) *
        volume (ConeStretch.cone i t 1) := by
  rw [σ, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply' _ (halfcap_measurable _ _),
    ← cone_eq]
  simp [Space, mul_assoc]

lemma halfcap_comparison {n : ℕ} (i : Fin n) {t s k r : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hs1 : s < 1) (hk : 1 ≤ k) (hr : 0 < r)
    (hrel : (k^2*(1-s^2)+s^2)*t^2 = s^2)
    (hrsq : r^2 = 1+(k^2-1)*t^2) :
    ENNReal.ofReal (r^n)*σ n (halfcap (axis i).val s) ≤
        ENNReal.ofReal k*σ n (halfcap (axis i).val t) ∧
    ENNReal.ofReal k*σ n (halfcap (axis i).val t) ≤
        ENNReal.ofReal (k^n)*σ n (halfcap (axis i).val s) := by
  have hh := ConeStretch.cone_volume_comparison i ht hs hs1 hk hr hrel hrsq
  rw [halfcap_eq_cone, halfcap_eq_cone]
  constructor
  · simpa only [mul_assoc, mul_left_comm] using mul_le_mul_right hh.1
      (((volume : Measure (Space n)).toSphere univ)⁻¹ * (n : ℝ≥0∞))
  · simpa only [mul_assoc, mul_left_comm] using mul_le_mul_right hh.2
      (((volume : Measure (Space n)).toSphere univ)⁻¹ * (n : ℝ≥0∞))

noncomputable def radial (t s : ℝ) : ℝ := Real.sqrt ((1-t^2)/(1-s^2))
noncomputable def axial (t s : ℝ) : ℝ := (s/t)*radial t s

lemma parameters {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s < 1) :
    1 ≤ axial t s ∧ 0 < radial t s ∧
    ((axial t s)^2*(1-s^2)+s^2)*t^2 = s^2 ∧
    (radial t s)^2 = 1+((axial t s)^2-1)*t^2 := by
  have hs0 : 0 < s := ht.trans_le hts
  have ht1 : t < 1 := hts.trans_lt hs
  have hb : 0 < 1-s^2 := by nlinarith
  have ha : 0 < 1-t^2 := by nlinarith
  have hrad : (radial t s)^2 = (1-t^2)/(1-s^2) := Real.sq_sqrt (div_pos ha hb).le
  have hr1 : 1 ≤ radial t s := by
    apply (Real.le_sqrt (by norm_num) (div_pos ha hb).le).mpr
    apply (le_div_iff₀ hb).mpr
    nlinarith
  have hr0 := zero_lt_one.trans_le hr1
  have hk1 : 1 ≤ axial t s := by
    exact one_le_mul_of_one_le_of_one_le ((one_le_div ht).mpr hts) hr1
  refine ⟨hk1, hr0, ?_, ?_⟩
  · dsimp [axial]
    rw [mul_pow, hrad]
    field_simp [ht.ne', hb.ne']
    ring
  · dsimp [axial]
    rw [mul_pow, hrad]
    field_simp [ht.ne', hb.ne']
    ring

lemma log_parameters {l u t s : ℝ} (hl : 0 < l) (hu : u < 1)
    (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u) :
    l*(s-t) ≤ Real.log (radial t s) ∧
    Real.log (axial t s) ≤ (1/l+1/(1-u^2))*(s-t) := by
  have ht : 0 < t := hl.trans_le hlt
  have hs0 : 0 < s := ht.trans_le hts
  have hs1 : s < 1 := hsu.trans_lt hu
  have ht1 : t < 1 := hts.trans_lt hs1
  have hb : 0 < 1-u^2 := by have : 0 < u := hs0.trans_le hsu; nlinarith
  let H := fun x : ℝ => -Real.log (1-x^2)/2
  let G := fun x : ℝ => Real.log x + H x
  have hH (x : ℝ) (hx : x ∈ Icc l u) : HasDerivAt H (x/(1-x^2)) x := by
    have hbx : 1-x^2 ≠ 0 := by have := hl.trans_le hx.1; have := hx.2.trans_lt hu; nlinarith
    convert! ((((hasDerivAt_id x).pow 2).const_sub 1).log hbx).neg.div_const 2 using 1; dsimp; ring
  have hG (x : ℝ) (hx : x ∈ Icc l u) :
      HasDerivAt G (1/x+x/(1-x^2)) x := by
    convert! (Real.hasDerivAt_log (ne_of_gt (hl.trans_le hx.1))).add (hH x hx) using 1;
      simp [one_div]
  have hHc : ContinuousOn H (Icc l u) := fun x hx => (hH x hx).continuousAt.continuousWithinAt
  have hGc : ContinuousOn G (Icc l u) := fun x hx => (hG x hx).continuousAt.continuousWithinAt
  have hHd : DifferentiableOn ℝ H (interior (Icc l u)) :=
    fun x hx => (hH x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hGd : DifferentiableOn ℝ G (interior (Icc l u)) :=
    fun x hx => (hG x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hlo (x : ℝ) (hx : x ∈ Icc l u) : l ≤ deriv H x := by
    rw [(hH x hx).deriv]
    have hbx : 0 < 1-x^2 := by have := hl.trans_le hx.1; have := hx.2.trans_lt hu; nlinarith
    apply (le_div_iff₀ hbx).mpr
    nlinarith [mul_nonneg hl.le (sq_nonneg x), hx.1]
  have hup (x : ℝ) (hx : x ∈ Icc l u) : deriv G x ≤ 1/l+1/(1-u^2) := by
    rw [(hG x hx).deriv]
    have hx0 : 0 < x := hl.trans_le hx.1
    have hx1 : x < 1 := hx.2.trans_lt hu
    have hbx : 0 < 1-x^2 := by nlinarith
    apply add_le_add (one_div_le_one_div_of_le hl hx.1)
    calc
      x/(1-x^2) ≤ 1/(1-x^2) := div_le_div_of_nonneg_right hx1.le hbx.le
      _ ≤ 1/(1-u^2) := one_div_le_one_div_of_le hb (by nlinarith [hx.2])
  have hlow := (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv hHc hHd
    (fun x hx => hlo x (interior_subset hx)) t ⟨hlt,hts.trans hsu⟩ s ⟨hlt.trans hts,hsu⟩ hts
  have hupp := (convex_Icc l u).image_sub_le_mul_sub_of_deriv_le hGc hGd
    (fun x hx => hup x (interior_subset hx)) t ⟨hlt,hts.trans hsu⟩ s ⟨hlt.trans hts,hsu⟩ hts
  have hbt : 0 < 1-t^2 := by nlinarith
  have hbs : 0 < 1-s^2 := by nlinarith
  have hrad : Real.log (radial t s) = H s-H t := by
    rw [radial, Real.log_sqrt (div_pos hbt hbs).le,
      Real.log_div hbt.ne' hbs.ne']
    dsimp [H]; ring
  have hrpos := (parameters ht hts hs1).2.1
  have hax : Real.log (axial t s) = G s-G t := by
    rw [axial, Real.log_mul (div_pos hs0 ht).ne' hrpos.ne',
      Real.log_div hs0.ne' ht.ne', hrad]
    dsimp [G]; ring
  rw [hrad, hax]
  exact ⟨hlow, hupp⟩

lemma halfcap_ratio {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u) :
    Real.exp (-((n:ℝ)-1)*(1/l+1/(1-u^2))*(s-t)) ≤
      (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) ∧
    (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) ≤
      Real.exp (((1/l+1/(1-u^2))-(n:ℝ)*l)*(s-t)) := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have ht : 0 < t := hl.trans_le hlt
  have hs0 : 0 < s := ht.trans_le hts
  have hs1 : s < 1 := hsu.trans_lt hu
  have par := parameters ht hts hs1
  have hh := halfcap_comparison i ht hs0 hs1 par.1 par.2.1 par.2.2.1 par.2.2.2
  have heq (v : ℝ) : σ n (halfcap (axis i).val v) = σ n (halfcap e.val v) :=
    halfcap_equal_norm (by rw [mem_sphere_zero_iff_norm.mp (axis i).property,
      mem_sphere_zero_iff_norm.mp e.property]) v
  rw [heq s, heq t] at hh
  have hk0 : 0 < axial t s := zero_lt_one.trans_le par.1
  have hr0 : 0 < radial t s := par.2.1
  have hspos : 0 < (σ n).real (halfcap e.val s) :=
    ENNReal.toReal_pos (ne_of_gt (halfcap_positive e hs1)) (measure_ne_top _ _)
  have htpos : 0 < (σ n).real (halfcap e.val t) :=
    ENNReal.toReal_pos (ne_of_gt (halfcap_positive e (hts.trans_lt hs1))) (measure_ne_top _ _)
  have hreal1 : (radial t s)^n*(σ n).real (halfcap e.val s) ≤
      axial t s*(σ n).real (halfcap e.val t) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hh.1
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr0.le n),
      ENNReal.toReal_ofReal hk0.le, measureReal_def] using this
  have hreal2 : axial t s*(σ n).real (halfcap e.val t) ≤
      (axial t s)^n*(σ n).real (halfcap e.val s) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hh.2
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hk0.le n),
      ENNReal.toReal_ofReal hk0.le, measureReal_def] using this
  have logr := log_parameters hl hu hlt hts hsu
  have hlog1 := Real.log_le_log (mul_pos (pow_pos hr0 n) hspos) hreal1
  have hlog2 := Real.log_le_log (mul_pos hk0 htpos) hreal2
  simp only [Real.log_mul (pow_pos hr0 n).ne' hspos.ne', Real.log_mul hk0.ne' htpos.ne',
    Real.log_mul (pow_pos hk0 n).ne' hspos.ne', Real.log_pow] at hlog1 hlog2
  have hnreal : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have he : Real.exp (Real.log ((σ n).real (halfcap e.val s)) -
      Real.log ((σ n).real (halfcap e.val t))) =
      (σ n).real (halfcap e.val s)/(σ n).real (halfcap e.val t) := by
    rw [Real.exp_sub, Real.exp_log hspos, Real.exp_log htpos]
  rw [← he]
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left logr.2 (sub_nonneg.mpr hnreal)]
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left logr.1 (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

end CapGeometry

end OAI
