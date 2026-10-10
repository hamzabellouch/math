import OAI.Geometry.TranslativeCovering.CapGeometry

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

universe u_1

namespace CapLens
open Set MeasureTheory Metric SphericalLaw CapGeometry
open scoped ENNReal Pointwise

noncomputable def unit {n : ℕ} (x : Space n) (hx : x ≠ 0) : Sphere n :=
  ⟨‖x‖⁻¹ • x, by rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

lemma inner_unit {n : ℕ} (x : Space n) (hx : x ≠ 0) (y : Space n) :
    inner ℝ y (unit x hx).val = inner ℝ y x / ‖x‖ := by
  simp [unit, inner_smul_right, div_eq_mul_inv, mul_comm]

lemma tangent_bad_subset {n : ℕ} (e v : Sphere n)
    (hev : inner ℝ e.val v.val = 0) {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    ∃ w : Sphere n, halfcap e.val t ∩ {u : Sphere n | inner ℝ u.val v.val < -h} ⊆
      halfcap w.val (Real.sqrt (t^2+h^2)) := by
  let z := t • e.val - h • v.val
  have hn : ‖z‖^2 = t^2+h^2 := by
    dsimp [z]
    rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp e.property, mem_sphere_zero_iff_norm.mp v.property,
      inner_smul_left, inner_smul_right, hev]
    simp [sq_abs]
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hn
    nlinarith [sq_nonneg h]
  refine ⟨unit z hz, ?_⟩
  intro u hu
  change Real.sqrt (t^2+h^2) < inner ℝ u.val (unit z hz).val
  rw [inner_unit, lt_div_iff₀ (norm_pos_iff.mpr hz)]
  have he : Real.sqrt (t^2+h^2) = ‖z‖ := by rw [← hn, Real.sqrt_sq (norm_nonneg z)]
  rw [he]
  have hu1 : t < inner ℝ u.val e.val := hu.1
  have hu2 : inner ℝ u.val v.val < -h := hu.2
  have hprod := mul_lt_mul_of_pos_left hu1 ht
  have hprod2 := mul_le_mul_of_nonneg_left hu2.le hh
  dsimp [z]
  rw [inner_sub_right, inner_smul_right, inner_smul_right]
  nlinarith [hn]

lemma tangent_bad_measure {n : ℕ} [NeZero n] (e v : Sphere n)
    (hev : inner ℝ e.val v.val = 0) {l u t h : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v.val < -h}) ≤
      Real.exp (-(n:ℝ)*l*h^2/4) * (σ n).real (halfcap e.val t) := by
  have ht : 0 < t := hl.trans_le hlt
  let q := Real.sqrt (t^2+h^2)
  have hq2 : q^2 = t^2+h^2 := Real.sq_sqrt (by positivity)
  have htq : t ≤ q := by
    dsimp [q]
    apply (Real.le_sqrt ht.le (by positivity)).mpr
    nlinarith [sq_nonneg h]
  have ht1 : t < 1 := (htq.trans hqu).trans_lt hu
  have hq1 : q < 1 := hqu.trans_lt hu
  have hgap : h^2/2 ≤ q-t := by nlinarith [sq_nonneg (q-t), mul_nonneg (sub_nonneg.mpr htq) (by linarith : 0 ≤ 2-q-t)]
  obtain ⟨w, hw⟩ := tangent_bad_subset e v hev ht hh
  have hmono := measureReal_mono hw (measure_ne_top (σ n) _)
  have heq : (σ n).real (halfcap w.val q) = (σ n).real (halfcap e.val q) := by
    exact congrArg ENNReal.toReal (halfcap_equal_norm ((mem_sphere_zero_iff_norm.mp w.property).trans
      (mem_sphere_zero_iff_norm.mp e.property).symm) q)
  rw [heq] at hmono
  have hrat := (halfcap_ratio e hl hu hlt htq hqu).2
  have htpos : 0 < (σ n).real (halfcap e.val t) :=
    ENNReal.toReal_pos (ne_of_gt (halfcap_positive e ht1)) (measure_ne_top _ _)
  have hcoef : ((1/l+1/(1-u^2))-(n:ℝ)*l)*(q-t) ≤ -(n:ℝ)*l*h^2/4 := by
    have hn0 : 0 ≤ (n:ℝ)*l := mul_nonneg (Nat.cast_nonneg n) hl.le
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hgap),
      mul_nonneg (by linarith : 0 ≤ (n:ℝ)*l/2-(1/l+1/(1-u^2))) (sub_nonneg.mpr htq)]
  exact hmono.trans (((div_le_iff₀ htpos).mp hrat).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcoef) htpos.le))

lemma common_lens {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I]
    (e : Sphere n) (v : I → Sphere n) (a b τ : I → ℝ)
    (hv : ∀ i, inner ℝ e.val (v i).val = 0)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i)
    {l u t h : ℝ} (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hτ : ∀ i, τ i ≤ a i*t-b i*h) :
    (1-(Fintype.card I : ℝ)*Real.exp (-(n:ℝ)*l*h^2/4)) *
      (σ n).real (halfcap e.val t) ≤
      (σ n).real (⋂ i, halfcap (a i • e.val + b i • (v i).val) (τ i)) := by
  let B : I → Set (Sphere n) := fun i => halfcap e.val t ∩
    {w : Sphere n | inner ℝ w.val (v i).val < -h}
  have hBm (i : I) : MeasurableSet (B i) := (halfcap_measurable _ _).inter
    (isOpen_lt (continuous_subtype_val.inner continuous_const) continuous_const).measurableSet
  have hsub : (⋃ i, B i) ⊆ halfcap e.val t := iUnion_subset fun _ => inter_subset_left
  have hlens : halfcap e.val t \ (⋃ i, B i) ⊆
      ⋂ i, halfcap (a i • e.val + b i • (v i).val) (τ i) := by
    intro w hw
    simp only [mem_iInter]
    intro i
    have hwi : -h ≤ inner ℝ w.val (v i).val := by
      by_contra hn
      exact hw.2 (mem_iUnion.mpr ⟨i, hw.1, lt_of_not_ge hn⟩)
    change τ i < inner ℝ w.val (a i • e.val + b i • (v i).val)
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have hwa : a i*t < a i*inner ℝ w.val e.val := mul_lt_mul_of_pos_left hw.1 (ha i)
    have hwb := mul_le_mul_of_nonneg_left hwi (hb i)
    linarith [hτ i]
  have hsum : (σ n).real (⋃ i, B i) ≤
      (Fintype.card I : ℝ)*Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) := by
    calc
      _ ≤ ∑ i, (σ n).real (B i) := measureReal_iUnion_fintype_le B
      _ ≤ ∑ _i : I, Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) :=
        Finset.sum_le_sum fun i _ => tangent_bad_measure e (v i) (hv i) hl hu hlt hh hqu hdim
      _ = _ := by simp; ring
  have hmon := measureReal_mono hlens (measure_ne_top (σ n) _)
  rw [measureReal_sdiff hsub (MeasurableSet.iUnion hBm)] at hmon
  linarith

end CapLens

end OAI
