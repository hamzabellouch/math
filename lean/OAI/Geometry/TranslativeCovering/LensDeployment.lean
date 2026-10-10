import OAI.Geometry.TranslativeCovering.NormalizedCaps

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

universe u_1 u_2

namespace LensDeployment
open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens CapCost CapAffinity
open scoped ENNReal NNReal

lemma tangent_bad_vector {n : ℕ} [NeZero n] (e : Sphere n) (v : Space n)
    (hev : inner ℝ e.val v = 0) {l u t h Φ : ℝ}
    (hΦ : ‖v‖ ≤ Φ) (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v < -Φ*h}) ≤
      Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) := by
  by_cases hv : v = 0
  · have hΦ0 : 0 ≤ Φ := (norm_nonneg v).trans hΦ
    have hem : halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v < -Φ*h} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro w ⟨_,hw⟩
      simp only [mem_ofPred_eq,hv,inner_zero_right] at hw
      nlinarith
    rw [hem,measureReal_empty]
    positivity
  · have hvp := norm_pos_iff.mpr hv
    have hsub : halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val v < -Φ*h} ⊆
        halfcap e.val t ∩ {w : Sphere n | inner ℝ w.val (unit v hv).val < -h} := by
      rintro w ⟨hw1,hw2⟩
      refine ⟨hw1,?_⟩
      change inner ℝ w.val (unit v hv).val < -h
      rw [inner_unit,div_lt_iff₀ hvp]
      have hm := mul_le_mul_of_nonneg_right hΦ hh
      exact hw2.trans_le (by nlinarith)
    exact (measureReal_mono hsub).trans (tangent_bad_measure e (unit v hv)
      (by rw [inner_unit,hev,zero_div]) hl hu hlt hh hqu hdim)

lemma projected_norm {n : ℕ} (e f : Sphere n) :
    ‖f.val-(inner ℝ e.val f.val) • e.val‖^2 = 1-(inner ℝ e.val f.val)^2 := by
  have he := mem_sphere_zero_iff_norm.mp e.property
  have hf := mem_sphere_zero_iff_norm.mp f.property
  rw [norm_sub_sq_real, norm_smul,Real.norm_eq_abs,he,hf,inner_smul_right,real_inner_comm f.val e.val]
  simp only [mul_one,one_pow,sq_abs]
  ring

lemma projected_bound {n : ℕ} (e f : Sphere n) {Φ : ℝ}
    (hΦ : 0 ≤ Φ) (hangle : InnerProductGeometry.angle e.val f.val ≤ Φ) :
    1-Φ^2/2 ≤ inner ℝ e.val f.val ∧
      ‖f.val-(inner ℝ e.val f.val) • e.val‖ ≤ Φ := by
  have he := mem_sphere_zero_iff_norm.mp e.property
  have hf := mem_sphere_zero_iff_norm.mp f.property
  have ha := InnerProductGeometry.angle_nonneg e.val f.val
  have hsq := pow_le_pow_left₀ ha hangle 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := InnerProductGeometry.angle e.val f.val)
  have hacos := InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one he hf
  have hac : inner ℝ e.val f.val ≤ 1 := by rw [hacos]; exact Real.cos_le_one _
  have ha0 : -1 ≤ inner ℝ e.val f.val := by rw [hacos]; exact Real.neg_one_le_cos _
  have hlow : 1-Φ^2/2 ≤ inner ℝ e.val f.val := by rw [hacos]; linarith
  refine ⟨hlow,?_⟩
  have hn := projected_norm e f
  have hs : 1-(inner ℝ e.val f.val)^2 ≤ Φ^2 := by
    nlinarith [sq_nonneg (inner ℝ e.val f.val-1)]
  nlinarith [norm_nonneg (f.val-(inner ℝ e.val f.val) • e.val)]

lemma ordinary_lens {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I]
    (e : Sphere n) (f : I → Sphere n) (τ : I → ℝ) {l u t h Φ : ℝ}
    (hΦ : 0 ≤ Φ) (hΦsmall : Φ^2 < 2)
    (hangle : ∀ i,InnerProductGeometry.angle e.val (f i).val ≤ Φ)
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hτ : ∀ i,τ i ≤ t-Φ^2/2-Φ*h) :
    (1-(Fintype.card I:ℝ)*Real.exp (-(n:ℝ)*l*h^2/4))*(σ n).real (halfcap e.val t) ≤
      (σ n).real (⋂ i,halfcap (f i).val (τ i)) := by
  let a := fun i => inner ℝ e.val (f i).val
  let v := fun i => (f i).val-a i • e.val
  have hv (i : I) : inner ℝ e.val (v i) = 0 := by
    dsimp [v,a]
    rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp e.property]
    ring
  have hb (i : I) := projected_bound e (f i) hΦ (hangle i)
  have hap (i : I) : 0 < a i := by dsimp [a]; linarith [(hb i).1]
  have ht0 : 0 < t := hl.trans_le hlt
  have ht1 : t < 1 := by
    have hsq := Real.sq_sqrt (show 0 ≤ t^2+h^2 by positivity)
    have htq : t ≤ Real.sqrt (t^2+h^2) := by nlinarith [Real.sqrt_nonneg (t^2+h^2),sq_nonneg h]
    exact (htq.trans hqu).trans_lt hu
  have hti (i : I) : τ i ≤ a i*t-Φ*h := by
    have hmul := mul_le_mul_of_nonneg_right (hb i).1 ht0.le
    have hh2 := mul_le_mul_of_nonneg_left ht1.le (sq_nonneg Φ)
    dsimp [a]
    nlinarith [hτ i]
  let B : I → Set (Sphere n) := fun i => halfcap e.val t ∩ {w | inner ℝ w.val (v i) < -Φ*h}
  have hBm (i : I) : MeasurableSet (B i) := (halfcap_measurable _ _).inter
    (isOpen_lt (continuous_subtype_val.inner continuous_const) continuous_const).measurableSet
  have hsub : (⋃ i,B i) ⊆ halfcap e.val t := iUnion_subset fun _ => inter_subset_left
  have hlens : halfcap e.val t \ (⋃ i,B i) ⊆ ⋂ i,halfcap (f i).val (τ i) := by
    rintro w ⟨hw,hwB⟩
    apply mem_iInter.mpr
    intro i
    have hwv : -Φ*h ≤ inner ℝ w.val (v i) := by
      by_contra hh
      exact hwB (mem_iUnion.mpr ⟨i,hw,lt_of_not_ge hh⟩)
    change τ i < inner ℝ w.val (f i).val
    have heq : (f i).val = a i • e.val+v i := by dsimp [v]; abel
    rw [heq,inner_add_right,inner_smul_right]
    have hmm := mul_lt_mul_of_pos_left hw (hap i)
    linarith [hti i]
  have hsum : (σ n).real (⋃ i,B i) ≤
      (Fintype.card I:ℝ)*Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) := by
    calc
      _ ≤ ∑ i,(σ n).real (B i) := measureReal_iUnion_fintype_le B
      _ ≤ ∑ _i : I,Real.exp (-(n:ℝ)*l*h^2/4)*(σ n).real (halfcap e.val t) :=
        Finset.sum_le_sum fun i _ => tangent_bad_vector e (v i) (hv i) (hb i).2 hl hu hlt hh hqu hdim
      _ = _ := by simp; ring
  have hm := measureReal_mono (μ := σ n) hlens
  rw [measureReal_sdiff hsub (MeasurableSet.iUnion hBm)] at hm
  linarith

lemma orient_axis {n : ℕ} (e f : Sphere n) :
    ∃ g : Sphere n, (∀ t,cap g.val t = cap f.val t) ∧
      InnerProductGeometry.angle e.val g.val = ProjectiveCaps.angle e.val f.val := by
  by_cases h : InnerProductGeometry.angle e.val f.val ≤ InnerProductGeometry.angle e.val (-f.val)
  · exact ⟨f,fun _ => rfl,(min_eq_left h).symm⟩
  · refine ⟨⟨-f.val,by simpa only [mem_sphere_zero_iff_norm,norm_neg] using f.property⟩,?_,?_⟩
    · intro t; ext w; simp [cap,inner_neg_right,abs_neg]
    · exact (min_eq_right (le_of_not_ge h)).symm

lemma projective_lens {n : ℕ} [NeZero n] {I : Type u_2} [Fintype I]
    (e : Sphere n) (f : I → Sphere n) (τ : I → ℝ) {l u t h Φ : ℝ}
    (hΦ : 0 ≤ Φ) (hΦsmall : Φ^2 < 2)
    (hangle : ∀ i,ProjectiveCaps.angle e.val (f i).val ≤ Φ)
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hh : 0 ≤ h)
    (hqu : Real.sqrt (t^2+h^2) ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hτ : ∀ i,τ i ≤ t-Φ^2/2-Φ*h) :
    (1-(Fintype.card I:ℝ)*Real.exp (-(n:ℝ)*l*h^2/4))*(σ n).real (halfcap e.val t) ≤
      (σ n).real (⋂ i,cap (f i).val (τ i)) := by
  choose g hg hang using fun i => orient_axis e (f i)
  apply (ordinary_lens e g τ hΦ hΦsmall (fun i => by rw [hang i]; exact hangle i)
    hl hu hlt hh hqu hdim hτ).trans
  apply measureReal_mono (μ := σ n)
  intro w hw
  apply mem_iInter.mpr
  intro i
  rw [← hg i (τ i)]
  change τ i < |inner ℝ w.val (g i).val|
  exact lt_of_lt_of_le (show τ i < inner ℝ w.val (g i).val from mem_iInter.mp hw i) (le_abs_self _)

end LensDeployment

end OAI
