import OAI.Geometry.TranslativeCovering.ProjectiveCaps

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

namespace CapAffinity
open Set MeasureTheory Metric SphericalLaw CapGeometry CapOverlap

lemma chord_angle {n : ℕ} (e f : Sphere n) :
    (4/Real.pi^2) * (InnerProductGeometry.angle e.val f.val)^2 ≤ ‖e.val-f.val‖^2 := by
  have he := mem_sphere_zero_iff_norm.mp e.property
  have hf := mem_sphere_zero_iff_norm.mp f.property
  have ha := InnerProductGeometry.angle_nonneg e.val f.val
  have hb := InnerProductGeometry.angle_le_pi e.val f.val
  have hc := Real.cos_le_one_sub_mul_cos_sq (by rw [abs_of_nonneg ha]; exact hb)
  rw [norm_sub_sq_real, he, hf,
    InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one he hf]
  ring_nf at hc ⊢
  linarith

lemma halfcap_overlap {n : ℕ} [NeZero n] (e f : Sphere n)
    {l u U t s k : ℝ} (hl : 0 < l) (hU : U < 1)
    (hlt : l ≤ t) (htu : t ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val t ∩ halfcap f.val s) ≤
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2/2) *
        Real.sqrt ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)) := by
  have hsq : ((σ n).real (halfcap e.val t ∩ halfcap f.val s))^2 ≤
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2) *
        (σ n).real (halfcap e.val t) * (σ n).real (halfcap f.val s) := by
    rcases le_total t s with hts | hst
    · exact halfcap_overlap_sq_ordered e f hl hU hlt hts hsu huU hk hkl hku hdim
    · have hh := halfcap_overlap_sq_ordered f e hl hU hls hst htu huU hk hkl hku hdim
      rw [inter_comm, norm_sub_rev] at hh
      nlinarith [hh]
  have he : (Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2/2))^2 =
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hh : 0 ≤ Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2/2) *
      Real.sqrt ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)) := by positivity
  nlinarith [sq_nonneg ((σ n).real (halfcap e.val t ∩ halfcap f.val s)),
    show (Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2/2) *
      Real.sqrt ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)))^2 =
      Real.exp (-(n:ℝ)*l*k*‖e.val-f.val‖^2)*
        ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)) by
        rw [mul_pow, he, Real.sq_sqrt (by positivity)]]

noncomputable def signed {n : ℕ} (e : Sphere n) (b : Bool) : Sphere n :=
  if b then e else ⟨-e.val, by simpa only [mem_sphere_zero_iff_norm, norm_neg]
    using mem_sphere_zero_iff_norm.mp e.property⟩

lemma halfcap_signed_mass {n : ℕ} (e : Sphere n) (b : Bool) (t : ℝ) :
    σ n (halfcap (signed e b).val t) = σ n (halfcap e.val t) :=
  halfcap_equal_norm ((mem_sphere_zero_iff_norm.mp (signed e b).property).trans
    (mem_sphere_zero_iff_norm.mp e.property).symm) t

lemma cap_eq_union {n : ℕ} (e : Sphere n) (t : ℝ) :
    cap e.val t = ⋃ b : Bool, halfcap (signed e b).val t := by
  ext w
  simp only [cap, halfcap, mem_ofPred_eq, mem_iUnion, Bool.exists_bool,
    signed, Bool.false_eq_true, ↓reduceIte, inner_neg_right]
  exact lt_abs.trans (by tauto)

lemma cap_mass {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : 0 ≤ t) :
    (σ n).real (cap e.val t) = 2*(σ n).real (halfcap e.val t) := by
  rw [cap_eq_union]
  have he : (⋃ b : Bool, halfcap (signed e b).val t) =
      halfcap (signed e false).val t ∪ halfcap (signed e true).val t := by
    ext w; simp only [mem_iUnion, Bool.exists_bool, mem_union]
  rw [he]
  have hd : Disjoint (halfcap (signed e false).val t) (halfcap (signed e true).val t) := by
    apply disjoint_left.mpr
    intro w hw1 hw2
    change t < inner ℝ w.val (-e.val) at hw1
    rw [inner_neg_right] at hw1
    change t < inner ℝ w.val e.val at hw2
    linarith
  rw [measureReal_union hd (halfcap_measurable _ _), measureReal_def, halfcap_signed_mass]
  change (σ n).real (halfcap e.val t) + (σ n).real (halfcap e.val t) = _
  ring

lemma projective_le_signed {n : ℕ} (e f : Sphere n) (a b : Bool) :
    ProjectiveCaps.angle e.val f.val ≤
      InnerProductGeometry.angle (signed e a).val (signed f b).val := by
  cases a <;> cases b <;> dsimp [signed, ProjectiveCaps.angle]
  · rw [InnerProductGeometry.angle_neg_neg]
    exact min_le_left _ _
  · rw [InnerProductGeometry.angle_neg_left, ← InnerProductGeometry.angle_neg_right]
    exact min_le_right _ _
  · exact min_le_right _ _
  · exact min_le_left _ _

lemma doublecap_overlap {n : ℕ} [NeZero n] (e f : Sphere n)
    {l u U t s k : ℝ} (hl : 0 < l) (hU : U < 1)
    (hlt : l ≤ t) (htu : t ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) :
    (σ n).real (cap e.val t ∩ cap f.val s) ≤
      2*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(ProjectiveCaps.angle e.val f.val)^2) *
        Real.sqrt ((σ n).real (cap e.val t)*(σ n).real (cap f.val s)) := by
  let E := Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(ProjectiveCaps.angle e.val f.val)^2)
  let F := Real.sqrt ((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s))
  have hbound (a b : Bool) :
      (σ n).real (halfcap (signed e a).val t ∩ halfcap (signed f b).val s) ≤ E*F := by
    have hh := halfcap_overlap (signed e a) (signed f b) hl hU hlt htu hls hsu huU hk hkl hku hdim
    have hm : Real.sqrt ((σ n).real (halfcap (signed e a).val t)*
        (σ n).real (halfcap (signed f b).val s)) = F := by
      simp only [measureReal_def, halfcap_signed_mass, F]
    rw [hm] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    have hc := chord_angle (signed e a) (signed f b)
    have hp := pow_le_pow_left₀ (ProjectiveCaps.angle_nonneg e.val f.val)
      (projective_le_signed e f a b) 2
    have hp2 := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 4/Real.pi^2)
    have hn : 0 ≤ (n:ℝ)*l*k := by positivity
    have hprod := mul_nonneg hn (sub_nonneg.mpr (hp2.trans hc))
    change -(n:ℝ)*l*k*‖(signed e a).val-(signed f b).val‖^2/2 ≤
      -(n:ℝ)*(2*l*k/Real.pi^2)*(ProjectiveCaps.angle e.val f.val)^2
    ring_nf at hprod ⊢
    nlinarith
  have heq : cap e.val t ∩ cap f.val s =
      ⋃ p : Bool × Bool, halfcap (signed e p.1).val t ∩ halfcap (signed f p.2).val s := by
    rw [cap_eq_union, cap_eq_union]
    ext w
    simp only [mem_inter_iff, mem_iUnion, Prod.exists]
    aesop
  have hb : (σ n).real (cap e.val t ∩ cap f.val s) ≤ 4*E*F := by
    rw [heq]
    calc
      _ ≤ ∑ p : Bool × Bool, (σ n).real (halfcap (signed e p.1).val t ∩
        halfcap (signed f p.2).val s) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : Bool × Bool, E*F := Finset.sum_le_sum fun p _ => hbound p.1 p.2
      _ = _ := by simp; ring
  have hm : Real.sqrt ((σ n).real (cap e.val t)*(σ n).real (cap f.val s)) = 2*F := by
    rw [cap_mass e (hl.trans_le hlt).le, cap_mass f (hl.trans_le hls).le]
    have he : (2*(σ n).real (halfcap e.val t))*(2*(σ n).real (halfcap f.val s)) =
        (2:ℝ)^2*((σ n).real (halfcap e.val t)*(σ n).real (halfcap f.val s)) := by ring
    rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hm]
  convert hb using 1; ring

end CapAffinity

end OAI
