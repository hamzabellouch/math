import OAI.Geometry.Convex.GeneralMahler.Kernel

namespace OAI
/-! Eq13 mixed derivative kernel, proof via rectangle cumulative
representation of a(min)B(max). -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers Profile
namespace rightLayer
variable (q:rightLayer)

lemma B_c : Continuous q.B :=
  continuous_iff_continuousAt.mpr fun x=>(q.drB x).continuousAt
lemma K_c : Continuous q.Km :=
  (cp.comp (by fun_prop)).mul (q.hc.comp (by fun_prop))
lemma K_nn (u) : 0≤q.Km u := mul_nonneg (p_pos _).le (q.hr _)

def Kab (u:Plane) := a (min u.1 u.2)*q.B (max u.1 u.2)

def Rect (u:Plane) : Set Plane := (Icc u.1 u.2) ×ˢ Icc u.1 u.2
lemma rcompact (u:Plane) : IsCompact (Rect u) := isCompact_Icc.prod isCompact_Icc
lemma concat_m : MeasurableSet ({p:Plane×Plane| p.2∈Rect p.1}) := by
  let f : Plane × Plane→Plane := Prod.fst
  let g : Plane × Plane→Plane := Prod.snd
  let D : ℕ→Plane × Plane→ℝ := fun i=> if i=0 then Prod.fst ∘ f else if i=1 then Prod.snd ∘ f else if i=2 then Prod.fst ∘ g else Prod.snd ∘ g
  have hi (i j : ℕ) : MeasurableSet {p|D i p ≤ D j p} := by
    unfold D f g; split_ifs <;> exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  exact ((hi 0 2).inter (hi 2 1)).inter ((hi 0 3).inter (hi 3 1))

open Classical in
def RectF (f:Plane→ℝ) (p:Plane×Plane) := if p.2∈Rect p.1 then q.Km p.1*f p.2 else 0
lemma rect_slice_i (f:Plane→ℝ) (hf:Continuous f) (u:Plane) :
    Integrable fun v=> q.RectF f (u,v) := by
  classical
  have he : (fun v=>q.RectF f (u,v))=(Rect u).indicator (fun v=>q.Km u*f v) := by ext v; rfl
  rw [he]
  exact (integrable_indicator_iff (rcompact u).measurableSet).mpr
    ((continuous_const.mul hf).continuousOn.integrableOn_compact (rcompact u))

lemma Rect_bound (u v:Plane) (h:v∈Rect u) : ‖v‖ ≤ ‖u‖ := by
  have he : (u.1≤v.1 ∧ v.1≤u.2)∧(u.1≤v.2∧v.2≤u.2) := h
  change max ‖v.1‖ ‖v.2‖ ≤ max ‖u.1‖ ‖u.2‖
  simp_rw [Real.norm_eq_abs]; grind
lemma length_rect (u:Plane) :
    volume.real (Rect u) ≤ 4*‖u‖^2 := by
  change ((volume.prod volume) ((Icc u.1 u.2) ×ˢ Icc u.1 u.2)).toReal ≤ _
  rw [prod_prod,ENNReal.toReal_mul]
  change volume.real (Icc u.1 u.2)*volume.real (Icc u.1 u.2) ≤ _
  rw [Real.volume_real_Icc]
  have h : max (u.2-u.1) 0 ≤ 2*‖u‖ := by
    change _≤2*max ‖u.1‖ ‖u.2‖
    simp only [Real.norm_eq_abs]; grind
  nlinarith [norm_nonneg u,le_max_right (u.2-u.1) (0:ℝ)]
lemma Rect_int {f:Plane→ℝ} (hp:PolyBound f) (hf:Continuous f) :
    Integrable (q.RectF f) := by
  classical
  have hm : Measurable (q.RectF f) := Measurable.ite concat_m
    ((q.K_c.measurable.comp measurable_fst).mul (hf.measurable.comp measurable_snd)) measurable_const
  rw [show (volume:Measure (Plane×Plane))=volume.prod volume from rfl]
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (q.rect_slice_i f hf),?_⟩
  obtain ⟨C,n,hc,h⟩ := hp
  let g : Plane→ℝ := fun u=> C*(1+‖u‖)^n
  have hp : PolyBound (fun u:Plane=> (4*‖u‖^2)*g u) :=
    ((PolyBound.const _).mul (PolyBound.id.norm.pow _)).mul
      ((PolyBound.const _).mul (((PolyBound.const _).add PolyBound.id.norm).pow n))
  have hi := q.K_pair hp (by unfold g; fun_prop)
  refine hi.mono' ?_ (ae_of_all _ fun x=>?_ )
  · exact ((hm.stronglyMeasurable.norm).integral_prod_right').aestronglyMeasurable
  · let R := fun u=> ‖q.RectF f (x,u)‖
    change ‖∫ u,R u‖≤_
    rw [Real.norm_of_nonneg (integral_nonneg (fun _=> norm_nonneg _))]
    have he : R=(Rect x).indicator fun u=> q.Km x*‖f u‖ := by
      funext u; unfold R RectF; by_cases h:u∈Rect x
      · simp only [ite_eq_left h,indicator_of_mem h,norm_mul,Real.norm_of_nonneg (q.K_nn x)]
      simp only [ite_eq_right h,indicator_of_notMem h,norm_zero]
    change ∫ u,R u≤ _
    rw [he,integral_indicator (rcompact x).measurableSet]
    have hu : (∫ u in Rect x,q.Km x*‖f u‖) ≤ ∫ u:Plane in Rect x,q.Km x*g x := by
      apply setIntegral_mono_on
        (((continuous_const.mul hf.norm).continuousOn).integrableOn_compact (rcompact x))
        (continuous_const.continuousOn.integrableOn_compact (rcompact x)) (rcompact x).measurableSet
      intro y hy
      apply mul_le_mul_of_nonneg_left _ (q.K_nn _)
      apply (h y).trans
      unfold g; gcongr; exact Rect_bound x y hy
    apply hu.trans
    rw [setIntegral_const,smul_eq_mul]
    have hx : 0 ≤ g x := by unfold g; positivity
    have hi := mul_le_mul_of_nonneg_right (length_rect x) (mul_nonneg (q.K_nn x) hx)
    linarith

lemma slice_rect_a (v:Plane) (f:Plane→ℝ) :
    (∫ u:Plane,q.RectF f (u,v))=q.Kab v*f v := by
  classical
  set x := min v.1 v.2
  set y := max v.1 v.2
  let g := (Iic x).indicator p; let h := (Ici y).indicator q.r
  have he : (fun u=>q.RectF f (u,v))=fun u:Plane=> (g u.1*h u.2)*f v := by
    ext u
    by_cases H:u.1≤x
    · by_cases W:y≤u.2
      · have hh : v∈Rect u := by
          change (u.1≤v.1 ∧ v.1≤u.2)∧(u.1≤v.2 ∧ v.2≤u.2); grind
        have hi : u.1≤u.2 := by grind
        simp [g,h,RectF,hh,Km,H,W,hi]
      have hh : v∉Rect u := by change ¬((u.1≤v.1 ∧ v.1≤u.2)∧(u.1≤v.2 ∧ v.2≤u.2)); grind
      simp [g,h,RectF,hh,W]
    have hh : v∉Rect u := by change ¬((u.1≤v.1 ∧ v.1≤u.2)∧(u.1≤v.2 ∧ v.2≤u.2)); grind
    simp [g,h,RectF,hh,H]
  rw [he,integral_mul_const]
  congr 1
  rw [show (volume:Measure Plane)=volume.prod volume from rfl,integral_prod_mul]
  unfold g h; rw [integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi,(q.r_slice y).2,(p_slice x).2]; rfl

lemma Kab_I {f:Plane→ℝ} (hf:Continuous f) (h:PolyBound f) :
    Integrable fun u=>q.Kab u*f u := by
  simp_rw [← q.slice_rect_a]
  exact (q.Rect_int h hf).integral_prod_right
lemma R_reverse {f:Plane→ℝ} (hf:Continuous f) (h:PolyBound f) :
    (∫ u,q.Kab u*f u)=∫ u:Plane,q.Km u*∫ v in Rect u,f v := by
  simp_rw [← q.slice_rect_a]
  rw [integral_integral_swap]
  · congr 1; ext u; rw [← integral_const_mul,← integral_indicator (rcompact u).measurableSet]
    rfl
  exact (q.Rect_int h hf).swap

lemma mrgMul {f:ℝ→ℝ} (hf:TestF f) :
    (∫ u:Plane,q.Km u*f u.1)= ∫ x,q.mrg x*f x := by
  rw [show (volume:Measure Plane)=volume.prod volume from rfl,integral_prod]
  · simp_rw [integral_mul_const]
    congr 1; ext x; rw [(q.marg x).2]
  exact q.K_pair (hf.poly.comp PolyBound.fst) (hf.cont.measurable.comp measurable_fst)

lemma R_identity {f g:ℝ→ℝ} (hf:TestF f) (hg:TestF g) :
    (∫ u:Plane,q.Kab u*(deriv f u.1*deriv g u.2))=
      (∫ x,q.mrg x*(f x*g x)) - q.Q f g := by
  classical
  rw [q.R_reverse (f:=fun u=>deriv f u.1*deriv g u.2) ((hf.der.cont.comp continuous_fst).mul (hg.der.cont.comp continuous_snd))
    ((hf.der.poly.comp PolyBound.fst).mul (hg.der.poly.comp PolyBound.snd))]
  let F := fun u:Plane=>q.Km u*(f u.1*g u.1) - q.Km u*(f u.1*g u.2)
  have hi : Integrable F :=
    (q.K_pair ((hf.poly.mul hg.poly).comp PolyBound.fst)
      ((hf.cont.mul hg.cont).measurable.comp measurable_fst)).sub (q.Q_int hf hg)
  have he : (∫ u:Plane,F u)=(∫ x,q.mrg x*(f x*g x))-q.Q f g := by
    unfold F Q; rw [integral_sub,q.mrgMul (hf.mul hg)]
    all_goals first | exact q.K_pair ((hf.poly.mul hg.poly).comp PolyBound.fst) ((hf.cont.mul hg.cont).measurable.comp measurable_fst) |
      exact q.Q_int hf hg
  rw [← he,split_plane F hi,
    ← integral_add (show Integrable F (volume.restrict Rlo) from hi.integrableOn) (show Integrable (fun u:Plane=>F u.swap) (volume.restrict Rlo) from hi.swap.integrableOn),
    ← integral_indicator Rlo_m]
  apply integral_congr_ae
  filter_upwards [off_diag] with u hu
  rcases lt_or_gt_of_ne hu with h|h
  · have hx:u∈Rlo := h
    rw [indicator_of_mem hx]
    unfold Rect
    rw [show (volume:Measure Plane)=volume.prod volume from rfl,← Measure.prod_restrict,integral_prod_mul]
    have h (f:ℝ→ℝ) (hf:TestF f) :
        (∫ a in Icc u.1 u.2,deriv f a)=f u.2-f u.1 := by
      rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le h.le]
      exact intervalIntegral.integral_deriv_eq_sub (fun a _=>hf.diff a) (hf.der.cont.intervalIntegrable ..)
    rw [h f hf,h g hg]; unfold F
    rw [show q.Km u.swap=q.Km u from by simp [Km,min_comm,max_comm]]
    change _ = q.Km u*_ -_ +(q.Km u*(f u.2*g u.2)-q.Km u*(f u.2*g u.1))
    ring
  have hx:u∉Rlo := not_lt_of_ge h.le
  rw [indicator_of_notMem hx]
  have hh : Rect u=∅ := by unfold Rect; rw [Icc_eq_empty_of_lt h]; simp
  simp [hh]

end rightLayer
end GeneralMahler

end

end OAI
