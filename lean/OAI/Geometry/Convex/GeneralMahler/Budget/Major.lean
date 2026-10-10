import OAI.Geometry.Convex.GeneralMahler.Budget.Roots

namespace OAI
/-! Piecewise kernel square estimates will use these scaled integrable
majorants. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Roots
open Classical
def slab (f g:ℝ→ℝ) (t:ℝ) :=
  if t<0 then f (-t) else if t≤1 then g t else f (t-1)
def U (f g:ℝ→ℝ) (x y z:ℝ) :=
  |y-x| *slab f g ((z-min x y)/ |y-x|)

lemma slab_int (f g:ℝ→ℝ) (hf:IntegrableOn f (Ioi 0))
    (hg:Continuous g) :
    Integrable (slab f g) ∧ (∫ x,slab f g x)=(2*∫ x in Ioi 0,f x)+∫ x in Icc 0 1,g x := by
  let l := (Ioi 0).indicator f
  let k := (Icc 0 1).indicator g
  have hl : Integrable l := (integrable_indicator_iff measurableSet_Ioi).mpr hf
  have hk : Integrable k := (integrable_indicator_iff measurableSet_Icc).mpr hg.integrableOn_Icc
  have hi : Integrable (fun x=>l (-x)) :=
    ((measurePreserving_neg volume).integrable_comp_emb (Homeomorph.neg _).measurableEmbedding).mpr hl
  have hh : Integrable (fun x=>l (x-1)) := by
    simpa [sub_eq_add_neg] using hl.comp_add_right (-1)
  have he : slab f g=fun x=> l (-x)+k x+l (x-1) := by
    ext x
    unfold l k slab
    by_cases h:x<0
    · simp [h,indicator,show ¬0≤x by linarith,show ¬0<x-1 by linarith]
    by_cases ht:x≤1
    · simp [h,ht, indicator, show 0≤x by linarith, show ¬0<x-1 by linarith]
    simp [h,ht,indicator,show 0<x-1 by linarith]
  rw [he]
  refine ⟨(hi.add hk).add hh,?_⟩
  rw [integral_add,integral_add hi hk, integral_neg_eq_self, integral_sub_right_eq_self]
  · unfold l k
    simp_rw [integral_indicator measurableSet_Ioi,integral_indicator measurableSet_Icc]; ring
  all_goals first | exact hi.add hk | exact hh

lemma secU (f:ℝ→ℝ) (q:ℝ) {a:ℝ} (ha:0<a) (hf:Integrable f) :
    Integrable (fun z=>a*f ((z-q)/a)) ∧ (∫ z:ℝ,a*f ((z-q)/a))=a^2*∫ x,f x := by
  have h : Integrable (fun z=> f (z/a)) :=
    by simp_rw [div_eq_mul_inv]; exact (integrable_comp_mul_right_iff f (inv_pos.mpr ha).ne').2 hf
  let l := fun z:ℝ=>f (z/a)
  have hi : Integrable (fun z=>l (z-q)) := by simpa [l,sub_eq_add_neg] using h.comp_add_right (-q)
  constructor
  · exact hi.const_mul _
  rw [integral_const_mul]
  have ht : (∫ z:ℝ,l (z-q))=∫ z,l z := integral_sub_right_eq_self l q
  change a*(∫ z,l (z-q))=_
  rw [ht]
  unfold l
  rw [Measure.integral_comp_div]
  simp [abs_of_pos ha]; ring
lemma U_area (f g:ℝ→ℝ) (hf:IntegrableOn f (Ioi 0)) (hg:Continuous g) (x y:ℝ) :
    Integrable (U f g x y) ∧ (∫ z,U f g x y z)=(x-y)^2*((2*∫ t in Ioi 0,f t)+∫ t in Icc 0 1,g t) := by
  by_cases h:x=y
  · subst y; rw [show U f g x x=(fun _ => (0:ℝ)) from by ext; simp [U] ]; simp
  have hu := secU (slab f g) (min x y) (show 0< |y-x| from abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))) (slab_int f g hf hg).1
  unfold U; convert hu using 1
  rw [sq_abs, (slab_int f g hf hg).2]; ring_nf

def gx (t:ℝ) := 2*(1-2*t)^2
lemma g_area : (∫ x in Icc (0:ℝ) 1,gx x)=2/3 := by
  let F := fun t:ℝ=>2*t-4*t^2+8/3*t^3
  have hd (x:ℝ) : HasDerivAt F (gx x) x := by
    convert ((((hasDerivAt_id' x).const_mul 2).sub (((hasDerivAt_id' x).pow 2).const_mul 4)).add
      (((hasDerivAt_id' x).pow 3).const_mul (8/3))) using 1
    all_goals first | rfl | (norm_num [F,gx]; ring)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=>hd x) ((by unfold gx; fun_prop :
      Continuous gx).intervalIntegrable ..)]
  unfold F; ring

def Ux := U xk gx
def Uy := U yk (fun _=>1/2)
lemma Ux_area (x y:ℝ) :
    Integrable (Ux x y) ∧ (∫ z,Ux x y z)=(2*Real.log 2-1/3)*(x-y)^2 := by
  have h := U_area _ _ x_area.1 (by unfold gx; fun_prop : Continuous gx) x y
  rw [x_area.2,g_area] at h; exact ⟨h.1,h.2.trans (by ring)⟩
lemma Uy_area (x y:ℝ) :
    Integrable (Uy x y) ∧ (∫ z,Uy x y z)=(Real.log 2+1/4)*(x-y)^2 := by
  have h := U_area _ (fun _=>1/2) y_area.1 continuous_const x y
  rw [y_area.2,setIntegral_const] at h; refine ⟨h.1,h.2.trans ?_⟩
  norm_num; ring
lemma U_swap (f g) (x y z) : U f g x y z=U f g y x z := by rw [U,U,abs_sub_comm,min_comm]
lemma U_outHi (f g) {x y z:ℝ} (hx:x<y) (hy:y<z) :
    U f g x y z=(y-x)*f ((z-y)/(y-x)) := by
  have h:= sub_pos.mpr hx
  have he : 1<(z-x)/(y-x) := by rw [lt_div_iff₀ h]; linarith
  rw [U,abs_of_pos h,min_eq_left hx.le,slab,ite_eq_right (by linarith),ite_eq_right (by linarith)]
  congr 2; field_simp; ring
lemma U_outLo (f g) {x y z:ℝ} (hx:x<y) (hy:z<x) :
    U f g x y z=(y-x)*f ((x-z)/(y-x)) := by
  have h:= sub_pos.mpr hx
  rw [U,abs_of_pos h,min_eq_left hx.le,slab,ite_eq_left (div_neg_of_neg_of_pos (sub_neg.mpr hy) h)]
  congr 2; ring
lemma U_mid (f g) {x y z:ℝ} (hx:x<z) (hy:z<y) :
    U f g x y z=(y-x)*g ((z-x)/(y-x)) := by
  have h:= sub_pos.mpr (hx.trans hy)
  rw [U,abs_of_pos h,min_eq_left (by linarith),slab,
    ite_eq_right (not_lt_of_ge (div_nonneg (by linarith) h.le)),ite_eq_left]; rw [div_le_iff₀ h]; linarith
end GeneralMahler.Roots

end

end OAI
