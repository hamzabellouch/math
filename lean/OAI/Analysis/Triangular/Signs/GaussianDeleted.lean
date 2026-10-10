import OAI.Analysis.Triangular.Construction.ActualInterpolation
import OAI.Analysis.Triangular.Signs.DeletedQuotient

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
lemma gaussianG_contDiff (z : ℝ) : ContDiff ℝ ⊤ (gaussianG z) := by unfold gaussianG; fun_prop
lemma gaussianG_second {z : ℝ} (hz : 0<z) (s : ℝ) :
    iteratedDeriv 2 (gaussianG z) s=Q 1/z*Real.exp ((1-s)/z) := by
  rw [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have he : deriv (gaussianG z)=fun t => -Q 1*Real.exp ((1-t)/z) := funext fun t => (gaussianG_deriv hz t).deriv
  rw [he]
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (-Q 1))
  convert hh.deriv using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)
lemma deletedSecond_lower {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (m s L : ℝ)
    (hb : ∀ t∈uIcc m s,L ≤ iteratedDeriv 2 f t/2) : L ≤ deletedSecond f m s := by
  by_cases hms : m=s
  · subst s
    simpa [deletedSecond] using hb m (left_mem_uIcc)
  · obtain ⟨c,hc,he⟩ := deletedSecond_eq_at_mean hf hms
    rw [he]
    exact hb c (Ioo_subset_Icc_self hc)
lemma gaussian_deleted_nonneg {z : ℝ} (hz : 0<z) (m v : ℝ) :
    0 ≤ deletedSecond (gaussianG z) m (m+v) := by
  apply deletedSecond_lower ((gaussianG_contDiff z).of_le (by norm_num))
  intro t _
  rw [gaussianG_second hz]
  exact div_nonneg (mul_nonneg (div_nonneg Q_one_pos.le hz.le) (Real.exp_pos _).le) (by norm_num)
lemma gaussian_deleted_left {z m v : ℝ} (hz : 0<z) (hv : v ≤ 0) :
    Q 1*Real.exp ((1-m)/z)/(2*z) ≤ deletedSecond (gaussianG z) m (m+v) := by
  apply deletedSecond_lower ((gaussianG_contDiff z).of_le (by norm_num))
  intro t ht
  have htm : t ≤ m := by
    have hh := ht.2
    rw [max_eq_left (by linarith : m+v ≤ m)] at hh
    exact hh
  rw [gaussianG_second hz]
  have he : Real.exp ((1-m)/z) ≤ Real.exp ((1-t)/z) := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) hz.le)
  have hh := mul_le_mul_of_nonneg_left he (div_nonneg Q_one_pos.le hz.le)
  convert div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 2) using 1; first | rfl | ring

def pade0 (x : ℝ) := Real.exp (-x)*(6+4*x+x^2)-6+2*x
def pade1 (x : ℝ) := 2-Real.exp (-x)*(2+2*x+x^2)
lemma pade0_deriv (x : ℝ) : HasDerivAt pade0 (pade1 x) x := by
  have he := ((hasDerivAt_id x).neg).exp
  have hp := (((hasDerivAt_const x (6:ℝ)).add ((hasDerivAt_id x).const_mul 4)).add ((hasDerivAt_id x).pow 2))
  have hh := ((he.mul hp).sub_const 6).add ((hasDerivAt_id x).const_mul 2)
  convert hh using 1 <;> first | rfl | (dsimp [pade1]; ring)
lemma pade1_deriv (x : ℝ) : HasDerivAt pade1 (x^2*Real.exp (-x)) x := by
  have he := ((hasDerivAt_id x).neg).exp
  have hp := (((hasDerivAt_const x (2:ℝ)).add ((hasDerivAt_id x).const_mul 2)).add ((hasDerivAt_id x).pow 2))
  have hh := (he.mul hp).const_sub 2
  convert hh using 1 <;> first | rfl | (dsimp; ring)
lemma pade1_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pade1 x := by
  have hm := monotone_of_hasDerivAt_nonneg pade1_deriv (fun t => mul_nonneg (sq_nonneg t) (Real.exp_pos _).le)
  have hh := hm hx
  simpa [pade1] using hh
lemma pade0_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ pade0 x := by
  have hm : MonotoneOn pade0 (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (by unfold pade0; fun_prop) (fun s _ => (pade0_deriv s).differentiableAt.differentiableWithinAt)
    (fun s hs => by rw [(pade0_deriv s).deriv]; exact pade1_nonneg (interior_subset hs))
  have hh := hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simpa [pade0] using hh
lemma pade_rational {x : ℝ} (hx : 0<x) :
    (3+x)/(6+4*x+x^2) ≤ (Real.exp (-x)-1+x)/x^2 := by
  have hd : 0<6+4*x+x^2 := by positivity
  rw [div_le_div_iff₀ hd (sq_pos_of_pos hx)]
  have hh := pade0_nonneg hx.le
  dsimp [pade0] at hh
  nlinarith
lemma gaussian_deleted_formula {z m v : ℝ} (hz : 0<z) (hv : v≠0) :
    deletedSecond (gaussianG z) m (m+v)=
      Q 1*z*Real.exp ((1-m)/z)*(Real.exp (-v/z)-1+v/z)/v^2 := by
  rw [deletedSecond,ite_eq_right (by intro hh; apply hv; linarith : m+v≠m),(gaussianG_deriv hz m).deriv]
  simp only [gaussianG]
  rw [show (1-(m+v))/z=(1-m)/z+(-v/z) by ring,Real.exp_add]
  field_simp [hz.ne',hv]
  ring
lemma gaussian_deleted_right {z m v : ℝ} (hz : 0<z) (hv : 0 ≤ v) :
    Q 1*Real.exp ((1-m)/z)*((3*z+v)/(6*z^2+4*z*v+v^2)) ≤
      deletedSecond (gaussianG z) m (m+v) := by
  rcases hv.eq_or_lt with hv|hv
  · subst v
    simp only [add_zero,deletedSecond,ite_true]
    rw [gaussianG_second hz]
    apply le_of_eq
    field_simp [hz.ne']
    ring
  · rw [gaussian_deleted_formula hz hv.ne']
    have hQ := Q_one_pos
    have hh := mul_le_mul_of_nonneg_left (pade_rational (div_pos hv hz))
      (show 0 ≤ Q 1*Real.exp ((1-m)/z)/z by positivity)
    have hz0 := hz.ne'
    have hv0 := hv.ne'
    have hd : 6*z^2+4*z*v+v^2≠0 := ne_of_gt (by positivity)
    convert hh using 1 <;> first | rfl | field_simp [hz0,hv0,hd]
lemma gaussian_deleted_three {z v : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hv : v ≤ 1/2) :
    (4/5)*Q 1*Real.exp (-2/z) ≤ deletedSecond (gaussianG z) 3 (3+v) := by
  have hzBound : z ≤ 391/1000 := hzB
  have hq : 0 ≤ Q 1*Real.exp (-2/z) := mul_nonneg Q_one_pos.le (Real.exp_pos _).le
  by_cases hv0 : v ≤ 0
  · have hh := gaussian_deleted_left (m:=3) hz hv0
    norm_num at hh
    have hr : (4/5:ℝ) ≤ 1/(2*z) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hl := mul_le_mul_of_nonneg_left hr hq
    have he : Q 1*Real.exp (-2/z)*(1/(2*z))=Q 1*Real.exp (-2/z)/(2*z) := by ring
    rw [he] at hl
    convert hl.trans hh using 1; first | rfl | ring
  · have hv0 : 0<v := lt_of_not_ge hv0
    have hd : 0<6*z^2+4*z*v+v^2 := by positivity
    have hz2 : z^2 ≤ (391/1000)*z := by nlinarith
    have hv2 : v^2 ≤ (1/2)*v := by nlinarith
    have hzv : z*v ≤ (1/2)*z := by nlinarith
    have hzv' : z*v ≤ (391/1000)*v := by nlinarith
    have hr : (4/5:ℝ) ≤ (3*z+v)/(6*z^2+4*z*v+v^2) := by
      rw [le_div_iff₀ hd]
      nlinarith
    have hh := gaussian_deleted_right (m:=3) hz hv0.le
    norm_num at hh
    convert (mul_le_mul_of_nonneg_left hr hq).trans hh using 1; first | rfl | ring
end AtomicTriangular.Construction
end

end OAI
