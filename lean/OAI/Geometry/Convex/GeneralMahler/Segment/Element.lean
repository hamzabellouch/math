import OAI.Geometry.Convex.GeneralMahler.Scalar.Circle

namespace OAI
/-! Elementary small angle quantitative inequalities. -/
noncomputable section
open MeasureTheory Set Filter Real Metric
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid Profile
lemma integUp (f:ℝ→ℝ) {g:ℝ→ℝ} {x:ℝ}(hd:∀ x,HasDerivAt f (g x) x)
    (hx:0≤ x)(he:0≤f 0)(hh:∀ t∈Icc 0 x,0≤g t): 0≤ f x:= by
  apply he.trans
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    (fun t ht=>(hd t).continuousAt.continuousWithinAt)
    (fun t ht=>(hd t).differentiableAt.differentiableWithinAt) _
    (show 0∈Icc (0:ℝ) x from ⟨le_rfl,hx⟩) (show x∈Icc 0 x from ⟨hx,le_rfl⟩) hx
  intro t ht; rw [(hd _).deriv]; exact hh _ (interior_subset ht)

lemma cs_L4 {x:ℝ}(h:0≤x): cos x ≤1-x^2/2+x^4/24:= by
  let f:=fun x:ℝ=>1-x^2/2+x^4/24-cos x
  have hd (t):HasDerivAt f (sin t-t+t^3/6) t:=by
    let T:=hasDerivAt_id' t
    convert (((((hasDerivAt_const t 1).fun_sub ((T.pow 2).div_const 2)).fun_add
      ((T.pow 4).div_const 24)).fun_sub (Real.hasDerivAt_cos t))) using 1
    all_goals first|rfl|(norm_num;ring)
  apply sub_nonneg.mp (integUp f hd h (by simp [f]) _)
  intro x hx; linarith [Real.sin_ge_sub_cube hx.1]
lemma sn_H5 {x:ℝ}(h:0≤x): sin x ≤ x-x^3/6+x^5/120:= by
  let f:=fun x:ℝ=>x-x^3/6+x^5/120-sin x
  have hd(t):HasDerivAt f (1-t^2/2+t^4/24-cos t) t:=by
    let T:=hasDerivAt_id' t
    convert (((T.fun_sub ((T.pow 3).div_const 6)).fun_add ((T.pow 5).div_const 120)).fun_sub
      (Real.hasDerivAt_sin t)) using 1
    all_goals first| rfl| (norm_num; ring)
  exact sub_nonneg.mp (integUp f hd h (by simp [f]) fun x hx=>sub_nonneg.mpr (cs_L4 hx.1))
lemma cs6 {x:ℝ}(h:0≤x):1-x^2/2+x^4/24-x^6/720 ≤ cos x:= by
  let f:= fun x:ℝ=> cos x-(1-x^2/2+x^4/24-x^6/720)
  have hd(t):HasDerivAt f (t-t^3/6+t^5/120-sin t) t:=by
    let T:=hasDerivAt_id' t
    convert ((Real.hasDerivAt_cos t).fun_sub
      (((((hasDerivAt_const t 1).fun_sub ((T.pow 2).div_const 2)).fun_add
        ((T.pow 4).div_const 24)).fun_sub ((T.pow 6).div_const 720)))) using 1
    all_goals first|rfl|( norm_num; ring)
  exact sub_nonneg.mp (integUp f hd h (by simp [f]) fun x hx=>sub_nonneg.mpr (sn_H5 hx.1))

lemma snsq (x:ℝ) (hx:0≤x): sin x^2 ≤ x^2 - x^4/3+2*x^6/45:= by
  have hh:=cs6 (show 0≤x+x by linarith)
  rw [Real.cos_add] at hh
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma sinDif (x:ℝ)(hx:0≤x): |sin x-x*cos x|≤ x^3/3 := by
  let f:=fun x:ℝ=>sin x-x*cos x
  let g:=fun x:ℝ=>x^3/3
  have hd(t):HasDerivAt f (t*sin t) t:=by
    convert ((Real.hasDerivAt_sin t).sub ((hasDerivAt_id' t).mul (Real.hasDerivAt_cos t))) using 1
    all_goals first|rfl|ring
  have he(t):HasDerivAt g (t*t) t:= by
    convert (((hasDerivAt_id' t).pow 3).div_const 3) using 1
    all_goals first|rfl| (norm_num;ring)
  have hl (t:ℝ)(ht: t∈ Icc 0 x): -t*t≤ t*sin t∧ t*sin t≤t*t:= by
    have h:t ≥ 0:= ht.1
    have hp:|sin t| ≤ t:= by simpa [abs_of_nonneg h] using
      (Real.abs_sin_le_abs (x:=t))
    obtain ⟨ha,hb⟩:=abs_le.mp hp
    constructor<;>nlinarith
  have hi := integUp _ (fun t=>(he t).fun_add (hd t)) hx (by simp [f,g])
    (fun x hx=> by linarith [(hl x hx).1])
  have hu:= integUp _ (fun t=>(he t).fun_sub (hd t)) hx (by simp [f,g])
    (fun x hx=>sub_nonneg.mpr (hl x hx).2)
  change |f x|≤g x
  rw [abs_le];  constructor<;> linarith

lemma ch0 (x:ℝ)(hx:0 ≤ x): x ≤ sinh x := by
  apply sub_nonneg.mp
  apply integUp (fun t=> sinh t-t) (fun x=>(Real.hasDerivAt_sinh x).fun_sub (hasDerivAt_id' x))
    hx (by simp)
  exact fun t _=> sub_nonneg.mpr (Real.one_le_cosh t)
lemma ch2 (x:ℝ)(hx:0≤x):1+x^2/2 ≤ cosh x:= by
  let f:=fun x:ℝ=> cosh x-(1+x^2/2)
  have he(t): HasDerivAt f (sinh t-t) t:=by
    convert ((Real.hasDerivAt_cosh t).sub ((((hasDerivAt_id' t).pow 2).div_const 2).const_add 1)) using 1
    all_goals first|rfl|(norm_num)
  exact sub_nonneg.mp (integUp f he hx (by simp [f]) fun t ht=>sub_nonneg.mpr (ch0 _ ht.1))

lemma sh3 (x:ℝ)(hx:0≤x): x+x^3/6 ≤ sinh x:= by
  let f:=fun x:ℝ=> sinh x-(x+x^3/6)
  have he(t):HasDerivAt f (cosh t-(1+t^2/2)) t:=by
    convert ((Real.hasDerivAt_sinh t).sub ((hasDerivAt_id' t).add
      (((hasDerivAt_id' t).pow 3).div_const 6))) using 1
    all_goals first|rfl|(norm_num;ring)
  exact sub_nonneg.mp (integUp f he hx (by simp [f]) (fun t ht=>sub_nonneg.mpr (ch2 t ht.1)))

lemma cshH {H C:ℝ}(hC:cosh H ≤ C) {x:ℝ}(hx:|x|≤H):
    cosh x≤1+C*x^2/2 := by
  have h (x:ℝ)(hx:0≤x)(he:x≤H): sinh x≤ C*x:= by
    apply sub_nonneg.mp
    have hd(t): HasDerivAt (fun x=>C*x-sinh x) (C-cosh t) t:=by
      convert (((hasDerivAt_id' t).const_mul C).fun_sub (Real.hasDerivAt_sinh t)) using 1; first|rfl|ring
    refine integUp (fun x=>C*x-sinh x) hd hx (by simp) ?_
    intro t ht
    apply sub_nonneg.mpr; apply le_trans _ hC
    apply cosh_le_cosh.2
    rw [abs_of_nonneg ht.1,abs_of_nonneg (hx.trans he)]; exact ht.2.trans he
  let f:=fun x:ℝ=>1+C*x^2/2-cosh x
  have he(t):HasDerivAt f (C*t-sinh t) t:=by
    convert ((((((hasDerivAt_id' t).pow 2).const_mul C).div_const 2).const_add 1).sub
      (Real.hasDerivAt_cosh t)) using 1
    all_goals first|rfl|(norm_num;ring)
  have hi:= integUp f he (abs_nonneg x) (by simp [f])
    (fun t ht=>sub_nonneg.mpr (h t ht.1 (ht.2.trans hx)))
  unfold f at hi; rw [sq_abs] at hi
  apply sub_nonneg.mp; convert hi using 1
  rcases le_total 0 x with H|H <;> simp [abs_of_nonpos,abs_of_nonneg,H]

lemma sinhH {H C:ℝ}(hC:cosh H≤ C) {x:ℝ}(hx:0≤x)(he:x≤H):
    sinh x ≤ x+C*x^3/6 := by
  let f:=fun x:ℝ=>x+C*x^3/6-sinh x
  have hd(t):HasDerivAt f (1+C*t^2/2-cosh t) t:=by
    convert (((hasDerivAt_id' t).add (((((hasDerivAt_id' t).pow 3).const_mul C).div_const 6))).sub
      (Real.hasDerivAt_sinh t)) using 1
    all_goals first|rfl|(norm_num;ring)
  apply sub_nonneg.mp (integUp f hd hx (by simp [f]) ?_)
  intro x hx
  exact sub_nonneg.mpr (cshH hC (show |x| ≤ H by rw [abs_of_nonneg hx.1]; exact hx.2.trans he))

lemma coth_est {x:ℝ}(hx:0<x):
    0 ≤ cosh x/sinh x - 1/x ∧ cosh x/sinh x-1/x ≤ x/3 := by
  let f:=fun x=> x*cosh x-sinh x
  have hf(t):HasDerivAt f (t*sinh t) t:=by
    convert (((hasDerivAt_id' t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)) using 1
    all_goals first| rfl|ring
  have hh (t:ℝ)(ht:0≤t):0≤f t:=integUp f hf ht (by simp [f])
    (fun t ht=> mul_nonneg ht.1 (Real.sinh_nonneg_iff.mpr ht.1))
  let g:=fun x:ℝ=> x^2*sinh x/3-f x
  have he(t): HasDerivAt g (t/3*f t) t:=by
    convert ((((((hasDerivAt_id' t).pow 2).mul (Real.hasDerivAt_sinh t))).div_const 3).sub (hf t))
      using 1
    all_goals first|rfl|(unfold f;norm_num;ring)
  have hi:=integUp g he hx.le (by simp [f,g])
    (fun t ht=>mul_nonneg (by linarith [show 0≤t from ht.1]) (hh t ht.1))
  have ho:=hh x hx.le
  have hp:=Real.sinh_pos_iff.mpr hx
  unfold g f at *; constructor <;> field_simp <;> nlinarith

open Cert Cert.IV
lemma smallConst :
    Real.cosh (16/100:ℝ)≤1014/1000 ∧ Real.cosh (3/10:ℝ)≤1046/1000 := by
  have h (x z:Int)(he: LeB (Row0.bCosh (bd x)) (bd z)):
      Real.cosh ((x:ℝ)/10000) ≤ (z:ℝ)/10000 :=
    mle (Row0.mHyp (mbd x)).2 (mbd z) he
  have ha:=h 1600 10140 (by decide +kernel)
  have hb:=h 3000 10460 (by decide +kernel)
  norm_num at *; exact ⟨ha,hb⟩
end GeneralMahler.SCal.SE

end

end OAI
