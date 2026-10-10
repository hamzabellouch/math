import OAI.Geometry.Convex.GeneralMahler.Budget.Major
import OAI.Geometry.Convex.GeneralMahler.BiWeight

namespace OAI
/-! Scalar exterior and middle estimates via Cauchy--Schwarz. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Interval
namespace GeneralMahler.Seg
open Roots Layers

lemma integral_sq_le (f:ℝ→ℝ) (hf:Continuous f) (a b:ℝ) (h:a≤b) :
    (∫ x in a..b,f x)^2 ≤ (b-a)*∫ x in a..b,f x^2 := by
  rcases h.eq_or_lt with rfl|h
  · simp
  have ht : 0<b-a := sub_pos.mpr h
  let c := (∫ x in a..b,f x)/(b-a)
  have hq : (∫ x in a..b,f x)=c*(b-a) := by unfold c; field_simp
  have hp := intervalIntegral.integral_nonneg h.le (f:=fun x=>(f x-c)^2)
    (μ:=volume) (fun x _=>sq_nonneg _)
  have hi (x) : (f x-c)^2=f x^2-(2*c)*f x+c^2 := by ring
  simp_rw [hi] at hp
  rw [intervalIntegral.integral_add,intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hp
  · rw [hq] at *
    change 0≤ _-_+(b-a)*c^2 at hp
    nlinarith [mul_nonneg hp ht.le]
  all_goals first | exact (hf.pow _).intervalIntegrable .. |
    exact ((continuous_const.mul hf).intervalIntegrable ..) |
    exact (continuous_const.intervalIntegrable ..) |
    exact (((hf.pow _).sub (continuous_const.mul hf)).intervalIntegrable ..)
lemma bar_sq (g:Plane→ℝ) (hg:Bwt g) (u:Plane) :
    bAv g u^2 ≤ bAv (fun v=>g v^2) u := by
  have hh := integral_sq_le (fun x=>g (u.1,along u x)) (hg.c.comp
    (by unfold along; fun_prop)) 0 1 zero_le_one
  simpa [bAv] using hh

def signE (x z:ℝ) := if z<x then (1:ℝ) else -1
def rcoef (x y z:ℝ) := if signE x z=signE y z then signE x z * √(|x-z|)*√(|y-z|) else 0
def Om (f:Plane→ℝ) (x y z:ℝ) :=
  (|x-z| *bAv f (z,x)+|y-z| *bAv f (z,y))/2
def kz (f:Plane→ℝ) (x y z:ℝ) :=
  ((x-z)*bAv f (z,x)+(y-z)*bAv f (z,y)-rcoef x y z*(bAv f (z,x)+bAv f (z,y)))/2

lemma r_swap (x y z) : rcoef x y z=rcoef y x z := by
  unfold rcoef
  by_cases h:signE x z=signE y z
  · simp only [h,↓reduceIte]; ring
  simp [h,Ne.symm h]
lemma K_swap (f) (x y z) : kz f x y z=kz f y x z := by
  unfold kz; rw [r_swap]; ring
lemma O_swap (f) (x y z) : Om f x y z=Om f y x z := by unfold Om; ring
lemma bar_const (x:Plane) : bAv (fun _=>1) x=1 := by unfold bAv; simp

lemma middle (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hx:x<z) (hy:z<y) :
    kz f x y z ^2≤Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2≤Om (fun _=>1) x y z* Ux x y z := by
  have ha : x≤ z := hx.le
  have he : rcoef x y z=0 := by unfold rcoef signE; norm_num [not_lt_of_ge ha,hy]
  let a := z-x
  let b := y-z
  let V := fun t => bAv f (z,t)
  let W := fun t => bAv (fun u=>f u^2) (z,t)
  have hp : 0<a := sub_pos.mpr hx
  have hh : 0<b := sub_pos.mpr hy
  have hu : y-x=a+b := by unfold a b; ring
  unfold kz Om Uy Ux
  rw [he,U_mid xk gx hx hy,U_mid yk _ hx hy,abs_of_neg (sub_neg.mpr hx),abs_of_pos (sub_pos.mpr hy)]
  have hh₁ : x-z= -a := by unfold a; ring
  rw [hh₁,neg_neg]
  constructor
  · change ((-a*V x+b*V y-0*_)/2)^2 ≤ (a*W x+b*W y)/2*((y-x)*(1/2))
    have hv : (a*V x-b*V y)^2 ≤ (a+b)*(a*W x+b*W y) :=
      calc
        _ ≤ (a+b)*(a*V x^2+b*V y^2) := by nlinarith [mul_nonneg (mul_nonneg hp.le hh.le) (sq_nonneg (V x+V y))]
        _ ≤ _ := by
          have hX : V x^2≤W x := bar_sq f hf _
          have hY : V y^2≤W y := bar_sq f hf _
          gcongr
    rw [hu]; nlinarith
  simp_rw [bar_const]
  unfold gx; rw [hu]
  have hh₂ : z-x=a := rfl
  rw [hh₂]; apply le_of_eq; field_simp; ring

-- parameterized ray ε, near z+ε*b, far z+ε*a.
lemma av_dist (f:Plane→ℝ) (z sig b:ℝ) (_hb:0<b) :
    bAv f (z,z+sig*b)*b = ∫ t in 0..b,f (z,z+sig*t) := by
  let g := fun t=>f (z,z+sig*t)
  have hh := intervalIntegral.smul_integral_comp_mul_left g (a:=0) (b:=1) b
  unfold bAv
  have he (t:ℝ) : f ((z,z+sig*b).1,along (z,z+sig*b) t) = g (b*t) := by
    unfold along g; dsimp; congr 2; ring
  simp_rw [he]
  simpa only [mul_zero,mul_one,smul_eq_mul,mul_comm b,zero_mul,one_mul,g] using hh

lemma ext_shape {a b:ℝ} (ha:0<b) (h:b<a) :
    let l:=a-b
    l*xk (b/l)=(√a-√b)^4/( (a+b)/2) ∧
      l*yk (b/l)=(√a-√b)^2/2*((a-b)/a+(1-√b/√a)^2/2) := by
  intro l
  have hl : 0<l:= sub_pos.mpr h
  have hp : 0<a:=ha.trans h
  have ht : 1+b/l=a/l := by field_simp; unfold l; ring
  unfold xk yk u
  rw [ht,Real.sqrt_div ha.le,Real.sqrt_div hp.le]
  have hk:= Real.sq_sqrt hl.le
  have he:= Real.sqrt_pos.mpr hp; have hh:=Real.sqrt_pos.mpr hl
  have hb : 1+2*(b/l)>0 := by positivity
  constructor
  all_goals field_simp
  · rw [show √l^4=l^2 by rw [show (4:ℕ)=2*2 from rfl,pow_mul,hk] ]
    unfold l; ring
  rw [hk]; unfold l; ring

-- exterior, parameterized orientation. U replaced analytic RHS.
lemma K_ext (f:Plane→ℝ) (hf:Bwt f) (z s a b:ℝ) (hs:s=1 ∨ s= -1)
    (hp:0<b) (h:b<a) :
    let x:=z+s*b
    let y:=z+s*a
    let l:=a-b
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z*(l*yk (b/l)) ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z*(l*xk (b/l)) := by
  intro x y l
  have ha : 0<a:=hp.trans h
  set A:=√a; set B:=√b
  have hA : 0<A:= Real.sqrt_pos.mpr ha
  have hB : 0<B:= Real.sqrt_pos.mpr hp
  have HB : B^2=b := Real.sq_sqrt hp.le
  have HA : A^2=a := Real.sq_sqrt ha.le
  let g := fun t=>f (z,z+s*t)
  have hg : Continuous g := hf.c.comp (by fun_prop)
  let R := fun t=> bAv f (z,z+s*t)
  let P := fun t=> bAv (fun u=> f u^2) (z,z+s*t)
  let x₁:=∫ t in b..a,g t
  let x₂:=∫ t in 0..b,g t
  let y₁:=∫ t in b..a,g t^2
  let y₂:=∫ t in 0..b,g t^2
  have hi : R b*b=x₂ ∧ R a*a=x₂+x₁ ∧ P b*b=y₂ ∧ P a*a=y₂+y₁ := by
    have he := hg.intervalIntegrable (μ:=volume)
    have hh := (hg.pow 2).intervalIntegrable (μ:=volume)
    exact ⟨av_dist f z s b hp,(av_dist f z s a ha).trans
      (intervalIntegral.integral_add_adjacent_intervals (he ..) (he ..)).symm,
      av_dist _ z s b hp,(av_dist _ z s a ha).trans
        (intervalIntegral.integral_add_adjacent_intervals (hh ..) (hh ..)).symm⟩
  obtain ⟨hx,hx',hy,hy'⟩:=hi
  have he : (A*R a-B*R b)^2 ≤ (a*P a+b*P b)*((a-b)/a+(1-B/A)^2/2) := by
    have h₁:= integral_sq_le g hg b a h.le
    have h₂:= integral_sq_le g hg 0 b hp.le; rw [sub_zero] at h₂
    change x₁^2≤l*y₁ at h₁
    change x₂^2≤b*y₂ at h₂
    have hl : 0<l:= sub_pos.mpr h
    let d:=1/A; let c:=1/A-1/B
    have hh : (d*x₁+c*x₂)^2 ≤ (d^2*l+c^2*b/2)*(y₁+2*y₂) := by
      have he := add_le_add ((div_le_iff₀ hl).mpr (h₁.trans_eq (mul_comm ..))) (mul_le_mul_of_nonneg_left ((div_le_iff₀ hp).mpr (h₂.trans_eq (mul_comm ..)))
        (show (0:ℝ)≤2 by norm_num))
      apply le_trans _ (mul_le_mul_of_nonneg_left he (by positivity))
      field_simp
      nlinarith [sq_nonneg (2*d*l*x₂-c*b*x₁)]
    have hz : d*x₁+c*x₂=A*R a-B*R b := by
      unfold d c
      rw [show x₁=R a*a-R b*b by linarith,← hx,← HA,← HB]
      field_simp; ring
    have hq : d^2*l+c^2*b/2=(a-b)/a+(1-B/A)^2/2 := by
      unfold d c l; rw [← HA,← HB]; field_simp; ring
    rw [hz,hq] at hh
    have hi : y₁+2*y₂=a*P a+b*P b := by linarith
    rw [hi] at hh; linarith
  have ht : |x-z|=b ∧ |y-z|=a ∧ x-z=s*b ∧ y-z=s*a ∧ rcoef x y z=s*B*A := by
    unfold x y rcoef signE
    rcases hs with h|h <;> subst s <;> simp [A,B,hp,ha,not_lt_of_ge hp.le,not_lt_of_ge ha.le,abs_of_pos]
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := ht
  obtain ⟨h₆,h₇⟩ := ext_shape hp h
  have hs' : s^2=1 := by rcases hs with rfl|rfl<;>ring
  unfold kz Om
  rw [h₅,h₁,h₂,h₃,h₄]
  constructor
  · change ((s*b*R b+s*a*R a-s*B*A*(R b+R a))/2)^2 ≤ (b*P b+a*P a)/2*(l*yk (b/l))
    rw [h₇]
    change _≤(b*P b+a*P a)/2*((A-B)^2/2*((a-b)/a+(1-B/A)^2/2))
    apply le_trans _ (by
      have h := mul_le_mul_of_nonneg_left he (show 0 ≤ (A-B)^2/4 by positivity)
      exact h.trans_eq (by ring))
    apply le_of_eq
    calc
      _ = s^2*((A-B)^2/4)*(A*R a-B*R b)^2 := by rw [← HA,← HB]; ring
      _ = _ := by rw [hs',one_mul]
  simp_rw [bar_const]
  rw [h₆]
  apply le_of_eq
  change _= _*((A-B)^4 / _)
  field_simp
  rw [← HA,← HB]
  rcases hs with h|h <;> rw [h] <;> ring

lemma k_same (f) (z x:ℝ) :
    kz f x x z=0 := by
  unfold kz rcoef
  rw [ite_eq_left rfl, mul_assoc (signE x z) (√|x-z|) (√|x-z|),← pow_two, Real.sq_sqrt (abs_nonneg _)]
  unfold signE; split_ifs with h
  · rw [abs_of_pos (sub_pos.mpr h)]; ring
  rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]; ring

lemma O_nn (f:Plane→ℝ) (hf:Bwt f) (x y z:ℝ) :
    0 ≤ Om (fun u=>f u^2) x y z ∧ 0 ≤ Om (fun _=>1) x y z := by
  constructor
  · have hh (u:Plane) : 0≤bAv (fun u=>f u^2) u := (sq_nonneg _).trans (bar_sq f hf u)
    unfold Om
    exact div_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (hh _)) (mul_nonneg (abs_nonneg _) (hh _))) (by norm_num)
  unfold Om; rw [bar_const,bar_const]; positivity

lemma pairOrd (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hx:x<y) (hy:z≠x) (hz:z≠y) :
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z* Ux x y z := by
  unfold Uy Ux
  rcases lt_or_gt_of_ne hy with h|h
  · rw [U_outLo _ _ hx h,U_outLo _ _ hx h]
    have hh := K_ext f hf z 1 (y-z) (x-z) (Or.inl rfl) (sub_pos.mpr h)
      (show x-z<y-z by linarith)
    simpa only [one_mul,add_sub_cancel,sub_sub_sub_cancel_right] using hh
  rcases lt_or_gt_of_ne hz with h'|h'
  · exact middle f hf h h'
  rw [U_outHi _ _ hx h',U_outHi _ _ hx h',K_swap,O_swap,K_swap (fun _=>1),O_swap (fun _=>1)]
  have hh := K_ext f hf z (-1) (z-x) (z-y) (Or.inr rfl) (sub_pos.mpr h')
    (show z-y<z-x by linarith)
  simpa only [neg_one_mul,← sub_eq_add_neg,sub_sub_cancel,sub_sub_sub_cancel_left] using hh

lemma pairEst (f:Plane→ℝ) (hf:Bwt f) {x y z:ℝ} (hy:z≠x) (hz:z≠y) :
    kz f x y z ^2 ≤ Om (fun u=>f u^2) x y z* Uy x y z ∧
    (2*kz (fun _=>1) x y z)^2 ≤ Om (fun _=>1) x y z* Ux x y z := by
  rcases lt_trichotomy x y with h|rfl|h
  · exact pairOrd f hf h hy hz
  · simp only [k_same,Ux,Uy,U,sub_self,abs_zero]; norm_num
  rw [K_swap,O_swap,K_swap (fun _=>1),O_swap (fun _=>1),Ux,U_swap,Uy,U_swap]
  exact pairOrd f hf h hz hy
end GeneralMahler.Seg

end

end OAI
