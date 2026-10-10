import Mathlib

namespace OAI
/-! §07 log-series h in stable formulas. Remainders and smooth positive coefficients. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Finset
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
-- scaled derivatives
def hden (u v:ℝ):= 1-u*v
def Qhv (n:Nat) (u v:ℝ):= (v/hden u v)^(n+1)
def Qh (n:Nat) (u:ℝ) := ∫ t in (0:ℝ)..1,Qhv n u t

lemma hpden {u t:ℝ} (ht:t∈Icc (0:ℝ) 1) (h:u<1) : 0<hden u t := by
  unfold hden; have h1 : 0 ≤ t := ht.1; have h2 : t ≤ 1 := ht.2
  rcases h1.eq_or_lt with hx|hx
  · rw [← hx]; simp
  have he := mul_lt_mul_of_pos_right h hx; linarith
lemma intH (n:Nat) {u:ℝ} (h:u<1): IntervalIntegrable (Qhv n u) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  unfold Qhv; apply ContinuousOn.pow
  exact continuousOn_id.div ((by unfold hden; fun_prop : Continuous _).continuousOn)
    fun x hx=>(hpden hx h).ne'
lemma hdv (n:Nat) {u t:ℝ} (ht:t∈Icc (0:ℝ) 1) (h:u<1) :
    HasDerivAt (fun x=> Qhv n x t) (((n+1:Nat):ℝ)* Qhv (n+1) u t) u := by
  have he: HasDerivAt (fun u=> hden u t) (-t) u := by
    convert ((hasDerivAt_const u 1).sub ((hasDerivAt_id' u).mul_const t)) using 1
    all_goals first|rfl|ring
  have hh:= ((hasDerivAt_const u t).div he (hpden ht h).ne').pow (n+1)
  convert hh using 1
  all_goals first| rfl | skip
  unfold Qhv; push_cast; simp [pow_succ]; ring

lemma hdQ (n:Nat) {u:ℝ} (h:u<1):
    HasDerivAt (Qh n) (((n+1:Nat):ℝ)* Qh (n+1) u) u := by
  let c:ℝ:= max 0 ((1+u)/2)
  let F:= Qhv n
  let G:= fun (x t:ℝ)=> ((n+1:Nat):ℝ)*Qhv (n+1) x t
  let A:= ((n+1:Nat):ℝ)*(1/(1-c))^(n+2)
  have hc : u<c := lt_of_lt_of_le (by linarith) (le_max_right ..)
  have hh : c<1 := max_lt (by linarith) (by linarith)
  have he (m:Nat) (u:ℝ): Measurable (Qhv m u) := by unfold Qhv hden; fun_prop
  have hm (t) (ht:t ∈ Ι (0:ℝ) 1) : t∈Icc (0:ℝ) 1 := by rw [uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le,ht.2⟩
  have hd (x:ℝ) (hx:x∈Iio c) (t) (ht:t∈Icc (0:ℝ) 1):
      ‖G x t‖ ≤ A := by
    have hv:=hpden ht (lt_trans hx hh)
    have hℓ : 1-c ≤ hden x t := by
      unfold hden
      have hc : 0≤ c:=le_max_left ..
      have h' : x*t ≤ c*1 := le_trans (mul_le_mul_of_nonneg_right hx.le ht.1)
        (mul_le_mul_of_nonneg_left ht.2 hc)
      linarith
    have htp : 0≤t/hden x t:= div_nonneg ht.1 hv.le
    unfold G A Qhv
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ htp
    apply div_le_div₀ (by positivity) ht.2 (sub_pos.mpr hh) hℓ
  have hi := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=volume) (F:=F)
    (F':=G) (x₀:=u) (bound:=fun _=> A) (s:=Iio c) (Iio_mem_nhds hc)
    (Eventually.of_forall fun x=> (he _ x).aestronglyMeasurable) (intH n h)
    ((measurable_const.mul (he _ u)).aestronglyMeasurable)
    (ae_of_all _ fun t ht x hx=> hd x hx _ (hm t ht)) (continuous_const.intervalIntegrable 0 1)
    (ae_of_all _ fun t ht x hx=> hdv n (hm t ht) (lt_trans hx hh))
  obtain ⟨_,hi⟩:=hi
  unfold G at hi; rw [intervalIntegral.integral_const_mul] at hi; exact hi
lemma hlog {u:ℝ} (hu:0<u) (h:u<1): u^2*Qh 0 u= -Real.log (1-u)-u := by
  let f:= fun t=> -Real.log (hden u t)-u*t
  let g:= fun t=> u^2*Qhv 0 u t
  have hd (x:ℝ) (hx:x∈Set.uIcc (0:ℝ) 1): HasDerivAt f (g x) x := by
    rw [Set.uIcc_of_le zero_le_one] at hx
    have he : HasDerivAt (hden u) (-u) x := by
      convert ((hasDerivAt_const x 1).sub ((hasDerivAt_id' x).const_mul u)) using 1
      all_goals first|rfl|ring
    convert ((he.log (hpden hx h).ne').neg.sub ((hasDerivAt_id' x).const_mul u)) using 1
    unfold g Qhv
    have hh:=hpden hx h
    unfold hden at *
    simp only [Nat.zero_add,pow_one]; field_simp; ring
  have hi:= intervalIntegral.integral_eq_sub_of_hasDerivAt hd (show IntervalIntegrable g volume 0 1 from
    (intH 0 h).const_mul _)
  unfold g f at hi; rw [intervalIntegral.integral_const_mul] at hi
  simpa only [hden,mul_zero,mul_one,sub_zero,Real.log_one,neg_zero,Qh] using hi

-- rational/geometric remainder
def hCoef (i n:Nat) : ℝ := Nat.choose (i+n) n
def Rpow (i:Nat) (t:ℝ) := (1/(1-t))^(i+1)
def Rpoly (i n:Nat) (t:ℝ) := ∑ j∈range n,hCoef i j*t^j

lemma comb (i n:Nat):
    hCoef (i+1) (n+1) = hCoef i (n+1)+ hCoef (i+1) n := by
  unfold hCoef
  rw [show i+1+(n+1)=i+n+1+1 from by omega,Nat.choose]
  push_cast; rw [show i+1+n=i+n+1 from by omega, show i+(n+1)=i+n+1 from by omega]
  ring

lemma RecPoly (i n:Nat) (x:ℝ):
    Rpoly (i+1) (n+1) x= Rpoly i (n+1) x + x* Rpoly (i+1) n x := by
  induction n with
  | zero=> simp [Rpoly,hCoef]
  | succ n ih=>
    have he (i n:Nat):Rpoly i (n+1) x=Rpoly i n x+hCoef i n*x^n :=
      sum_range_succ ..
    rw [he,he i (n+1),comb,pow_succ]
    have ht := he (i+1) n
    linear_combination ih - x * ht
lemma PowRec (i:Nat) (x:ℝ): Rpow (i+1) x= Rpow i x+x*Rpow (i+1) x := by
  by_cases h:x=1
  · subst x; simp [Rpow]
  unfold Rpow
  rw [pow_succ _ (i+1)]
  field_simp; ring

lemma r_est (i n:Nat) {x:ℝ} (hx:0≤x) (he:x<1):
    let u:= Rpow i x-Rpoly i n x
    0 ≤ u ∧ u ≤ hCoef i n*x^n*Rpow i x := by
  dsimp only
  have hr (i n:Nat): 0 ≤ hCoef i n := by unfold hCoef; positivity
  have hp : 1 ≤1/(1-x) := by rw [le_div_iff₀ (by linarith)]; linarith
  induction i generalizing n with
  | zero=>
    have hj : Rpow 0 x-Rpoly 0 n x=hCoef 0 n*x^n*Rpow 0 x := by
      simp only [Rpow,Rpoly,hCoef,Nat.zero_add,Nat.choose_self,Nat.cast_one,one_mul,pow_one]
      rw [geom_sum_eq (ne_of_lt he)]
      have h1:=sub_ne_zero.mpr (ne_of_lt he)
      have h2:=sub_ne_zero.mpr (ne_of_gt he)
      field_simp
      ring
    rw [hj]; unfold Rpow; exact ⟨mul_nonneg (mul_nonneg (hr ..) (pow_nonneg hx _)) (pow_nonneg (by linarith) _),le_rfl⟩
  | succ i ih=>
    induction n with
    | zero=>
      have ht : 0≤Rpow (i+1) x := by unfold Rpow; positivity
      simpa [Rpoly,hCoef] using ht
    | succ n H=>
      have hz (n:Nat): Rpow (i+1) x-Rpoly (i+1) (n+1) x =
          Rpow i x-Rpoly i (n+1) x + x*(Rpow (i+1) x-Rpoly (i+1) n x) := by
        rw [RecPoly]; linarith [PowRec i x]
      have ht := H.2
      have hh := ih (n+1)
      rw [hz]
      refine ⟨add_nonneg hh.1 (mul_nonneg hx H.1),?_⟩
      have he' : Rpow i x ≤ Rpow (i+1) x := by unfold Rpow; gcongr; omega
      rw [comb]
      have hj:= mul_le_mul_of_nonneg_left he' (show 0≤ hCoef i (n+1)*x^(n+1) from
        mul_nonneg (hr ..) (pow_nonneg hx _))
      apply le_trans (add_le_add hh.2 (mul_le_mul_of_nonneg_left H.2 hx))
      rw [add_mul, add_mul]
      apply add_le_add hj (le_of_eq ?_)
      rw [pow_succ]; ring
end GeneralMahler.SCal

end

end OAI
