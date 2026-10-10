import OAI.NumberTheory.Jacobsthal.Primes.PrimeIntervalFlags

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedTagSieve
open Erdos970Dependency.SiegelWalfisz
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

theorem interval_AP_li_error :
    ∃ c C X₀ : ℝ,0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ R V : ℝ,X₀ ≤ R → 0 ≤ V → V ≤ R → ∀ q : ℕ,∀ r : ℤ,
      0 < q → IsCoprime r (q:ℤ) → (q:ℝ) ≤ Real.exp (c*cubeHeight R) →
      |((intervalPrimes R V q r).card:ℝ)-
        (logarithmicIntegral (R+V)-logarithmicIntegral R)/(q.totient:ℝ)| ≤
          C*R*Real.exp (-c*cubeHeight R) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := large_modulus_siegel_walfisz
  refine ⟨c,3*C,X₀,hc,by positivity,hX₀,?_⟩
  intro R V hR hV hVR q r hq hr hmod
  have hR3 : 3 ≤ R := hX₀.trans hR
  have hR0 : 0 ≤ R := by linarith
  have hRV : R ≤ R+V := by linarith
  have hh : cubeHeight R ≤ cubeHeight (R+V) := cubeHeight_mono (by linarith) hRV
  have hmod' : (q:ℝ) ≤ Real.exp (c*cubeHeight (R+V)) :=
    hmod.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh hc.le))
  have hlo := hAP R hR q r hq hr hmod
  have hhi := hAP (R+V) (hR.trans hRV) q r hq hr hmod'
  have he : Real.exp (-c*cubeHeight (R+V)) ≤ Real.exp (-c*cubeHeight R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hh (by linarith))
  have hb : C*(R+V)*Real.exp (-c*cubeHeight (R+V)) ≤ 2*C*R*Real.exp (-c*cubeHeight R) := by
    calc
      _ ≤ C*(R+V)*Real.exp (-c*cubeHeight R) := mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ _ := by
        have hx := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (show R+V ≤ 2*R by linarith) hC.le)
          (Real.exp_pos (-c*cubeHeight R)).le
        simpa only [mul_assoc,mul_left_comm,mul_comm] using hx
  have hcount : ((intervalPrimes R V q r).card:ℝ)=
      ((intervalPrimes 0 (R+V) q r).card:ℝ)-((intervalPrimes 0 R q r).card:ℝ) := by
    simpa only [add_sub_cancel_left] using intervalPrimes_count_sub hR0 hRV q r
  have hid : ((intervalPrimes R V q r).card:ℝ)-
      (logarithmicIntegral (R+V)-logarithmicIntegral R)/(q.totient:ℝ)=
      (((intervalPrimes 0 (R+V) q r).card:ℝ)-logarithmicIntegral (R+V)/(q.totient:ℝ))-
      (((intervalPrimes 0 R q r).card:ℝ)-logarithmicIntegral R/(q.totient:ℝ)) := by
    rw [hcount]
    ring
  rw [hid]
  have ht := abs_add_le
    (((intervalPrimes 0 (R+V) q r).card:ℝ)-logarithmicIntegral (R+V)/(q.totient:ℝ))
    (-(((intervalPrimes 0 R q r).card:ℝ)-logarithmicIntegral R/(q.totient:ℝ)))
  simp only [abs_neg,← sub_eq_add_neg] at ht
  have hs := ht.trans (add_le_add (hhi.trans hb) hlo)
  convert hs using 1
  dsimp only [cubeHeight]
  ring

theorem interval_AP_count_error :
    ∃ c C X₀ : ℝ,0 < c ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ R V : ℝ,X₀ ≤ R → 0 ≤ V → V ≤ R → ∀ q : ℕ,∀ r : ℤ,
      0 < q → IsCoprime r (q:ℤ) → (q:ℝ) ≤ Real.exp (c*cubeHeight R) →
      |((intervalPrimes R V q r).card:ℝ)-
        ((intervalPrimes R V 1 0).card:ℝ)/(q.totient:ℝ)| ≤
          C*R*Real.exp (-c*cubeHeight R) := by
  obtain ⟨c,C,X₀,hc,hC,hX₀,hAP⟩ := interval_AP_li_error
  refine ⟨c,2*C,X₀,hc,by positivity,hX₀,?_⟩
  intro R V hR hV hVR q r hq hr hmod
  have hR3 : 3 ≤ R := hX₀.trans hR
  have hh : 0 < cubeHeight R := cubeHeight_pos (by linarith)
  have hmod1 : ((1:ℕ):ℝ) ≤ Real.exp (c*cubeHeight R) := by
    simpa using Real.one_le_exp_iff.mpr (mul_nonneg hc.le hh.le)
  have h1 := hAP R V hR hV hVR 1 0 (by norm_num) (by norm_num) hmod1
  have h := hAP R V hR hV hVR q r hq hr hmod
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  simp only [Nat.totient_one,Nat.cast_one,div_one] at h1
  have hp0 : 0 < (q.totient:ℝ) := by linarith
  have hd : |(logarithmicIntegral (R+V)-logarithmicIntegral R-
      ((intervalPrimes R V 1 0).card:ℝ))/(q.totient:ℝ)| ≤ C*R*Real.exp (-c*cubeHeight R) := by
    rw [abs_div,abs_of_pos hp0,abs_sub_comm]
    exact (div_le_div_of_nonneg_right h1 hp0.le).trans (div_le_self (by positivity) hphi)
  have hid : ((intervalPrimes R V q r).card:ℝ)-((intervalPrimes R V 1 0).card:ℝ)/(q.totient:ℝ)=
      (((intervalPrimes R V q r).card:ℝ)-(logarithmicIntegral (R+V)-logarithmicIntegral R)/(q.totient:ℝ))+
      (logarithmicIntegral (R+V)-logarithmicIntegral R-((intervalPrimes R V 1 0).card:ℝ))/(q.totient:ℝ) := by ring
  rw [hid]
  have hs := (abs_add_le _ _).trans (add_le_add h hd)
  convert hs using 1
  dsimp only [cubeHeight]
  ring

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve
open _root_.Filter
open scoped Topology
open Erdos970Dependency.SiegelWalfisz

lemma moving_lower_ge_self {w : ℝ} (hw : 1 ≤ w) :
    w ≤ Real.exp (w^((1:ℝ)/4)*Real.log w) := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hp : 1 ≤ w^((1:ℝ)/4) := Real.one_le_rpow hw (by norm_num)
  have hl : 0 ≤ Real.log w := Real.log_nonneg hw
  calc
    w = Real.exp (Real.log w) := (Real.exp_log hw0).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hp) hl])

lemma cubeHeight_moving_lower {w R : ℝ} (hw : 3 ≤ w)
    (hR : Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R) :
    w^((1:ℝ)/12) ≤ cubeHeight R := by
  have hw0 : 0 < w := by linarith
  have hl : 1 ≤ Real.log w :=
    ((Real.lt_log_iff_exp_lt hw0).mpr (Real.exp_one_lt_three.trans_le hw)).le
  have hlog := Real.log_le_log (Real.exp_pos (w^((1:ℝ)/4)*Real.log w)) hR
  rw [Real.log_exp] at hlog
  have hp : 0 ≤ w^((1:ℝ)/4) := Real.rpow_nonneg hw0.le _
  have hs : w^((1:ℝ)/4) ≤ Real.log R := by nlinarith [mul_nonneg hp (sub_nonneg.mpr hl)]
  calc
    w^((1:ℝ)/12) = (w^((1:ℝ)/4))^((1:ℝ)/3) := by
      rw [← Real.rpow_mul hw0.le]
      norm_num
    _ ≤ cubeHeight R := Real.rpow_le_rpow hp hs (by norm_num)

theorem eventually_moving_exponential_domination (A b K c : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (_hK : 0 ≤ K) (hc : 0 < c) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ ∀ P R : ℝ,1 ≤ P →
      P ≤ Real.exp (K*(Real.log w)^3) → Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      w^A*P^b ≤ Real.exp (c*cubeHeight R) := by
  have hpoly := Real.tendsto_log_atTop.eventually
    (eventually_polynomial_le_exp ((A+b*K)/c) 3 (by norm_num : (0:ℝ)<1/12))
  filter_upwards [eventually_ge_atTop (3:ℝ),hpoly] with w hw hpolyw
  refine ⟨hw,?_⟩
  intro P R hP hPcap hR
  have hw0 : 0 < w := by linarith
  have hP0 : 0 < P := by linarith
  have hl1 := hpolyw.1
  have hLP : Real.log P ≤ K*(Real.log w)^3 := by
    have h := Real.log_le_log hP0 hPcap
    simpa only [Real.log_exp] using h
  have hLsq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hLcube : Real.log w ≤ (Real.log w)^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl1) (sq_nonneg (Real.log w))]
  have hcost : A*Real.log w+b*Real.log P ≤ (A+b*K)*(Real.log w)^3 := by
    have ha := mul_le_mul_of_nonneg_left hLcube hA
    have hh := mul_le_mul_of_nonneg_left hLP hb
    nlinarith
  have hy := cubeHeight_moving_lower hw hR
  have he : Real.exp ((1/12:ℝ)*Real.log w)=w^((1:ℝ)/12) := by
    rw [Real.rpow_def_of_pos hw0]
    congr 1
    ring
  have hpol : ((A+b*K)/c)*(Real.log w)^3 ≤ cubeHeight R := by
    have hz : ((A+b*K)/c)*(Real.log w)^3 ≤ w^((1:ℝ)/12) := by
      simpa only [he] using hpolyw.2
    exact hz.trans hy
  have hh := mul_le_mul_of_nonneg_left hpol hc.le
  have hEq : c*(((A+b*K)/c)*(Real.log w)^3)=(A+b*K)*(Real.log w)^3 := by
    field_simp
  rw [hEq] at hh
  rw [Real.rpow_def_of_pos hw0,Real.rpow_def_of_pos hP0,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem eventually_moving_error (A b K c B eps : ℝ)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hK : 0 ≤ K) (hc : 0 < c)
    (hB : 0 ≤ B) (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ ∀ P R : ℝ,1 ≤ P →
      P ≤ Real.exp (K*(Real.log w)^3) → Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R →
      B*w^A*P^b*Real.log R*Real.exp (-c*cubeHeight R) ≤ eps := by
  have hdom := eventually_moving_exponential_domination A b K (c/2) hA hb hK (by positivity)
  have ht : Tendsto (fun y : ℝ => B*y^3*Real.exp (-(c/2)*y)) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3:ℝ) (c/2) (by positivity)).const_mul B
  obtain ⟨y₀,hy₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds heps))
  have hp : ∀ᶠ w : ℝ in atTop,y₀ ≤ w^((1:ℝ)/12) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/12)).eventually (eventually_ge_atTop y₀)
  filter_upwards [hdom,hp] with w hw hwy
  refine ⟨hw.1,?_⟩
  intro P R hP hPcap hR
  have hRw : w ≤ R := (moving_lower_ge_self (by linarith [hw.1])).trans hR
  have hR1 : 1 ≤ R := by linarith [hw.1]
  have hlog : 0 ≤ Real.log R := Real.log_nonneg hR1
  have he := hw.2 P R hP hPcap hR
  have hprod := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB) hlog)
    (Real.exp_pos (-c*cubeHeight R)).le
  have hrate := hy₀ (cubeHeight R) (hwy.trans (cubeHeight_moving_lower hw.1 hR))
  have hEq : B*Real.exp ((c/2)*cubeHeight R)*Real.log R*Real.exp (-c*cubeHeight R)=
      B*(cubeHeight R)^3*Real.exp (-(c/2)*cubeHeight R) := by
    rw [cubeHeight_pow_three hR1]
    have hh : Real.exp ((c/2)*cubeHeight R)*Real.exp (-c*cubeHeight R)=Real.exp (-(c/2)*cubeHeight R) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = B*Real.log R*(Real.exp ((c/2)*cubeHeight R)*Real.exp (-c*cubeHeight R)) := by ring
      _ = _ := by rw [hh]
  rw [hEq] at hprod
  have hleft : B*w^A*P^b*Real.log R*Real.exp (-c*cubeHeight R)=
      B*(w^A*P^b)*Real.log R*Real.exp (-c*cubeHeight R) := by ring
  rw [hleft]
  exact hprod.trans hrate.le

end ErdosStoppedTagSieve



namespace ErdosStoppedTagSieve
open _root_.Filter
open scoped Topology
open Erdos970Dependency.SiegelWalfisz

lemma eventually_cutoff_dominates (a K : ℝ) (hK : 0 < K) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ w^a < Real.exp (K*(Real.log w)^3) := by
  filter_upwards [eventually_ge_atTop (3:ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 ((a+1)/K)))] with w hw hL
  refine ⟨hw,?_⟩
  have hw0 : 0 < w := by linarith
  have hL1 : 1 ≤ Real.log w := (le_max_left _ _).trans hL
  have haK : (a+1)/K ≤ Real.log w := (le_max_right _ _).trans hL
  have hKL : a+1 ≤ K*Real.log w := by
    have hh := (div_le_iff₀ hK).mp haK
    nlinarith
  have hLsq : Real.log w ≤ (Real.log w)^2 := by nlinarith
  have hKsq : a+1 ≤ K*(Real.log w)^2 := hKL.trans (mul_le_mul_of_nonneg_left hLsq hK.le)
  have hcube : (a+1)*Real.log w ≤ K*(Real.log w)^3 := by
    calc
      _ ≤ (K*(Real.log w)^2)*Real.log w := mul_le_mul_of_nonneg_right hKsq (by linarith)
      _ = _ := by ring
  rw [Real.rpow_def_of_pos hw0]
  apply Real.exp_lt_exp.mpr
  nlinarith

lemma eventually_cutoff_le_subbin (K : ℝ) :
    ∀ᶠ w : ℝ in atTop,3 ≤ w ∧ ∀ P R : ℝ,
      P ≤ Real.exp (K*(Real.log w)^3) → Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R → P ≤ R := by
  have hp := Real.tendsto_log_atTop.eventually
    (eventually_polynomial_le_exp K 3 (by norm_num : (0:ℝ)<1/4))
  filter_upwards [eventually_ge_atTop (3:ℝ),hp] with w hw hpw
  refine ⟨hw,?_⟩
  intro P R hP hR
  have hw0 : 0 < w := by linarith
  have he : Real.exp ((1/4:ℝ)*Real.log w)=w^((1:ℝ)/4) := by
    rw [Real.rpow_def_of_pos hw0]
    congr 1
    ring
  have hpoly : K*(Real.log w)^3 ≤ w^((1:ℝ)/4) := by simpa only [he] using hpw.2
  have hlog := hpw.1
  have hpow : 0 ≤ w^((1:ℝ)/4) := Real.rpow_nonneg hw0.le _
  have hh : K*(Real.log w)^3 ≤ w^((1:ℝ)/4)*Real.log w := by
    nlinarith [mul_nonneg hpow (sub_nonneg.mpr hlog)]
  exact (hP.trans (Real.exp_le_exp.mpr hh)).trans hR

end ErdosStoppedTagSieve


end Erdos970

end OAI
