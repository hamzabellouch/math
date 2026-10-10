import OAI.Dynamics.StandardMap.ScaleTestBounds

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma meanDeficit_ratio (k : ℝ) (hk : 0≤k) (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    meanDeficit k n ≤ ((m:ℝ)/(n:ℝ))*meanDeficit k m := by
  have hh := meanDeficit_comparison k hk n m hnm
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show (0:ℝ)<n by exact_mod_cast hn)).mpr
  nlinarith
lemma dyadic_aligned_deficit_bound (k : ℝ) (hk : 0≤k) (p l H : ℕ)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (hH : (t:ℝ)-(s:ℝ)≤2^(H+1)) :
    meanDeficit k (m*2^l) ≤ (2^(H+1)/((t:ℝ)-(s:ℝ)))*meanDeficit k (2^(p+l+H)) := by
  have hlen : ((t:ℝ)-(s:ℝ))*(2:ℝ)^p=2*(m:ℝ) := by push_cast at hs ht; nlinarith
  have hlen0 : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hratio : (((2^(p+l+H):ℕ):ℝ)/((m*2^l:ℕ):ℝ))=(2:ℝ)^(H+1)/((t:ℝ)-(s:ℝ)) := by
    push_cast
    apply (div_eq_div_iff (by positivity) hlen0.ne').mpr
    rw [pow_add,pow_add,pow_succ]
    nlinarith [congrArg (fun x : ℝ => x*((2:ℝ)^l*(2:ℝ)^H)) hlen]
  have hn : m*2^l≤2^(p+l+H) := by
    have hR : (m:ℝ)*2^l≤2^(p+l+H) := by
      rw [pow_add,pow_add]
      have hh := mul_le_mul_of_nonneg_right hH (show (0:ℝ)≤2^p by positivity)
      rw [pow_succ] at hh
      have hmH : (m:ℝ)≤2^p*2^H := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hmH (show (0:ℝ)≤2^l by positivity)]
    exact_mod_cast hR
  exact (meanDeficit_ratio k hk (m*2^l) (2^(p+l+H)) (by positivity) hn).trans_eq (by rw [hratio])
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
noncomputable def initialLaw (i : ℕ) : Measure DistanceArray :=
  scaleLaw (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i) 1 (S.epsilon i)
noncomputable def terminalLaw (i : ℕ) : Measure DistanceArray :=
  scaleLaw (S.parameter i) (S.positive i).le (S.exponent i) 1 (S.epsilon i)
noncomputable def multiLaw (i : ℕ) : Measure DistanceArray :=
  scaleLaw (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i)
    (S.exponent i-criticalLowerExponent S.offset i) (S.epsilon i)
instance initialLaw_finite (i : ℕ) : IsFiniteMeasure (S.initialLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
instance terminalLaw_finite (i : ℕ) : IsFiniteMeasure (S.terminalLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
instance multiLaw_finite (i : ℕ) : IsFiniteMeasure (S.multiLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
lemma lowerExponent_tendsto : Tendsto (criticalLowerExponent S.offset) atTop atTop := by
  apply tendsto_atTop_mono (f := fun i : ℕ => i) _ tendsto_id
  intro i
  unfold criticalLowerExponent
  omega
lemma exponent_tendsto : Tendsto S.exponent atTop atTop := tendsto_atTop_mono (fun i => (S.lower_lt i).le) S.lowerExponent_tendsto
lemma multiLaw_test_bound (j : ArrayTestIndex) :
    ∃ C : ℝ, ∀ᶠ i in atTop, (∫ d,arrayTest j d ∂S.multiLaw i)≤C := by
  rcases j with ⟨⟨s,t⟩,hst⟩
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨H,hH⟩ := pow_unbounded_of_one_lt ((t:ℝ)-(s:ℝ)) (by norm_num : (1:ℝ)<2)
  have hH' : (t:ℝ)-(s:ℝ)≤(2:ℝ)^(H+1) := hH.le.trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) H])
  let R : ℝ := 2^(H+1)/((t:ℝ)-(s:ℝ))
  have hR : 0<R := div_pos (by positivity) (sub_pos.mpr hst)
  refine ⟨18*R*(2*doublingConstant)^H,?_⟩
  filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop p₀] with i hi
  obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
  have hb := integral_test_scalelaw (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i)
    (S.exponent i-criticalLowerExponent S.offset i) (S.epsilon i) (S.epsilon_pos i) s t hst a m hm hs ht
  have hh := dyadic_aligned_deficit_bound (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i)
    (S.exponent i-criticalLowerExponent S.offset i) H s t hst a m hm hs ht hH'
  rw [Nat.add_sub_of_le (S.lower_lt i).le] at hh
  have hterm := S.terminal i H
  have heps := S.epsilon_pos i
  change _ ≤ R*meanDeficit (S.parameter i) (2^(S.exponent i+H)) at hh
  have hl := hh.trans (mul_le_mul_of_nonneg_left hterm hR.le)
  apply hb.trans
  apply (div_le_iff₀ heps).mpr
  change 9*meanDeficit (S.parameter i) (m*2^(S.exponent i-criticalLowerExponent S.offset i))≤_
  change _ ≤ R*(2*(2*doublingConstant)^H*S.epsilon i) at hl
  nlinarith
lemma singleLaw_test_bound (p : ℕ) (k : ℝ) (hk : 0 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (s t : DyadicTime) (hst : (s:ℝ) < (t:ℝ)) (a : ℤ) (m H : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (hH : (t:ℝ)-(s:ℝ) ≤ 2^(H+1)) :
    (∫ d,arrayTest ⟨(s,t),hst⟩ d ∂scaleLaw k hk p 1 ε) ≤
      (9*(2^(H+1)/((t:ℝ)-(s:ℝ))))*(meanDeficit k (2^(p+(H+1)))/ε) := by
  have hb := integral_test_scalelaw k hk p 1 ε hε s t hst a m hm hs ht
  have hh := dyadic_aligned_deficit_bound k hk p 1 H s t hst a m hm hs ht hH
  rw [show p+1+H=p+(H+1) by omega] at hh
  apply hb.trans
  have hmul := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 9 by norm_num)
  have hd := (div_le_div_iff_of_pos_right hε).mpr hmul
  simpa only [mul_div_assoc,mul_assoc] using hd
lemma terminalLaw_test_bound (j : ArrayTestIndex) :
    ∃ C : ℝ, ∀ᶠ i in atTop, (∫ d,arrayTest j d ∂S.terminalLaw i) ≤ C := by
  rcases j with ⟨⟨s,t⟩,hst⟩
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨H,hH⟩ := pow_unbounded_of_one_lt ((t:ℝ)-(s:ℝ)) (by norm_num : (1:ℝ) < 2)
  have hH' : (t:ℝ)-(s:ℝ) ≤ (2:ℝ)^(H+1) := hH.le.trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) H])
  let R : ℝ := 2^(H+1)/((t:ℝ)-(s:ℝ))
  have hR : 0 < R := div_pos (by positivity) (sub_pos.mpr hst)
  refine ⟨18*R*(2*doublingConstant)^(H+1),?_⟩
  filter_upwards [S.exponent_tendsto.eventually_ge_atTop p₀] with i hi
  obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
  have hb := singleLaw_test_bound (S.exponent i) (S.parameter i) (S.positive i).le (S.epsilon i)
    (S.epsilon_pos i) s t hst a m H hm hs ht hH'
  have hh := S.terminal i (H+1)
  have he : meanDeficit (S.parameter i) (2^(S.exponent i+(H+1)))/S.epsilon i ≤ 2*(2*doublingConstant)^(H+1) := by
    apply (div_le_iff₀ (S.epsilon_pos i)).mpr
    exact hh
  exact hb.trans ((mul_le_mul_of_nonneg_left he (show 0 ≤ 9*R by positivity)).trans_eq (by ring))
lemma initialLaw_test_tendsto (j : ArrayTestIndex) :
    Tendsto (fun i => ∫ d,arrayTest j d ∂S.initialLaw i) atTop (𝓝 0) := by
  rcases j with ⟨⟨s,t⟩,hst⟩
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨H,hH⟩ := pow_unbounded_of_one_lt ((t:ℝ)-(s:ℝ)) (by norm_num : (1:ℝ) < 2)
  have hH' : (t:ℝ)-(s:ℝ) ≤ (2:ℝ)^(H+1) := hH.le.trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) H])
  let R : ℝ := 2^(H+1)/((t:ℝ)-(s:ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg (fun d => arrayTest_nonneg _ d)))
  · filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop p₀] with i hi
    obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
    exact singleLaw_test_bound (criticalLowerExponent S.offset i) (S.parameter i) (S.positive i).le (S.epsilon i)
      (S.epsilon_pos i) s t hst a m H hm hs ht hH'
  · simpa only [mul_zero] using (S.initial_ratio_tendsto (H+1)).const_mul (9*R)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
