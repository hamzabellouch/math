import OAI.Analysis.C0Absorption.Weights

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def boundedAngle (J : ℕ) (u : ℝ) (j : ℕ) : ℝ :=
  if j=0 then Real.pi/2 else if J<j then 0 else transitionAngle j u

@[simp] theorem boundedAngle_zero (J : ℕ) (u : ℝ) : boundedAngle J u 0=Real.pi/2 := by simp [boundedAngle]
@[simp] theorem boundedAngle_last (J : ℕ) (u : ℝ) : boundedAngle J u (J+1)=0 := by simp [boundedAngle]

theorem boundedAngle_inner {J j : ℕ} (hj : 0<j) (hJ : j≤J) (u : ℝ) :
    boundedAngle J u j=transitionAngle j u := by simp [boundedAngle,hj.ne',not_lt.mpr hJ]

theorem boundedAngle_range (J j : ℕ) (u : ℝ) :
    0 ≤ boundedAngle J u j ∧ boundedAngle J u j ≤ Real.pi/2 := by
  unfold boundedAngle
  split_ifs
  · exact ⟨by positivity,le_rfl⟩
  · exact ⟨le_rfl,by positivity⟩
  · exact ⟨transitionAngle_nonneg j u,transitionAngle_le j u⟩

theorem boundedAngle_dichotomy (J j : ℕ) (u : ℝ) :
    boundedAngle J u (j+1)=0 ∨ boundedAngle J u j=Real.pi/2 := by
  by_cases hj : j=0
  · exact Or.inr (by simp [hj])
  by_cases hJ : J<j+1
  · exact Or.inl (by simp [boundedAngle,hJ])
  · rw [boundedAngle_inner (by omega) (by omega),boundedAngle_inner (by omega) (by omega)]
    exact transitionAngle_dichotomy j u

def thetaLog (J : ℕ) (u : ℝ) (j : ℕ) : ℝ :=
  Real.sin (boundedAngle J u j)+Real.cos (boundedAngle J u (j+1))-1

theorem thetaLog_mul (J j : ℕ) (u : ℝ) : thetaLog J u j=
    Real.sin (boundedAngle J u j)*Real.cos (boundedAngle J u (j+1)) := by
  rcases boundedAngle_dichotomy J j u with h|h <;> simp [thetaLog,h]

theorem thetaLog_nonneg (J j : ℕ) (u : ℝ) : 0 ≤ thetaLog J u j := by
  rw [thetaLog_mul]
  apply mul_nonneg
  · exact Real.sin_nonneg_of_nonneg_of_le_pi (boundedAngle_range J j u).1
      ((boundedAngle_range J j u).2.trans (by linarith [Real.pi_pos]))
  · exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [(boundedAngle_range J (j+1) u).1,Real.pi_pos])
      (boundedAngle_range J (j+1) u).2

theorem thetaLog_le_one (J j : ℕ) (u : ℝ) : thetaLog J u j ≤ 1 := by
  rcases boundedAngle_dichotomy J j u with h|h
  · simpa only [thetaLog,h,Real.cos_zero,add_sub_cancel_right] using Real.sin_le_one (boundedAngle J u j)
  · simpa only [thetaLog,h,Real.sin_pi_div_two,add_sub_cancel_left] using Real.cos_le_one (boundedAngle J u (j+1))

theorem thetaLog_sq (J j : ℕ) (u : ℝ) : thetaLog J u j^2=
    Real.sin (boundedAngle J u j)^2-Real.sin (boundedAngle J u (j+1))^2 := by
  rcases boundedAngle_dichotomy J j u with h|h
  · simp [thetaLog,h]
  · have hs := Real.sin_sq_add_cos_sq (boundedAngle J u (j+1))
    simp only [thetaLog,h,Real.sin_pi_div_two,one_pow]
    nlinarith

theorem sum_range_differences (f : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (f j-f (j+1))=f 0-f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

theorem thetaLog_squares (J : ℕ) (u : ℝ) : ∑ j : Fin (J+1), thetaLog J u j^2=1 := by
  simp_rw [thetaLog_sq]
  rw [Fin.sum_univ_eq_sum_range (fun j => Real.sin (boundedAngle J u j)^2-Real.sin (boundedAngle J u (j+1))^2),sum_range_differences]
  simp

theorem transitionAngle_unique (u : ℝ) :
    Set.Subsingleton {j | transitionAngle j u ≠ 0 ∧ transitionAngle j u ≠ Real.pi/2} := by
  intro i hi j hj
  by_contra hij
  have mem (k : ℕ) (hk : transitionAngle k u ≠ 0 ∧ transitionAngle k u ≠ Real.pi/2) :
      u ∈ transitionInterval k := by
    constructor
    · by_contra hn
      exact hk.2 (transitionAngle_full k (by linarith))
    · by_contra hn
      exact hk.1 (transitionAngle_zero k (by linarith))
  exact Set.disjoint_left.mp (transitionInterval_disjoint hij) (mem i hi) (mem j hj)

theorem thetaLog_sum_formula (J : ℕ) (u : ℝ) :
    (∑ j : Fin (J+1),thetaLog J u j)=1+
      ∑ j : Fin J, (Real.sin (transitionAngle (j+1) u)+Real.cos (transitionAngle (j+1) u)-1) := by
  rw [Fin.sum_univ_eq_sum_range (thetaLog J u),Fin.sum_univ_eq_sum_range (fun j => Real.sin (transitionAngle (j+1) u)+Real.cos (transitionAngle (j+1) u)-1)]
  simp only [thetaLog,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_range,nsmul_eq_mul,mul_one]
  rw [Finset.sum_range_succ' (fun j => Real.sin (boundedAngle J u j)),
    Finset.sum_range_succ (fun j => Real.cos (boundedAngle J u (j+1)))]
  simp only [boundedAngle_zero,boundedAngle_last,Real.sin_pi_div_two,Real.cos_zero]
  have hs : (∑ j ∈ Finset.range J,Real.sin (boundedAngle J u (j+1)))=
      ∑ j ∈ Finset.range J,Real.sin (transitionAngle (j+1) u) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [boundedAngle_inner (by omega) (by have := Finset.mem_range.mp hj; omega)]
  have hc : (∑ j ∈ Finset.range J,Real.cos (boundedAngle J u (j+1)))=
      ∑ j ∈ Finset.range J,Real.cos (transitionAngle (j+1) u) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [boundedAngle_inner (by omega) (by have := Finset.mem_range.mp hj; omega)]
  rw [hs,hc]
  push_cast
  ring

theorem thetaLog_sum_le (J : ℕ) (u : ℝ) : (∑ j : Fin (J+1),thetaLog J u j) ≤ 2 := by
  classical
  rw [thetaLog_sum_formula]
  let f (j : Fin J) := Real.sin (transitionAngle (j+1) u)+Real.cos (transitionAngle (j+1) u)-1
  have hz (j : Fin J) (hj : transitionAngle (j+1) u=0 ∨ transitionAngle (j+1) u=Real.pi/2) : f j=0 := by
    rcases hj with h|h <;> simp [f,h]
  suffices (∑ j,f j) ≤ 1 by linarith
  by_cases h : ∃ j : Fin J, transitionAngle (j+1) u≠0 ∧ transitionAngle (j+1) u≠Real.pi/2
  · obtain ⟨j,hj⟩ := h
    rw [Finset.sum_eq_single j]
    · dsimp [f]
      linarith [Real.sin_le_one (transitionAngle (j+1) u),Real.cos_le_one (transitionAngle (j+1) u)]
    · intro k _ hkj
      apply hz
      by_contra hh
      push Not at hh
      exact hkj (Fin.ext (by have he := transitionAngle_unique u hh hj; omega))
    · simp
  · have hh (j : Fin J) : f j=0 := by
      apply hz
      have hn := not_exists.mp h j
      tauto
    simp only [hh,Finset.sum_const_zero,zero_le_one]

theorem boundedAngle_difference_sum (J : ℕ) (u v : ℝ) :
    (∑ j : Fin (J+1), (|boundedAngle J u j-boundedAngle J v j|+
      |boundedAngle J u (j+1)-boundedAngle J v (j+1)|)) =
      2*∑ j : Fin J, |transitionAngle (j+1) u-transitionAngle (j+1) v| := by
  simp only [Finset.sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun j => |boundedAngle J u j-boundedAngle J v j|),
    Fin.sum_univ_eq_sum_range (fun j => |boundedAngle J u (j+1)-boundedAngle J v (j+1)|),
    Fin.sum_univ_eq_sum_range (fun j => |transitionAngle (j+1) u-transitionAngle (j+1) v|),
    Finset.sum_range_succ' (fun j => |boundedAngle J u j-boundedAngle J v j|),
    Finset.sum_range_succ (fun j => |boundedAngle J u (j+1)-boundedAngle J v (j+1)|)]
  simp only [boundedAngle_zero,boundedAngle_last,sub_self,abs_zero,add_zero]
  have hh : (∑ j ∈ Finset.range J,|boundedAngle J u (j+1)-boundedAngle J v (j+1)|)=
      ∑ j ∈ Finset.range J,|transitionAngle (j+1) u-transitionAngle (j+1) v| := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [boundedAngle_inner (by omega) (by have := Finset.mem_range.mp hj; omega),
      boundedAngle_inner (by omega) (by have := Finset.mem_range.mp hj; omega)]
  rw [hh]
  ring

theorem thetaLog_distance (J : ℕ) (u v : ℝ) :
    (∑ j : Fin (J+1), |thetaLog J u j-thetaLog J v j|) ≤ (Real.pi/scheduleH)*dist u v := by
  calc
    _ ≤ ∑ j : Fin (J+1), (|boundedAngle J u j-boundedAngle J v j|+
        |boundedAngle J u (j+1)-boundedAngle J v (j+1)|) := by
      apply Finset.sum_le_sum
      intro j _
      have he : thetaLog J u j-thetaLog J v j =
          (Real.sin (boundedAngle J u j)-Real.sin (boundedAngle J v j))+
          (Real.cos (boundedAngle J u (j+1))-Real.cos (boundedAngle J v (j+1))) := by unfold thetaLog; ring
      rw [he]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using Real.lipschitzWith_sin.dist_le_mul (boundedAngle J u j) (boundedAngle J v j)
      · simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using Real.lipschitzWith_cos.dist_le_mul (boundedAngle J u (j+1)) (boundedAngle J v (j+1))
    _ = 2*∑ j : Fin J,|transitionAngle (j+1) u-transitionAngle (j+1) v| := boundedAngle_difference_sum J u v
    _ ≤ 2*(angleSpeed*dist u v) := mul_le_mul_of_nonneg_left (angle_sum_distance J u v) (by norm_num)
    _ = (Real.pi/scheduleH)*dist u v := by change 2*(Real.pi/(2*scheduleH)*dist u v)=_; ring

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def theta (J : ℕ) (r : ℝ) (j : ℕ) : ℝ :=
  if r≤0 then if j=J then 1 else 0 else thetaLog J (Real.log r) j

theorem theta_nonneg (J j : ℕ) (r : ℝ) : 0 ≤ theta J r j := by
  unfold theta
  split_ifs <;> first | exact thetaLog_nonneg J j _ | norm_num

theorem theta_le_one (J j : ℕ) (r : ℝ) : theta J r j ≤ 1 := by
  unfold theta
  split_ifs <;> first | exact thetaLog_le_one J j _ | norm_num

theorem theta_squares (J : ℕ) (r : ℝ) : (∑ j : Fin (J+1),theta J r j^2)=1 := by
  classical
  by_cases hr : r≤0
  · simp only [theta,hr,↓reduceIte,ite_pow,one_pow,zero_pow (two_ne_zero)]
    have he (j : Fin (J+1)) : (j.val=J) ↔ j=Fin.last J := by simp only [Fin.ext_iff,Fin.val_last]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
  · simp only [theta,hr,↓reduceIte]
    exact thetaLog_squares J _

theorem theta_sum_le (J : ℕ) (r : ℝ) : (∑ j : Fin (J+1),theta J r j) ≤ 2 := by
  classical
  by_cases hr : r≤0
  · simp only [theta,hr,↓reduceIte]
    have he (j : Fin (J+1)) : (j.val=J) ↔ j=Fin.last J := by simp only [Fin.ext_iff,Fin.val_last]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]
    norm_num
  · simp only [theta,hr,↓reduceIte]
    exact thetaLog_sum_le J _

theorem log_radius_lower {r : ℝ} (hr : 0<r) (j : ℕ)
    (hle : r ≤ Real.exp (-scheduleH)*rho j) : Real.log r ≤ Real.log (rho j)-scheduleH := by
  have hh := (Real.log_le_log_iff hr (mul_pos (Real.exp_pos _) (rho_pos j))).mpr hle
  rwa [Real.log_mul (Real.exp_pos _).ne' (rho_pos j).ne',Real.log_exp,neg_add_eq_sub] at hh

theorem boundedAngle_full_of_small {J j : ℕ} (hj : j≤J) {r : ℝ} (hr : 0<r)
    (hle : r≤Real.exp (-scheduleH)*rho J) : boundedAngle J (Real.log r) j=Real.pi/2 := by
  by_cases hz : j=0
  · simp [hz]
  · rw [boundedAngle_inner (by omega) hj]
    exact transitionAngle_full j ((log_radius_lower hr J hle).trans (sub_le_sub_right (log_rho_antitone hj) _))

theorem theta_terminal (J j : ℕ) {r : ℝ} (hr : r ≤ Real.exp (-scheduleH)*rho J) :
    theta J r j=if j=J then 1 else 0 := by
  by_cases h : r≤0
  · simp only [theta,h,↓reduceIte]
  have hp : 0<r := lt_of_not_ge h
  simp only [theta,h,↓reduceIte,thetaLog]
  rcases lt_trichotomy j J with hj|rfl|hj
  · rw [boundedAngle_full_of_small hj.le hp hr,boundedAngle_full_of_small (by omega) hp hr,
      Real.sin_pi_div_two,Real.cos_pi_div_two,ite_eq_right hj.ne]
    ring
  · simp only [boundedAngle_full_of_small le_rfl hp hr,boundedAngle_last,
      Real.sin_pi_div_two,Real.cos_zero,ite_true]
    ring
  · simp only [boundedAngle,show j≠0 by omega,show j+1≠0 by omega,hj,
      show J<j+1 by omega,↓reduceIte,Real.sin_zero,Real.cos_zero,ite_eq_right hj.ne',zero_add,sub_self]

theorem boundedAngle_continuous (J j : ℕ) : Continuous (fun u => boundedAngle J u j) := by
  unfold boundedAngle
  split_ifs
  · exact continuous_const
  · exact continuous_const
  · exact (transitionAngle_lipschitz j).continuous

theorem thetaLog_continuous (J j : ℕ) : Continuous (fun u => thetaLog J u j) :=
  ((Real.continuous_sin.comp (boundedAngle_continuous J j)).add (Real.continuous_cos.comp (boundedAngle_continuous J (j+1)))).sub continuous_const

theorem theta_continuous (J j : ℕ) : Continuous (fun r => theta J r j) := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : 0<r
  · apply ((thetaLog_continuous J j).continuousAt.comp (Real.continuousAt_log hr.ne')).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr] with s hs
    simp only [theta,not_le.mpr hs,↓reduceIte,Function.comp_def]
  · have hR : r<Real.exp (-scheduleH)*rho J := lt_of_le_of_lt (le_of_not_gt hr)
      (mul_pos (Real.exp_pos _) (rho_pos J))
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hR] with s hs
    exact theta_terminal J j hs.le

theorem theta_upper_support {J j : ℕ} (hj : 0<j) (hJ : j≤J) {r : ℝ}
    (_hr : 0≤r) (ht : theta J r j≠0) : r≤rho j := by
  by_contra hn
  have hp : 0<r := (rho_pos j).trans (lt_of_not_ge hn)
  have hlog : Real.log (rho j) ≤ Real.log r :=
    (Real.log_le_log_iff (rho_pos j) hp).mpr (le_of_not_ge hn)
  have ha := transitionAngle_zero j hlog
  apply ht
  simp only [theta,not_le.mpr hp,↓reduceIte,thetaLog_mul,boundedAngle_inner hj hJ,ha,Real.sin_zero,zero_mul]

theorem theta_lower_support {J j : ℕ} (hj : j<J) {r : ℝ}
    (_hr : 0≤r) (ht : theta J r j≠0) : ell j≤r := by
  by_contra hn
  have hp : 0<r := by
    by_contra hh
    have hz : r≤0 := le_of_not_gt hh
    exact ht (by simp [theta,hz,hj.ne])
  have hlog := log_radius_lower hp (j+1) (le_of_not_ge hn)
  have ha := transitionAngle_full (j+1) hlog
  apply ht
  simp only [theta,not_le.mpr hp,↓reduceIte,thetaLog_mul,
    boundedAngle_inner (by omega : 0<j+1) (by omega : j+1≤J),ha,Real.cos_pi_div_two,mul_zero]

theorem min_mul_log_distance {r s : ℝ} (hr : 0<r) (hs : 0<s) :
    min r s*|Real.log r-Real.log s| ≤ |r-s| := by
  have oneOrder (r s : ℝ) (hr : 0<r) (hs : 0<s) (hle : r ≤ s) :
      r*|Real.log r-Real.log s| ≤ |r-s| := by
    have hlog := (Real.log_le_log_iff hr hs).mpr hle
    rw [abs_of_nonpos (sub_nonpos.mpr hlog),abs_of_nonpos (sub_nonpos.mpr hle)]
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hs hr)) hr.le
    rw [Real.log_div hs.ne' hr.ne'] at hh
    have he : r*(s/r-1)=s-r := by field_simp
    rw [he] at hh
    linarith
  rcases le_total r s with h|h
  · rw [min_eq_left h]
    exact oneOrder r s hr hs h
  · rw [min_eq_right h,abs_sub_comm (Real.log r),abs_sub_comm r]
    exact oneOrder s r hs hr h

theorem theta_weighted_distance (J : ℕ) {r s : ℝ} (hr : 0≤r) (hs : 0 ≤ s) :
    min r s*(∑ j : Fin (J+1),|theta J r j-theta J s j|) ≤
      (Real.pi/scheduleH)*|r-s| := by
  by_cases hr0 : r=0
  · simp only [hr0,min_eq_left hs,zero_mul]
    exact mul_nonneg (div_nonneg Real.pi_pos.le scheduleH_pos.le) (abs_nonneg _)
  by_cases hs0 : s=0
  · simp only [hs0,min_eq_right hr,zero_mul]
    exact mul_nonneg (div_nonneg Real.pi_pos.le scheduleH_pos.le) (abs_nonneg _)
  have hr' : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hs' : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  simp only [theta,not_le.mpr hr',not_le.mpr hs',↓reduceIte]
  calc
    _ ≤ min r s*((Real.pi/scheduleH)*|Real.log r-Real.log s|) :=
      mul_le_mul_of_nonneg_left (thetaLog_distance J _ _) (le_min hr hs)
    _ = (Real.pi/scheduleH)*(min r s*|Real.log r-Real.log s|) := by ring
    _ ≤ (Real.pi/scheduleH)*|r-s| := mul_le_mul_of_nonneg_left (min_mul_log_distance hr' hs')
      (div_nonneg Real.pi_pos.le scheduleH_pos.le)

end
end C0Absorption

end OAI
