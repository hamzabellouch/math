import OAI.Combinatorics.EditDistance.LowerParameters

namespace OAI

/-!
# Inverting recursive depth for all sufficiently large lengths
-/

namespace EditDepth
open Filter

noncomputable def radius (t : ℝ) := Real.sqrt (t / Real.log t)
noncomputable def depth (t : ℝ) : ℕ := ⌊radius t / 100⌋₊

lemma radius_nonneg (t : ℝ) : 0 ≤ radius t := Real.sqrt_nonneg _

lemma eventually_radius_large (K : ℕ) :
    ∀ᶠ t : ℝ in atTop, (100 : ℝ)*(K+2) ≤ radius t := by
  let R : ℝ := 100*((K : ℝ)+2)
  have hR : 0 < R := by dsimp [R]; positivity
  have he : 0 < 1/R^2 := by positivity
  have hlog := Real.isLittleO_log_id_atTop.def he
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hlog,hl,eventually_ge_atTop (1 : ℝ)] with t ht hlt htp
  have tp : 0 < t := by linarith
  have lp : 0 < Real.log t := by linarith
  have ht' : Real.log t ≤ t/R^2 := by
    simpa only [Function.id_def,Real.norm_eq_abs,abs_of_pos tp,abs_of_pos lp,div_eq_mul_inv,one_mul,mul_comm] using ht
  have hs : R^2 ≤ t/Real.log t := by
    apply (le_div_iff₀ lp).mpr
    have hb := (le_div_iff₀ (sq_pos_of_pos hR)).mp ht'
    nlinarith
  exact Real.le_sqrt_of_sq_le hs

lemma depth_lower {t : ℝ} (ht : 200 ≤ radius t) : radius t/200 ≤ (depth t : ℝ) := by
  have hf := Nat.lt_floor_add_one (radius t/100)
  change radius t/100 < (depth t : ℝ)+1 at hf
  linarith

lemma depth_upper (t : ℝ) : (depth t : ℝ) ≤ radius t/100 :=
  Nat.floor_le (div_nonneg (radius_nonneg t) (by norm_num))

lemma depth_bounds {t : ℝ} (ht : 1 ≤ t) (hlt : 1 ≤ Real.log t)
    (hr : 200 ≤ radius t) (hll : Real.log (Real.log t) ≤ Real.log t/6)
    (hlarge : 12*Real.log (200 : ℝ) ≤ Real.log t) :
    1000*(depth t : ℝ)^2*Real.log (depth t : ℝ) ≤ t ∧
      Real.sqrt (t*Real.log t)/1200 ≤ (1/2 : ℝ)*(depth t : ℝ)*Real.log (depth t : ℝ) := by
  have tp : 0 < t := by linarith
  have lp : 0 < Real.log t := by linarith
  have rp : 0 < radius t := by linarith
  have kp : 0 < (depth t : ℝ) := lt_of_lt_of_le (by positivity) (depth_lower hr)
  have hr2 : radius t^2 = t/Real.log t := Real.sq_sqrt (div_nonneg tp.le lp.le)
  have hr2' : radius t^2*Real.log t = t := (eq_div_iff lp.ne').mp hr2
  have hrle : radius t ≤ t := by
    have hdiv : t/Real.log t ≤ t := (div_le_iff₀ lp).mpr (by nlinarith)
    nlinarith [radius_nonneg t]
  have hkle : (depth t : ℝ) ≤ t := by
    have hh := depth_upper t
    nlinarith [radius_nonneg t]
  have logupper : Real.log (depth t : ℝ) ≤ Real.log t := Real.log_le_log kp hkle
  have loglower : Real.log t/3 ≤ Real.log (depth t : ℝ) := by
    have hlog := Real.log_le_log (by positivity : 0 < radius t/200) (depth_lower hr)
    have logR : Real.log (radius t) = (Real.log t - Real.log (Real.log t))/2 := by
      dsimp [radius]
      rw [Real.log_sqrt (div_nonneg tp.le lp.le),Real.log_div tp.ne' lp.ne']
    rw [Real.log_div rp.ne' (by norm_num),logR] at hlog
    linarith
  have hsq : (depth t : ℝ)^2 ≤ radius t^2/10000 := by
    have hh := depth_upper t
    nlinarith [sq_nonneg (radius t/100-(depth t : ℝ))]
  have hsqrt : Real.sqrt (t*Real.log t) = radius t*Real.log t := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    nlinarith [congrArg (fun x : ℝ => x*Real.log t) hr2']
  constructor
  · calc
      _ ≤ 1000*(depth t : ℝ)^2*Real.log t := mul_le_mul_of_nonneg_left logupper (by positivity)
      _ ≤ t := by
        have hh := mul_le_mul_of_nonneg_right hsq lp.le
        nlinarith
  · rw [hsqrt]
    have hh : radius t/200*(Real.log t/3) ≤ (depth t : ℝ)*Real.log (depth t : ℝ) := by
      gcongr
      · exact depth_lower hr
    linarith

theorem eventually_choose_depth (K : ℕ) : ∀ᶠ t : ℝ in atTop,
    K ≤ depth t ∧ 1000*(depth t : ℝ)^2*Real.log (depth t : ℝ) ≤ t ∧
      Real.sqrt (t*Real.log t)/1200 ≤ (1/2 : ℝ)*(depth t : ℝ)*Real.log (depth t : ℝ) := by
  have hsmall := Real.isLittleO_log_id_atTop.def (by norm_num : (0 : ℝ)<1/6)
  have hsmall' := Real.tendsto_log_atTop.eventually hsmall
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hh := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (12*Real.log (200 : ℝ)))
  filter_upwards [eventually_radius_large K,hsmall',hl,hh,eventually_ge_atTop (1 : ℝ)] with t hr hs hl hh ht
  have hK : (K : ℝ) ≤ radius t/100 := by nlinarith
  have hr' : 200 ≤ radius t := by have := Nat.cast_nonneg (α := ℝ) K; nlinarith
  have hll : Real.log (Real.log t) ≤ Real.log t/6 := by
    have hlog := Real.log_nonneg hl
    have hpos : 0 ≤ Real.log t := by linarith
    simpa only [Function.id_def,Real.norm_eq_abs,abs_of_nonneg hlog,abs_of_nonneg hpos,
      div_eq_mul_inv,one_mul,mul_comm] using hs
  exact ⟨Nat.le_floor hK,depth_bounds ht hl hr' hll hh⟩

end EditDepth

end OAI
