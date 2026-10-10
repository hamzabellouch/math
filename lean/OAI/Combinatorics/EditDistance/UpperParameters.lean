import OAI.Combinatorics.EditDistance.DepthInversion
import OAI.Combinatorics.EditDistance.UpperRecursion

namespace OAI

/-!
# Branching and depth choices at every sufficiently large length
-/

namespace EditUpperParameters
open Filter

noncomputable def peak (t : ℝ) : ℝ := Real.sqrt (t*Real.log t)
noncomputable def level (t : ℝ) : ℕ := ⌊EditDepth.radius t⌋₊
noncomputable def branching (t : ℝ) : ℕ := ⌈Real.exp (2*peak t)⌉₊

lemma radius_peak {t : ℝ} (ht : 1 ≤ t) (hlt : 1 ≤ Real.log t) :
    EditDepth.radius t * Real.log t = peak t ∧ EditDepth.radius t * peak t = t ∧ 1 ≤ peak t := by
  have tp : 0 < t := by linarith
  have lp : 0 < Real.log t := by linarith
  have hr : 0 ≤ EditDepth.radius t := EditDepth.radius_nonneg t
  have hr2 : EditDepth.radius t^2 = t/Real.log t := Real.sq_sqrt (div_nonneg tp.le lp.le)
  have hr2' : EditDepth.radius t^2*Real.log t = t := (eq_div_iff lp.ne').mp hr2
  have hs : peak t = EditDepth.radius t*Real.log t := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    nlinarith [congrArg (fun x : ℝ => x*Real.log t) hr2']
  refine ⟨hs.symm,?_,?_⟩
  · rw [hs]
    nlinarith [hr2']
  · apply Real.le_sqrt_of_sq_le
    nlinarith

lemma choose_parameters {t : ℝ} (ht : 1 ≤ t) (hlt : 1024 ≤ Real.log t)
    (hr : 2 ≤ EditDepth.radius t) :
    1 ≤ level t ∧ 2 ≤ branching t ∧
      Real.exp t ≤ (branching t : ℝ)^(level t) ∧
      2*((branching t : ℝ)+2)*
        (1024*(1+(level t : ℝ)*Real.log (branching t : ℝ))^2)^(level t) ≤
          Real.exp (32*peak t) := by
  have hlt1 : 1 ≤ Real.log t := by linarith
  obtain ⟨hRS,hRt,hS⟩ := radius_peak ht hlt1
  have hNup : (level t : ℝ) ≤ EditDepth.radius t := Nat.floor_le (EditDepth.radius_nonneg t)
  have hNfloor := Nat.lt_floor_add_one (EditDepth.radius t)
  change EditDepth.radius t < (level t : ℝ)+1 at hNfloor
  have hNlo : EditDepth.radius t/2 ≤ (level t : ℝ) := by linarith
  have hNp : 1 ≤ level t := by
    have hh : (1 : ℝ) ≤ level t := by linarith
    exact_mod_cast hh
  have helo : Real.exp (2*peak t) ≤ (branching t : ℝ) := Nat.le_ceil _
  have hehi : (branching t : ℝ) < Real.exp (2*peak t)+1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hexp : 3 ≤ Real.exp (2*peak t) := by have := Real.add_one_le_exp (2*peak t); linarith
  have hb : 2 ≤ branching t := by
    have hh : (2 : ℝ) ≤ branching t := by linarith
    exact_mod_cast hh
  have hbp : (0 : ℝ) < branching t := by exact_mod_cast (show 0 < branching t by omega)
  have hBnon : 0 ≤ Real.log (branching t : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ branching t by omega))
  have hBlo : 2*peak t ≤ Real.log (branching t : ℝ) := (Real.le_log_iff_exp_le hbp).mpr helo
  have hBup : Real.log (branching t : ℝ) ≤ 3*peak t := by
    have hh : (branching t : ℝ) ≤ 2*Real.exp (2*peak t) := by linarith
    have hl := Real.log_le_log hbp hh
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hl
    have h2 := log_two_bounds
    linarith
  have hBlog : Real.log ((branching t : ℝ)+2) ≤ 5*peak t := by
    have hh : (branching t : ℝ)+2 ≤ 4*Real.exp (2*peak t) := by linarith
    have hl := Real.log_le_log (by positivity : 0 < (branching t : ℝ)+2) hh
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hl
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<4)
    linarith
  have hNnon : 0 ≤ (level t : ℝ) := Nat.cast_nonneg _
  have hNblo : t ≤ (level t : ℝ)*Real.log (branching t : ℝ) := by
    have hh := mul_le_mul hNlo hBlo (by linarith : 0 ≤ 2*peak t) hNnon
    nlinarith [hRt]
  have hNbup : (level t : ℝ)*Real.log (branching t : ℝ) ≤ 3*t := by
    have hh := mul_le_mul hNup hBup hBnon (EditDepth.radius_nonneg t)
    nlinarith [hRt]
  have hcap : Real.exp t ≤ (branching t : ℝ)^(level t) := by
    apply (Real.le_log_iff_exp_le (pow_pos hbp _)).mp
    rw [Real.log_pow]
    exact hNblo
  let T := 1+(level t : ℝ)*Real.log (branching t : ℝ)
  let P := 1024*T^2
  have hT : 0 < T := by dsimp [T]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hTup : T ≤ 4*t := by dsimp [T]; linarith
  have hlogT : Real.log T ≤ 3+Real.log t := by
    have hh := Real.log_le_log hT hTup
    rw [Real.log_mul (by norm_num) (by linarith : t ≠ 0)] at hh
    have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<4)
    linarith
  have hlogP : Real.log P ≤ 4*Real.log t := by
    dsimp [P]
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hT.ne'),Real.log_pow]
    have h1024 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<1024)
    norm_num only [Nat.cast_ofNat]
    linarith
  have hNP : (level t : ℝ)*Real.log P ≤ 4*peak t := by
    have h1 := mul_le_mul_of_nonneg_left hlogP hNnon
    have h2 := mul_le_mul_of_nonneg_right hNup (show 0 ≤ 4*Real.log t by linarith)
    nlinarith [hRS]
  refine ⟨hNp,hb,hcap,?_⟩
  change 2*((branching t : ℝ)+2)*P^(level t) ≤ _
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_mul (by positivity) (pow_ne_zero _ hP.ne'),
    Real.log_mul (by norm_num) (by positivity : ((branching t : ℝ)+2) ≠ 0),Real.log_pow]
  have h2 := log_two_bounds
  nlinarith

theorem eventual_choice : ∀ᶠ d : ℕ in atTop,
    1 ≤ level (Real.log (d : ℝ)) ∧ 2 ≤ branching (Real.log (d : ℝ)) ∧
      d ≤ branching (Real.log (d : ℝ))^level (Real.log (d : ℝ)) ∧
      2*((branching (Real.log (d : ℝ)) : ℝ)+2)*
        (1024*(1+(level (Real.log (d : ℝ)) : ℝ)*Real.log (branching (Real.log (d : ℝ)) : ℝ))^2)^level (Real.log (d : ℝ)) ≤
          Real.exp (32*Real.sqrt (Real.log (d : ℝ)*Real.log (Real.log (d : ℝ)))) := by
  have htend : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := htend.eventually (eventually_ge_atTop (1 : ℝ))
  have h2 := htend.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1024 : ℝ)))
  have h3 := htend.eventually (EditDepth.eventually_radius_large 0)
  filter_upwards [h1,h2,h3,eventually_ge_atTop (1 : ℕ)] with d ht hl hr hd
  have hr' : 2 ≤ EditDepth.radius (Real.log (d : ℝ)) := by norm_num at hr; linarith
  obtain ⟨hN,hb,hcap,hbound⟩ := choose_parameters ht hl hr'
  refine ⟨hN,hb,?_,hbound⟩
  rw [Real.exp_log (by exact_mod_cast (show 0 < d by omega))] at hcap
  exact_mod_cast hcap

end EditUpperParameters

end OAI
