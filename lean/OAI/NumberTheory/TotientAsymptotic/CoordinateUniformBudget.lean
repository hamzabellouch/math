import OAI.NumberTheory.TotientAsymptotic.CoordinateDeviationCount

namespace OAI

/-! A single numerical threshold implies all budgets in the deviation count. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_decay_small {ω : ℝ} {k : ℕ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1) :
    coordinateDecay ω k ≤ 1/12000000 := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hp : 1 ≤ ((k:ℝ)+2)^6 := one_le_pow₀ (by linarith)
  have hsq : ω^2 ≤ 1 := by nlinarith
  unfold coordinateDecay
  apply (div_le_iff₀ (by positivity : 0 < 12000000*((k:ℝ)+2)^6)).mpr
  nlinarith only [hsq,hp]

lemma coordinate_decay_scaled (b ω : ℝ) (k : ℕ) :
    coordinateDecay ω k*b*((k:ℝ)+2)^6=ω^2*b/12000000 := by
  unfold coordinateDecay
  field_simp

lemma coordinate_uniform_budget {b ω F : ℝ} {k : ℕ}
    (hb : 300000000 ≤ b) (hω : 0 ≤ ω) (hω1 : ω ≤ 1) (hF : 0 ≤ F)
    (hbudget : 100*(Real.log (b+4)+F+30)^2 ≤ coordinateDecay ω k*b) :
    Real.log (20*b)+2 ≤ b/10000 ∧
    4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6) ∧
    (Real.log (20*b)+9+F+Real.log (b+1))*((k:ℝ)+2)^2 ≤ ω*b/100 ∧
    3*b ≤ Real.exp ((coordinateBottom b ω k:ℝ)-1) ∧
    9*(Real.log (b+4))^2+6*Real.log (b+4) ≤ coordinateDecay ω k*b := by
  let l := Real.log (b+4)
  let S := l+F+30
  let d := coordinateDecay ω k*b
  have hb0 : 0 < b := by linarith
  have hl : 0 ≤ l := Real.log_nonneg (by linarith)
  have hS : 30 ≤ S := by dsimp [S]; linarith
  have h2S : 2*S ≤ d := by
    change 100*S^2 ≤ d at hbudget
    nlinarith only [hbudget,hS]
  have hsmall : d ≤ b/12000000 := by
    have hh := mul_le_mul_of_nonneg_right (coordinate_decay_small (k:=k) hω hω1) hb0.le
    change coordinateDecay ω k*b ≤ _
    linarith only [hh]
  have hlogb : Real.log b ≤ l := Real.log_le_log hb0 (by linarith)
  have hlogb1 : Real.log (b+1) ≤ l := Real.log_le_log (by linarith) (by linarith)
  have hlog20 : Real.log (20*b) ≤ l+19 := by
    rw [Real.log_mul (by norm_num : (20:ℝ)≠0) hb0.ne']
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<20)
    linarith only [hh,hlogb]
  have hcoefficient : Real.log (20*b)+9+F+Real.log (b+1) ≤ 2*S := by
    dsimp [S]
    linarith only [hlog20,hlogb1,hF]
  have hlogbudget : Real.log (20*b)+2 ≤ b/10000 := by
    have hh : Real.log (20*b)+2 ≤ 2*S := by dsimp [S]; linarith only [hlog20,hl,hF]
    linarith only [hh,h2S,hsmall,hb0]
  have htwelve : ω^2*b/(1000000*((k:ℝ)+2)^6)=12*d := by
    dsimp [d,coordinateDecay]
    field_simp
    ring
  have hlarge : 4 ≤ ω^2*b/(1000000*((k:ℝ)+2)^6) := by
    rw [htwelve]
    linarith only [h2S,hS]
  have hdm : d*((k:ℝ)+2)^6 ≤ ω^2*b/1000000 := by
    rw [show d*((k:ℝ)+2)^6=ω^2*b/12000000 from coordinate_decay_scaled b ω k]
    have hn : 0 ≤ ω^2*b := by positivity
    linarith only [hn]
  have hd0 : 0 ≤ d := by dsimp [d]; exact mul_nonneg (coordinate_decay_bounds (k:=k) hω hω1).1 hb0.le
  have hlin := coordinate_linear_budget hb0.le hω hω1 hd0
    (show 1 ≤ (k:ℝ)+2 by have hk := Nat.cast_nonneg (α:=ℝ) k; linarith) hdm
  have hgrid : (Real.log (20*b)+9+F+Real.log (b+1))*((k:ℝ)+2)^2 ≤ ω*b/100 := by
    have hh := mul_le_mul_of_nonneg_right (hcoefficient.trans h2S) (sq_nonneg ((k:ℝ)+2))
    have hn := mul_nonneg hω hb0.le
    linarith only [hh,hlin,hn]
  have hsize : 3*b ≤ Real.exp ((coordinateBottom b ω k:ℝ)-1) := by
    have hbot := (coordinate_bottom_bounds hb0.le hω hω1 hlarge).2.2.2
    rw [htwelve] at hbot
    have hlog3 : Real.log (3*b) ≤ l+2 := by
      rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hb0.ne']
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
      linarith only [hh,hlogb]
    have hh : Real.log (3*b) ≤ (coordinateBottom b ω k:ℝ)-1 := by
      dsimp [S] at h2S hS
      linarith only [hlog3,hbot,h2S,hS,hF,hl]
    exact (Real.exp_log (by positivity : 0 < 3*b)) ▸ Real.exp_le_exp.mpr hh
  refine ⟨hlogbudget,hlarge,hgrid,hsize,?_⟩
  change 100*S^2 ≤ d at hbudget
  change 9*l^2+6*l ≤ d
  have hSl : l ≤ S := by dsimp [S]; linarith
  have hsquares : l^2 ≤ S^2 := by nlinarith only [hl,hS,hSl]
  nlinarith only [hbudget,hsquares,hl,hS,hSl]

end TotientAsymptotic

end

end OAI
