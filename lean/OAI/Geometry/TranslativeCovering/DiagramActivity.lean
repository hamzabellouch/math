import OAI.Geometry.TranslativeCovering.DiagramSelfBounds

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3

namespace DiagramActivity
open MeasureTheory CellMatching PoissonDiagrams
open scoped BigOperators Classical
variable {Ω : Type u_1} {I : Type u_2} {J : Type u_3} [MeasurableSpace Ω] [Fintype I] [Fintype J]

lemma prod_exp_log (a : I → ℝ) (ha : ∀ i,0 < a i) :
    ∏ i,a i = Real.exp (∑ i,Real.log (a i)) := by
  rw [Real.exp_sum]
  simp_rw [Real.exp_log (ha _)]

lemma activity_lower (μ : Measure Ω) (E : I → Set Ω) (hpos : ∀ i,0 < μ.real (E i))
    {B : ℝ} (hbudget : ∑ i,Real.log (1+(μ.real (E i))⁻¹) ≤ B) :
    Real.exp (-B) ≤ ∏ i,μ.real (E i) := by
  rw [prod_exp_log _ hpos]
  apply Real.exp_le_exp.mpr
  have hh : ∑ i,-Real.log (μ.real (E i)) ≤ ∑ i,Real.log (1+(μ.real (E i))⁻¹) := by
    apply Finset.sum_le_sum
    intro i _
    rw [← Real.log_inv]
    apply Real.log_le_log (inv_pos.mpr (hpos i))
    linarith
  rw [Finset.sum_neg_distrib] at hh
  linarith

omit [Fintype I] in
lemma self_normalized_weight_le (μ : Measure Ω) (E : I → Set Ω)
    (hpos : ∀ i,0 < μ.real (E i)) (i j : I) :
    μ.real (E i ∩ E j)/
      Real.sqrt (μ.real (E i)*(1+μ.real (E i))*μ.real (E j)*(1+μ.real (E j))) ≤
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*μ.real (E j)) := by
  apply div_le_div_of_nonneg_left measureReal_nonneg (Real.sqrt_pos.mpr (mul_pos (hpos i) (hpos j)))
  apply Real.sqrt_le_sqrt
  have hi := hpos i
  have hj := hpos j
  nlinarith [mul_pos hi hj,mul_nonneg hi.le hi.le,mul_nonneg hj.le hj.le,
    mul_nonneg (mul_nonneg hi.le hi.le) hj.le,mul_nonneg hi.le (mul_nonneg hj.le hj.le),
    mul_nonneg (mul_nonneg hi.le hi.le) (mul_nonneg hj.le hj.le)]

lemma self_activity (μ : Measure Ω) (E : I → Set Ω) (hpos : ∀ i,0 < μ.real (E i))
    {B T : ℝ} (hfirst : ∑ i,Real.log (1+(μ.real (E i))⁻¹) ≤ B)
    (hrow : ∑ i,Real.log (1+∑ j ∈ Finset.univ.erase i,
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*μ.real (E j))) ≤ T) :
    diagram μ E E ≤ (∏ i,μ.real (E i))^2*Real.exp (B+T) := by
  have hprod : 0 < (∏ i,μ.real (E i))^2 := sq_pos_of_pos (Finset.prod_pos fun i _ => hpos i)
  have hb := self_bound μ E hpos
  have hnorm : (∏ i,(1+∑ j ∈ Finset.univ.erase i,
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*(1+μ.real (E i))*μ.real (E j)*(1+μ.real (E j))))) ≤
      ∏ i,(1+∑ j ∈ Finset.univ.erase i,
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*μ.real (E j))) := by
    apply Finset.prod_le_prod₀
    · intro i _; positivity
    · intro i _
      apply add_le_add le_rfl
      exact Finset.sum_le_sum (fun j _ => self_normalized_weight_le μ E hpos i j)
  have hfirstprod : (∏ i,(1+(μ.real (E i))⁻¹)) ≤ Real.exp B := by
    rw [prod_exp_log _ (fun i => by positivity)]
    exact Real.exp_le_exp.mpr hfirst
  have hrowprod : (∏ i,(1+∑ j ∈ Finset.univ.erase i,
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*μ.real (E j)))) ≤ Real.exp T := by
    rw [prod_exp_log _ (fun i => by positivity)]
    exact Real.exp_le_exp.mpr hrow
  have hh := hb.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have hmul := mul_le_mul hfirstprod hrowprod (by positivity) (Real.exp_pos B).le
  rw [← Real.exp_add] at hmul
  have hdiv : diagram μ E E/(∏ i,μ.real (E i))^2 ≤ Real.exp (B+T) := by linarith
  exact (div_le_iff₀ hprod).mp hdiv |>.trans_eq (mul_comm _ _)

lemma activity_upper (μ : Measure Ω) (E : I → Set Ω) (hle : ∀ i,μ.real (E i) ≤ 1) :
    ∏ i,μ.real (E i) ≤ 1 := Finset.prod_le_one₀ (fun _ _ => measureReal_nonneg) (fun i _ => hle i)

lemma cross_zero (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω)
    (hzero : ∀ i j,μ.real (E i ∩ F j) = 0) : diagram μ E F = 0 := by
  unfold diagram
  suffices (∑ M : Matching I J, if M.val.Nonempty then
      ∏ ij ∈ M.val,μ.real (E ij.1 ∩ F ij.2)/(μ.real (E ij.1)*μ.real (F ij.2)) else 0) = 0 by rw [this,mul_zero]
  apply Finset.sum_eq_zero
  intro M _
  split_ifs with hM
  · obtain ⟨e,he⟩ := hM
    exact Finset.prod_eq_zero he (by rw [hzero,zero_div])
  · rfl

lemma self_activity_normalized (μ : Measure Ω) (E : I → Set Ω) (hpos : ∀ i,0 < μ.real (E i))
    {B T : ℝ} (hfirst : ∑ i,Real.log (1+(μ.real (E i))⁻¹) ≤ B)
    (hrow : ∑ i,Real.log (1+∑ j ∈ Finset.univ.erase i,
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*(1+μ.real (E i))*μ.real (E j)*(1+μ.real (E j)))) ≤ T) :
    diagram μ E E ≤ (∏ i,μ.real (E i))^2*Real.exp (B+T) := by
  have hprod : 0 < (∏ i,μ.real (E i))^2 := sq_pos_of_pos (Finset.prod_pos fun i _ => hpos i)
  have hfirstprod : (∏ i,(1+(μ.real (E i))⁻¹)) ≤ Real.exp B := by
    rw [prod_exp_log _ (fun i => by positivity)]
    exact Real.exp_le_exp.mpr hfirst
  have hrowprod : (∏ i,(1+∑ j ∈ Finset.univ.erase i,
      μ.real (E i ∩ E j)/Real.sqrt (μ.real (E i)*(1+μ.real (E i))*μ.real (E j)*(1+μ.real (E j))))) ≤ Real.exp T := by
    rw [prod_exp_log _ (fun i => by positivity)]
    exact Real.exp_le_exp.mpr hrow
  have hh := self_bound μ E hpos
  have hmul := mul_le_mul hfirstprod hrowprod (by positivity) (Real.exp_pos B).le
  rw [← Real.exp_add] at hmul
  have hh2 : diagram μ E E/(∏ i,μ.real (E i))^2 ≤ Real.exp (B+T) := by linarith only [hh.trans hmul]
  exact (div_le_iff₀ hprod).mp hh2 |>.trans_eq (mul_comm _ _)

end DiagramActivity

end OAI
