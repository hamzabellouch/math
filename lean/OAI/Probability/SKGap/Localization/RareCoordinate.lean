import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators

lemma gaussian_standard_subgaussian : HasSubgaussianMGF (fun x : ℝ=>x) 1 (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    change mgf id (gaussianReal 0 1) t ≤ _
    rw [mgf_id_gaussianReal]
    simp

lemma gaussian_observation_small {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s=1 ∨ s= -1) :
    (gaussianReal 0 1).real {z : ℝ | |T*s+sqrt T*z| < T/2} ≤ exp (-T/8) := by
  have ht : 0 < sqrt T := sqrt_pos.mpr hT
  have ht2 := sq_sqrt hT.le
  rcases hs with rfl | rfl
  · have hsub : {z : ℝ | |T*1+sqrt T*z| < T/2} ⊆ {z | sqrt T/2 ≤ -z} := by
      intro z hz
      change |T*1+sqrt T*z| < T/2 at hz
      have hz' := (abs_lt.mp hz).2
      have hm : sqrt T/2*sqrt T ≤ -z*sqrt T := by nlinarith only [hz',ht2]
      exact le_of_mul_le_mul_right hm ht
    apply (measureReal_mono hsub (measure_ne_top _ _)).trans
    have hh := gaussian_standard_subgaussian.neg.measure_ge_le (show 0 ≤ sqrt T/2 by positivity)
    have he : -(sqrt T/2)^2/(2*(1:ℝ))= -T/8 := by
      simp only [div_pow,ht2]
      ring
    simpa only [NNReal.coe_one,Pi.neg_apply,he] using hh
  · have hsub : {z : ℝ | |T*(-1)+sqrt T*z| < T/2} ⊆ {z | sqrt T/2 ≤ z} := by
      intro z hz
      change |T*(-1)+sqrt T*z| < T/2 at hz
      have hz' := (abs_lt.mp hz).1
      have hm : sqrt T/2*sqrt T ≤ z*sqrt T := by nlinarith only [hz',ht2]
      exact le_of_mul_le_mul_right hm ht
    apply (measureReal_mono hsub (measure_ne_top _ _)).trans
    have hh := gaussian_standard_subgaussian.measure_ge_le (show 0 ≤ sqrt T/2 by positivity)
    have he : -(sqrt T/2)^2/(2*(1:ℝ))= -T/8 := by
      simp only [div_pow,ht2]
      ring
    simpa only [NNReal.coe_one,he] using hh

variable {ι : Type*} [Fintype ι] {E : ι→Type*} [∀ i,MeasurableSpace (E i)]

def rareCount (B : ∀ i,Set (E i)) (x : ∀ i,E i) : ℝ := by
  classical
  exact ∑ i,if x i∈B i then 1 else 0

lemma rareCount_measurable (B : ∀ i,Set (E i)) (hB : ∀ i,MeasurableSet (B i)) :
    Measurable (rareCount B) := by
  classical
  unfold rareCount
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_const (a:=(1:ℝ))).indicator (hB i)).comp (measurable_pi_apply i)

omit [∀ i,MeasurableSpace (E i)] in
lemma rareCount_bounds (B : ∀ i,Set (E i)) (x : ∀ i,E i) :
    0 ≤ rareCount B x ∧ rareCount B x ≤ Fintype.card ι := by
  classical
  constructor
  · exact Finset.sum_nonneg (fun i _=>by split_ifs <;> norm_num)
  · apply (Finset.sum_le_sum (g:=fun _=>(1:ℝ)) (fun i _=>by split_ifs <;> norm_num)).trans_eq
    simp

lemma rareCount_exp_integral (μ : ∀ i,Measure (E i)) [∀ i,IsProbabilityMeasure (μ i)]
    (B : ∀ i,Set (E i)) (hB : ∀ i,MeasurableSet (B i)) :
    (∫ x,exp (rareCount B x) ∂Measure.pi μ)=∏ i,(1+((μ i).real (B i))*(exp 1-1)) := by
  classical
  have hi (i : ι) : (∫ z,exp (if z∈B i then (1:ℝ) else 0) ∂μ i)=
      1+(μ i).real (B i)*(exp 1-1) := by
    have he : (fun z=>exp (if z∈B i then (1:ℝ) else 0))=
        fun z=>1+(B i).indicator (fun _=>exp 1-1) z := by
      funext z
      by_cases hz : z∈B i <;> simp [hz]
    rw [he,integral_add (integrable_const _) ((integrable_const _).indicator (hB i)),integral_indicator_const _ (hB i)]
    simp
  simp only [rareCount,exp_sum]
  rw [integral_fintype_prod_eq_prod (μ:=μ) (fun i z=>exp (if z∈B i then (1:ℝ) else 0))]
  exact Finset.prod_congr rfl (fun i _=>hi i)

theorem rareCount_tail (μ : ∀ i,Measure (E i)) [∀ i,IsProbabilityMeasure (μ i)]
    (B : ∀ i,Set (E i)) (hB : ∀ i,MeasurableSet (B i))
    {p a : ℝ} (hp : ∀ i,(μ i).real (B i) ≤ p) :
    (Measure.pi μ).real {x | a < rareCount B x} ≤
      exp (-a+(Fintype.card ι:ℝ)*p*(exp 1-1)) := by
  classical
  have hmono : 0 ≤ exp (1:ℝ)-1 := by linarith only [one_le_exp (by norm_num : (0:ℝ) ≤ 1)]
  have hi : Integrable (fun x=>exp (rareCount B x)) (Measure.pi μ) :=
    Integrable.of_bound (rareCount_measurable B hB |>.exp.aestronglyMeasurable)
      (exp (Fintype.card ι:ℝ)) (ae_of_all _ (fun x=>by
        rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr (rareCount_bounds B x).2))
  have hm := mul_meas_ge_le_integral_of_nonneg (μ:=Measure.pi μ)
    (ae_of_all _ (fun x=>(exp_pos (rareCount B x)).le)) hi (exp a)
  rw [rareCount_exp_integral μ B hB] at hm
  have hset : {x | a < rareCount B x} ⊆ {x | exp a ≤ exp (rareCount B x)} :=
    fun _ hx=>exp_le_exp.mpr hx.le
  have hh := measureReal_mono hset (measure_ne_top (Measure.pi μ) _)
  have hprod : (∏ i,(1+(μ i).real (B i)*(exp 1-1))) ≤
      exp ((Fintype.card ι:ℝ)*p*(exp 1-1)) := by
    have hp' (i : ι) : 1+(μ i).real (B i)*(exp 1-1) ≤ exp (p*(exp 1-1)) := by
      calc
        _ ≤ 1+p*(exp 1-1) := add_le_add_right (mul_le_mul_of_nonneg_right (hp i) hmono) 1
        _ ≤ _ := by linarith only [add_one_le_exp (p*(exp 1-1))]
    calc
      _ ≤ ∏ _i : ι,exp (p*(exp 1-1)) := Finset.prod_le_prod₀
        (fun i _=>add_nonneg (by norm_num) (mul_nonneg (measureReal_nonneg) hmono)) (fun i _=>hp' i)
      _ = _ := by rw [Finset.prod_const,Finset.card_univ,← exp_nat_mul];congr 1;ring
  have hm' := (mul_le_mul_of_nonneg_left hh (exp_pos a).le).trans (hm.trans hprod)
  have he : exp (-a+(Fintype.card ι:ℝ)*p*(exp 1-1))=
      exp ((Fintype.card ι:ℝ)*p*(exp 1-1))/exp a := by rw [← exp_sub];congr 1;ring
  rw [he]
  apply (le_div_iff₀ (exp_pos a)).mpr
  simpa only [mul_comm] using hm'
end SKGap

end
end

end OAI
