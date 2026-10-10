import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H]

variable (x : ℕ → H)

def weight (n : ℕ) : ℝ := (1/2:ℝ)^n/(1+‖x n‖^2)

lemma weight_pos (n : ℕ) : 0<weight x n := by
  apply div_pos
  · positivity
  · positivity

lemma weight_norm_bound (n : ℕ) : weight x n*‖x n‖^2≤(1/2:ℝ)^n := by
  have hd : 0<1+‖x n‖^2 := by positivity
  rw [weight,div_mul_eq_mul_div,div_le_iff₀ hd]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) n]

variable [InnerProductSpace ℂ H]

def term (n : ℕ) (T : H →L[ℂ] H) : ℂ :=
  (weight x n:ℂ)*inner ℂ (x n) (T (x n))

lemma term_bound (n : ℕ) (T : H →L[ℂ] H) : ‖term x n T‖≤(1/2:ℝ)^n*‖T‖ := by
  rw [term,norm_mul,Complex.norm_real,Real.norm_of_nonneg (weight_pos x n).le]
  calc
    _≤weight x n*(‖x n‖*(‖T‖*‖x n‖)) := mul_le_mul_of_nonneg_left
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)))
      (weight_pos x n).le
    _=(weight x n*‖x n‖^2)*‖T‖ := by ring
    _≤_ := mul_le_mul_of_nonneg_right (weight_norm_bound x n) (norm_nonneg T)

lemma term_summable (T : H →L[ℂ] H) : Summable (fun n => term x n T) :=
  ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_right ‖T‖).of_norm_bounded
    (fun n => term_bound x n T)

lemma term_add (n : ℕ) (S T : H →L[ℂ] H) : term x n (S+T)=term x n S+term x n T := by
  simp [term,mul_add]

lemma term_smul (n : ℕ) (z : ℂ) (T : H →L[ℂ] H) : term x n (z•T)=z*term x n T := by
  simp only [term,smul_apply,inner_smul_right]
  ring

lemma term_nonneg (n : ℕ) {T : H →L[ℂ] H} (hT : 0≤T) : 0≤term x n T := by
  apply mul_nonneg (Complex.zero_le_real.mpr (weight_pos x n).le)
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).inner_nonneg_right _

def functional : (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toFun T := ∑' n,term x n T
  map_add' S T := by simp_rw [term_add]; exact (term_summable x S).tsum_add (term_summable x T)
  map_smul' z T := by simp_rw [term_smul,tsum_mul_left]; rfl
  monotone' := by
    intro S T hST
    have hnon : 0≤∑' n,term x n (T-S) := tsum_nonneg (fun n => term_nonneg x n (sub_nonneg.mpr hST))
    have hsub : (∑' n,term x n (T-S))=(∑' n,term x n T)-(∑' n,term x n S) := by
      rw [←(term_summable x T).tsum_sub (term_summable x S)]
      congr 1
      ext n
      simp [term,mul_sub]
    rw [hsub] at hnon
    exact sub_nonneg.mp hnon

variable [CompleteSpace H]

lemma functional_faithful (hd : DenseRange x) (T : H →L[ℂ] H)
    (hz : functional x (star T*T)=0) : T=0 := by
  have hzero (n : ℕ) : T (x n)=0 := by
    have hterm : term x n (star T*T)=0 := by
      apply le_antisymm ?_ (term_nonneg x n (star_mul_self_nonneg _))
      have ht := (term_summable x (star T*T)).le_tsum n
        (fun j _ => term_nonneg x j (star_mul_self_nonneg _))
      exact ht.trans_eq hz
    change (weight x n:ℂ)*inner ℂ (x n) (T.adjoint (T (x n)))=0 at hterm
    rw [ContinuousLinearMap.adjoint_inner_right] at hterm
    exact inner_self_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (weight_pos x n))))
  ext y
  exact hd.induction_on y (isClosed_eq T.continuous continuous_const) hzero

lemma functional_boundedWOT (C : ℝ) :
    Continuous (fun a : {T : H →WOT[ℂ] H // ‖T.toCLM‖≤C} => functional x a.val.toCLM) := by
  apply continuous_tsum
    (u:=fun n => (1/2:ℝ)^n*max C 0)
  · intro n
    exact continuous_const.mul (ContinuousLinearMapWOT.continuous_inner_apply
      continuous_subtype_val (x n) (x n))
  · exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_right _
  · intro n a
    exact (term_bound x n a.val.toCLM).trans (mul_le_mul_of_nonneg_left
      (a.property.trans (le_max_left _ _)) (by positivity))

end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
