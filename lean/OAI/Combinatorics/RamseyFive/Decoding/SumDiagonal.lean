import Mathlib
import OAI.Combinatorics.RamseyFive.Probability.PositiveTailMoment

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ValidationBounds
open scoped BigOperators Classical

lemma sum_diagonal {H : Type*} [Fintype H] (f : H → H → ℝ) :
    (∑ h,∑ k,f h k) = (∑ h,f h h) +
      ∑ z : {z : H × H // z.1 ≠ z.2},f z.val.1 z.val.2 := by
  classical
  rw [← Fintype.sum_prod_type']
  have he : (∑ z : H × H,f z.1 z.2) =
      (∑ z : H × H with z.1 = z.2,f z.1 z.2) +
      ∑ z : H × H with z.1 ≠ z.2,f z.1 z.2 := by
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun z : H × H => z.1=z.2) _).symm
  rw [he]
  congr 1
  · rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    simp
  · rw [Finset.sum_subtype (Finset.univ.filter fun z : H × H => z.1 ≠ z.2)
      (p := fun z => z.1 ≠ z.2) (by intro z; simp)]

theorem overlap_power_sum {H : Type*} [Fintype H] (θ : H → H → ℝ)
    (hθ0 : ∀ h k,0 ≤ θ h k) (hθ2 : ∀ h k,θ h k ≤ 2)
    (A C : ℝ) (hA : 0 ≤ A) (hcard : (Fintype.card H:ℝ) ≤ C)
    (K R : ℕ) (hR : K+1 ≤ R)
    (htail : ∀ a : ℝ,0 < a → a ≤ 2 →
      ((Finset.univ.filter fun z : {z : H × H // z.1 ≠ z.2} => a ≤ θ z.val.1 z.val.2).card:ℝ)*a^K ≤ A) :
    (∑ h,∑ k,θ h k^R) ≤ (C+2*A)*2^R := by
  rw [sum_diagonal]
  have hd : (∑ h,θ h h^R) ≤ C*2^R := by
    calc
      _ ≤ ∑ _h : H,(2:ℝ)^R := Finset.sum_le_sum fun h _ =>
        pow_le_pow_left₀ (hθ0 h h) (hθ2 h h) R
      _ = Fintype.card H*2^R := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have ho := TailMoment.tail_moment (fun z : {z : H × H // z.1 ≠ z.2} => θ z.val.1 z.val.2)
    (fun z => hθ0 _ _) (fun z => hθ2 _ _) A hA K R hR htail
  exact (add_le_add hd ho).trans_eq (by ring)

lemma validation_budget {B P L : ℝ} {R : ℕ}
    (hP : 100000 ≤ P) (hR : (R:ℝ) ≤ P/100000)
    (hLR : 100*L ≤ P)
    (D S : ℝ) (hD0 : 0 ≤ D) (hD : D ≤ 100*B*Real.exp (L/100))
    (hS : S ≤ (100*B^2+2*(B^2*Real.exp (P/50)))*2^R) :
    D^2+S ≤ B^2*Real.exp (3*P/100) := by
  have hlog : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hpow : (2:ℝ)^R ≤ Real.exp (P/100000) := by
    rw [show (2:ℝ)^R = Real.exp ((R:ℝ)*Real.log 2) by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]]
    apply Real.exp_le_exp.mpr
    calc
      (R:ℝ)*Real.log 2 ≤ (R:ℝ)*1 := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ P/100000 := by simpa using hR
  have hE : 1 ≤ Real.exp (P/50) := Real.one_le_exp (by linarith)
  have hS' : S ≤ 102*B^2*Real.exp (P/50+P/100000) := by
    calc
      S ≤ (100*B^2+2*(B^2*Real.exp (P/50)))*2^R := hS
      _ ≤ (102*B^2*Real.exp (P/50))*Real.exp (P/100000) := by
        apply mul_le_mul _ hpow (by positivity) (by positivity)
        nlinarith [sq_nonneg B,mul_le_mul_of_nonneg_left hE (sq_nonneg B)]
      _ = _ := by rw [Real.exp_add]; ring
  have hD' : D^2 ≤ 10000*B^2*Real.exp (P/5000) := by
    calc
      _ ≤ (100*B*Real.exp (L/100))^2 := pow_le_pow_left₀ hD0 hD 2
      _ = 10000*B^2*Real.exp (2*(L/100)) := by
        rw [show Real.exp (2*(L/100)) = Real.exp (L/100)^2 by
          simpa using Real.exp_nat_mul (L/100) 2]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hD'' : D^2 ≤ 10000*B^2*Real.exp (P/50+P/100000) := hD'.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity))
  have hcoef : (10102:ℝ) ≤ Real.exp (3*P/100-(P/50+P/100000)) := by
    have ht : (100:ℝ) ≤ 3*P/100-(P/50+P/100000) := by linarith
    have he' : (10102:ℝ) ≤ Real.exp (100:ℝ) := by
      have he2 := Real.add_one_le_exp (25:ℝ)
      have he26 : (26:ℝ) ≤ Real.exp 25 := by linarith
      have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤26) he26 4
      rw [← Real.exp_nat_mul] at hp
      norm_num at hp
      exact (by norm_num : (10102:ℝ)≤456976).trans hp
    exact he'.trans (Real.exp_le_exp.mpr ht)
  calc
    D^2+S ≤ 10102*B^2*Real.exp (P/50+P/100000) := by linarith [hD'',hS']
    _ ≤ Real.exp (3*P/100-(P/50+P/100000))*B^2*Real.exp (P/50+P/100000) := by
      gcongr
    _ = _ := by rw [mul_assoc,mul_left_comm,← Real.exp_add]; congr 2; ring

end SharpRamseyFive.ValidationBounds

end OAI
