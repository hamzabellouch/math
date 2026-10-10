import OAI.NumberTheory.Jacobsthal.Estimates.SourceSamplePopulation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling
attribute [local instance] Classical.decEq

noncomputable def primeCost (U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (p : ℕ) (s : Sample U h) : ℝ :=
  ((p : ℝ)/(M0 : ℝ))*(∑ v : ZMod M0,∏ i : Fin h,((E p v (s i)).card : ℝ)/((s i).val : ℝ))+
    (M0 : ℝ)*(∏ i : Fin h,((s i).val : ℝ))

theorem primeCost_nonneg (U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (p : ℕ) (s : Sample U h) :
    0 ≤ primeCost U h M0 E p s := by unfold primeCost;positivity

theorem primeCost_average_bound (U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (p : ℕ) (tau T : ℝ)
    (hU : 0 < U.card) (hh : h ≤ U.card)
    (hPref : (U.card : ℝ)^h/(U.card.descFactorial h : ℝ) ≤ 2)
    (hMean : ∀ v : ZMod M0,(∑ u : U,((E p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ) ≤ tau)
    (hCap : ∀ u : U,(u.val : ℝ) ≤ T) :
    sampleAverage U h (primeCost U h M0 E p) ≤ 2*(p : ℝ)*tau^h+(M0 : ℝ)*T^h := by
  have hRatio : ∀ (v : ZMod M0) (u : U),0 ≤ ((E p v u).card : ℝ)/(u.val : ℝ) := by
    intro v u
    positivity
  have hProduct : ∀ v : ZMod M0,
      sampleAverage U h (fun s => ∏ i : Fin h,((E p v (s i)).card : ℝ)/((s i).val : ℝ)) ≤ 2*tau^h := by
    intro v
    have hm0 : 0 ≤ (∑ u : U,((E p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ) :=
      div_nonneg (Finset.sum_nonneg (fun u _ => hRatio v u)) (Nat.cast_nonneg _)
    calc
      _ ≤ ((U.card : ℝ)^h/(U.card.descFactorial h : ℝ))*
          ((∑ u : U,((E p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ))^h :=
        sample_product_average_le U h (fun u => ((E p v u).card : ℝ)/(u.val : ℝ)) (hRatio v) hU hh
      _ ≤ 2*tau^h := mul_le_mul hPref (pow_le_pow_left₀ hm0 (hMean v) h)
        (pow_nonneg hm0 h) (by norm_num)
  have hRound : sampleAverage U h (fun s => ∏ i : Fin h,((s i).val : ℝ)) ≤ T^h :=
    sampleAverage_product_bound U h hh (fun u => (u.val : ℝ)) T (fun u => Nat.cast_nonneg _) hCap
  have hM : (M0 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M0)
  unfold primeCost
  rw [sampleAverage_add,sampleAverage_mul,sampleAverage_mul,sampleAverage_sum]
  calc
    _ ≤ ((p : ℝ)/(M0 : ℝ))*(∑ _v : ZMod M0,2*tau^h)+(M0 : ℝ)*T^h :=
      add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hProduct v)) (by positivity))
        (mul_le_mul_of_nonneg_left hRound (Nat.cast_nonneg _))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
      field_simp

end ErdosInverseSampleCost

end

end Erdos970

end OAI
