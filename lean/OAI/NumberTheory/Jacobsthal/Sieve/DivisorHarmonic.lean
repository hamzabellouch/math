import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace ErdosHyperbola

noncomputable def harmonicWeight (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, 1/(n : ℝ)

theorem harmonicWeight_nonneg (N : ℕ) : 0 ≤ harmonicWeight N := by
  unfold harmonicWeight
  positivity

theorem multiple_reciprocal_sum_le (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), 1/(n : ℝ)) ≤
      (1/(d : ℝ))*harmonicWeight N := by
  let S := (Finset.Icc 1 N).filter (d ∣ ·)
  let f : ℕ → ℕ := fun n => n/d
  have hi : Set.InjOn f (S : Set ℕ) := by
    intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    calc
      a = d*(a/d) := (Nat.mul_div_cancel' ha').symm
      _ = d*(b/d) := by rw [show a/d = b/d from he]
      _ = b := Nat.mul_div_cancel' hb'
  have hsub : S.image f ⊆ Finset.Icc 1 N := by
    intro j hj
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hnI,hnD⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1,hnN⟩ := Finset.mem_Icc.mp hnI
    have he := Nat.mul_div_cancel' hnD
    have hjp : 0 < (n/d : ℕ) := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz,mul_zero] at he
      omega
    exact Finset.mem_Icc.mpr ⟨hjp,(Nat.div_le_self n d).trans hnN⟩
  have heq : (∑ n ∈ S, 1/(n : ℝ)) =
      (1/(d : ℝ)) * ∑ j ∈ S.image f, 1/(j : ℝ) := by
    rw [Finset.mul_sum,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnD := (Finset.mem_filter.mp hn).2
      dsimp only [f]
      rw [one_div_mul_one_div,← Nat.cast_mul,Nat.mul_div_cancel' hnD]
    · exact fun a ha b hb he => hi ha hb he
  change (∑ n ∈ S, 1/(n : ℝ)) ≤ _
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

theorem sqrt_multiple_sum_le (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·), Real.sqrt d/(n : ℝ)) ≤ harmonicWeight N := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith⟩
  have hs : Real.sqrt (d : ℝ)/(d : ℝ) ≤ 1 := (div_le_one hdp).mpr hsqrt
  calc
    _ = Real.sqrt d * (∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·),1/(n : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ Real.sqrt d * ((1/(d : ℝ))*harmonicWeight N) :=
      mul_le_mul_of_nonneg_left (multiple_reciprocal_sum_le N d hd) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (d : ℝ)/(d : ℝ))*harmonicWeight N := by ring
    _ ≤ 1*harmonicWeight N := mul_le_mul_of_nonneg_right hs (harmonicWeight_nonneg N)
    _ = _ := one_mul _

theorem gcd_harmonic_sum_le (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 1 N, Real.sqrt (Nat.gcd n N)/(n : ℝ)) ≤
      (N.divisors.card : ℝ)*harmonicWeight N := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ N.divisors,
        if d ∣ n then Real.sqrt d/(n : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      have hg : Nat.gcd n N ∈ N.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,Nat.ne_of_gt hN⟩
      have h := Finset.single_le_sum (s := N.divisors)
        (f := fun d => if d ∣ n then Real.sqrt d/(n : ℝ) else 0)
        (fun _ _ => by positivity) hg
      simpa only [ite_eq_left (Nat.gcd_dvd_left n N)] using h
    _ = ∑ d ∈ N.divisors,
        ∑ n ∈ (Finset.Icc 1 N).filter (d ∣ ·),Real.sqrt d/(n : ℝ) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ _d ∈ N.divisors,harmonicWeight N := by
      apply Finset.sum_le_sum
      intro d hd
      exact sqrt_multiple_sum_le N d (Nat.pos_of_mem_divisors hd)
    _ = _ := by simp

end ErdosHyperbola

end

end Erdos970

end OAI
