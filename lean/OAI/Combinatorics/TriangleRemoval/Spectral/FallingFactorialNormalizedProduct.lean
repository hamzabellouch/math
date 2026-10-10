import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.UnitTime

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma fallingFactorial_normalized_product (r a n : ℕ) (hn : r+a ≤ n) (hn0 : 0 < n) :
    ((n-r).descFactorial a : ℝ)/(n : ℝ)^a =
      ∏ i ∈ Finset.range a, (1-((r+i : ℕ) : ℝ)/(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]
  have hh : (n : ℝ)^a = ∏ _i ∈ Finset.range a, (n : ℝ) := by simp
  rw [hh,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hri : r+i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [Nat.sub_sub,Nat.cast_sub hri]
  field_simp

theorem fallingFactorial_normalized_error (r a n : ℕ) (hn : r+a ≤ n) (hn0 : 0 < n) :
    |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-1| ≤
      (a : ℝ)*(r+a : ℕ)/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [fallingFactorial_normalized_product r a n hn hn0]
  let f := fun i : ℕ => 1-((r+i : ℕ) : ℝ)/(n : ℝ)
  have hf : ∀ i ∈ Finset.range a, f i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    have hri : r+i ≤ n := by have := Finset.mem_range.mp hi; omega
    have h0 : 0 ≤ ((r+i : ℕ) : ℝ)/(n : ℝ) := by positivity
    have h1 : ((r+i : ℕ) : ℝ)/(n : ℝ) ≤ 1 := by
      apply (div_le_one hnR).mpr
      exact_mod_cast hri
    exact ⟨by dsimp [f]; linarith,by dsimp [f]; linarith⟩
  have hh := abs_prod_sub_prod_le_sum (Finset.range a) f (fun _ => 1) hf
    (fun _ _ => ⟨zero_le_one,le_rfl⟩)
  simp only [Finset.prod_const_one] at hh
  apply hh.trans
  calc
    (∑ i ∈ Finset.range a, |f i-1|) =
        ∑ i ∈ Finset.range a, ((r+i : ℕ) : ℝ)/(n : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      have h0 : 0 ≤ ((r+i : ℕ) : ℝ)/(n : ℝ) := by positivity
      rw [show 1-((r+i : ℕ) : ℝ)/(n : ℝ)-1 = -(((r+i : ℕ) : ℝ)/(n : ℝ)) by ring,
        abs_neg,abs_of_nonneg h0]
    _ ≤ ∑ _i ∈ Finset.range a, ((r+a : ℕ) : ℝ)/(n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply div_le_div_of_nonneg_right _ hnR.le
      exact_mod_cast (by have := Finset.mem_range.mp hi; omega : r+i ≤ r+a)
    _ = _ := by simp; ring

theorem initialDensity_power_error (b n : ℕ) (hn : 1 ≤ n) :
    |(1-1/(n : ℝ))^b-1| ≤ (b : ℝ)/(n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 ≤ 1-1/(n : ℝ) := by
    have : 1/(n : ℝ) ≤ 1 := by apply (div_le_one (by linarith)).mpr; exact hnR
    linarith
  have hp1 : 1-1/(n : ℝ) ≤ 1 := by
    have : 0 ≤ 1/(n : ℝ) := by positivity
    linarith
  have hh := abs_prod_sub_prod_le_sum (Finset.range b) (fun _ => 1-1/(n : ℝ))
    (fun _ => 1) (fun _ _ => ⟨hp0,hp1⟩) (fun _ _ => ⟨zero_le_one,le_rfl⟩)
  simpa only [Finset.prod_const,Finset.card_range,one_pow,
    show 1-1/(n : ℝ)-1 = -(1/(n : ℝ)) by ring,abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1/(n : ℝ)),Finset.sum_const,
    nsmul_eq_mul,mul_one_div] using hh

theorem initialRootedScaling_error (r a b n : ℕ) (hn : r+a ≤ n) (hn2 : 2 ≤ n) :
    |((n-r).descFactorial a : ℝ) /
      ((n : ℝ)^a * (1-1/(n : ℝ))^b)-1| ≤
      (2 : ℝ)^b * ((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : 0 < n := by omega
  have hnR0 : (0 : ℝ) < n := by linarith
  have hp : (1/2 : ℝ) ≤ 1-1/(n : ℝ) := by
    have hh : 1/(n : ℝ) ≤ 1/2 := (div_le_div_iff₀ hnR0 (by norm_num)).mpr (by linarith)
    linarith
  have hp0 : 0 < (1-1/(n : ℝ))^b := pow_pos (by linarith) _
  have hi : 1/(1-1/(n : ℝ))^b ≤ (2 : ℝ)^b := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hp b
    have hh2 : (1/2 : ℝ)^b = 1/(2 : ℝ)^b := by rw [div_pow,one_pow]
    rw [hh2] at hh
    exact (div_le_iff₀ hp0).mpr (by
      have ht : (0 : ℝ) < (2 : ℝ)^b := by positivity
      have hmul := (div_le_iff₀ ht).mp hh
      simpa only [mul_comm] using hmul)
  have hf := fallingFactorial_normalized_error r a n hn hn0
  have ht := initialDensity_power_error b n (by omega)
  have he : |((n-r).descFactorial a : ℝ) /
      ((n : ℝ)^a*(1-1/(n : ℝ))^b)-1| =
      |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b| /
        (1-1/(n : ℝ))^b := by
    calc
      _ = |(((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b) /
          (1-1/(n : ℝ))^b| := by
        rw [sub_div,div_self (ne_of_gt hp0),div_div]
      _ = _ := by rw [abs_div,abs_of_pos hp0]
  rw [he,div_eq_mul_inv]
  have he2 : |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-(1-1/(n : ℝ))^b| ≤
      ((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ) := by
    calc
      _ ≤ |((n-r).descFactorial a : ℝ)/(n : ℝ)^a-1| +
          |(1-1/(n : ℝ))^b-1| := by
        simpa only [abs_sub_comm (1 : ℝ)] using
          (abs_sub_le (((n-r).descFactorial a : ℝ)/(n : ℝ)^a) 1 ((1-1/(n : ℝ))^b))
      _ ≤ (a : ℝ)*(r+a : ℕ)/(n : ℝ)+(b : ℝ)/(n : ℝ) := add_le_add hf ht
      _ = _ := by ring
  calc
    _ ≤ (((a : ℝ)*(r+a : ℕ)+(b : ℝ))/(n : ℝ)) * (2 : ℝ)^b :=
      mul_le_mul he2 (by simpa only [one_div] using hi) (inv_nonneg.mpr hp0.le)
        (by positivity)
    _ = _ := by ring

end SharpTerminalLeave

end

end OAI
