import OAI.Analysis.Cotype.ProjectionDerivatives
import OAI.Analysis.Cotype.CoefficientArithmetic

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial
namespace Cotype

variable {m : ℕ}

def lowPartialS (f : SignMatrix m → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
    (retainedCoefficient f d k l * (chebLow d ((X : ℝ[X])^k)).derivative.eval 0) • X^l

def highPartialS (f : SignMatrix m → ℝ) (d : ℕ) : ℝ[X] :=
  partialS f d - lowPartialS f d

theorem lowPartialS_eval (f : SignMatrix m → ℝ) (d : ℕ) (u : ℝ) :
    (lowPartialS f d).eval u = (splitLowS f d u).derivative.eval 0 := by
  simp only [lowPartialS, splitLowS, retainedSectionS, map_sum, map_smul,
    eval_finsetSum, eval_smul, smul_eq_mul,
    eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem highPartialS_sum (f : SignMatrix m → ℝ) (d : ℕ) :
    highPartialS f d = ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1),
      (retainedCoefficient f d k l *
        (((X : ℝ[X])^k - chebLow d (X^k)).derivative.eval 0)) • X^l := by
  simp only [highPartialS, partialS, lowPartialS, ← Finset.sum_sub_distrib,
    derivative_sub, eval_sub]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [← sub_smul, ← mul_sub]

theorem highPartialS_degree (f : SignMatrix m → ℝ) (d : ℕ) :
    (highPartialS f d).degree ≤ d := by
  rw [highPartialS_sum]
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro k _
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro l _
  by_cases hk : k ≤ d
  · have he : chebLow d ((X : ℝ[X])^k) = X^k := chebLow_eq_self (by simpa using hk)
    simp [he]
  · by_cases hl : l ≤ d
    · apply (degree_smul_le _ _).trans
      simpa using hl
    · simp [retainedCoefficient, hk, hl]

theorem highPartialU_eval (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) :
    (partialU f d - chebLow d (partialU f d)).eval s =
      (splitHighU f d s).derivative.eval 0 := by
  simp only [partialU, splitHighU, map_sum, map_smul, ← Finset.sum_sub_distrib,
    eval_finsetSum, eval_sub, eval_smul, smul_eq_mul,
    eval_pow, eval_X]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem mixed_split (f : SignMatrix m → ℝ) (d : ℕ) :
    (partialS f d).derivative.eval 0 =
      (chebLow d (partialU f d)).derivative.eval 0 + (highPartialS f d).derivative.eval 0 := by
  have he : (lowPartialS f d).derivative.eval 0 = (chebLow d (partialU f d)).derivative.eval 0 := by
    simp only [lowPartialS, partialU, map_sum, map_smul,
      eval_finsetSum, eval_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [highPartialS, derivative_sub, eval_sub]
  linarith

theorem admissible_partialS_bound {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (ha : 0 ≤ a) {d : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) {u : ℝ} (hu : |u| ≤ 1) :
    |(partialS Ψ d).eval u| ≤ (m : ℝ)*a*4 := by
  rw [admissible_partialS h hd hm]
  obtain ⟨_, _, _, _, _, hgM, _, _, _, _⟩ := h
  have hmean : |u/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ha)]
  exact mul_le_mul_of_nonneg_left (biasedExpectation_bound (fun _ => hmean) hgM)
    (mul_nonneg (Nat.cast_nonneg _) ha)

theorem admissible_partialU_bound {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (hb : 0 ≤ b) {d : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) {s : ℝ} (hs : |s| ≤ 1) :
    |(partialU Ψ d).eval s| ≤ (m : ℝ)*b*4 := by
  rw [admissible_partialU h hd hm]
  obtain ⟨_, _, _, _, hfM, _, _, _, _, _⟩ := h
  have hmean : |s/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hb)]
  exact mul_le_mul_of_nonneg_left (biasedExpectation_bound (fun _ => hmean) hfM)
    (mul_nonneg (Nat.cast_nonneg _) hb)

theorem admissible_mixed_upper {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (hr : RankOneSupported Ψ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m) :
    |(partialS Ψ (degreeCutoff m)).derivative.eval 0| ≤
      4 * (degreeCutoff m : ℝ) * (degreeCutoff m+1) *
        ((m : ℝ)*a + (m : ℝ)*b + 10*(degreeCutoff m : ℝ)*(degreeCutoff m+1)^2) := by
  let d := degreeCutoff m
  have hd1 : 1 ≤ d := by dsimp [d]; omega
  have hm1 : 1 ≤ m := by omega
  have hΨ := h.1
  have hM : ∀ S, |Ψ S| ≤ 4 := h.2.2.2.1
  have hlo (u : ℝ) (hu : |u| ≤ 1) :
      |(lowPartialS Ψ d).eval u| ≤ 16*(d : ℝ)*(d+1)^2 := by
    rw [lowPartialS_eval]
    have hh := polynomial_derivative_zero_bound (splitLowS Ψ d u) d (splitLowS_degree Ψ d u)
      (by positivity : 0 ≤ 16*((d:ℝ)+1)) (fun s hs => by
        simpa only [show (4:ℝ)*4=16 by norm_num] using
          splitLowS_bound hΨ hr (by norm_num) hM hd hm (abs_le.mpr hs) hu)
    convert hh using 1; ring
  have hhi (s : ℝ) (hs : |s| ≤ 1) :
      |(partialU Ψ d - chebLow d (partialU Ψ d)).eval s| ≤ 24*(d : ℝ)*(d+1)^2 := by
    rw [highPartialU_eval]
    have hh := polynomial_derivative_zero_bound (splitHighU Ψ d s) d (splitHighU_degree Ψ d s)
      (by positivity : 0 ≤ 24*((d:ℝ)+1)) (fun u hu => by
        simpa only [show (6:ℝ)*4=24 by norm_num] using
          splitHighU_bound hΨ hr (by norm_num) hM hd hm hs (abs_le.mpr hu))
    convert hh using 1; ring
  have hhs (u : ℝ) (hu : |u| ≤ 1) :
      |(highPartialS Ψ d).eval u| ≤ (m : ℝ)*a*4 + 16*(d : ℝ)*(d+1)^2 := by
    simp only [highPartialS, eval_sub]
    exact (abs_sub _ _).trans (add_le_add (admissible_partialS_bound h ha hd1 hm1 hu) (hlo u hu))
  have hlu (s : ℝ) (hs : |s| ≤ 1) :
      |(chebLow d (partialU Ψ d)).eval s| ≤ (m : ℝ)*b*4 + 24*(d : ℝ)*(d+1)^2 := by
    have hh := hhi s hs
    simp only [eval_sub] at hh
    have hpu := admissible_partialU_bound h hb hd1 hm1 hs
    have he : (chebLow d (partialU Ψ d)).eval s =
        (partialU Ψ d).eval s - ((partialU Ψ d).eval s - (chebLow d (partialU Ψ d)).eval s) := by ring
    rw [he]
    exact (abs_sub _ _).trans (add_le_add hpu hh)
  have hb1 := polynomial_derivative_zero_bound (highPartialS Ψ d) d (highPartialS_degree Ψ d)
    (by positivity : 0 ≤ (m:ℝ)*a*4 + 16*(d:ℝ)*(d+1)^2)
    (fun u hu => hhs u (abs_le.mpr hu))
  have hb2 := polynomial_derivative_zero_bound (chebLow d (partialU Ψ d)) d (chebLow_degree d _)
    (by positivity : 0 ≤ (m:ℝ)*b*4 + 24*(d:ℝ)*(d+1)^2)
    (fun s hs => hlu s (abs_le.mpr hs))
  rw [mixed_split]
  apply (abs_add_le _ _).trans
  have hh := add_le_add hb2 hb1
  convert hh using 1; dsimp [d]; ring

theorem admissible_exists_rank_two {Ψ : SignMatrix m → ℝ} {f g : Cube m → ℝ} {a b : ℝ}
    (h : ScalarAdmissible m a b Ψ f g) (ha : 0 < a) (hb : 0 < b)
    (hd : 4 ≤ degreeCutoff m) (hm : degreeCutoff m < m)
    (hlarge : 80*(degreeCutoff m : ℝ)*(degreeCutoff m+1)^2 ≤ min ((m:ℝ)*a) ((m:ℝ)*b)) :
    ∃ P : SignMatrix m, 2 ≤ (binaryMatrix P).rank ∧ fourier Ψ P ≠ 0 := by
  by_contra hn
  have hr : RankOneSupported Ψ := by
    intro P hP
    have hh : ¬ 2 ≤ (binaryMatrix P).rank := fun hh => hn ⟨P, hh, hP⟩
    omega
  have hu := admissible_mixed_upper h hr ha.le hb.le hd hm
  rw [admissible_mixed_derivative h (by omega) (by omega)] at hu
  rw [abs_of_nonneg (by positivity)] at hu
  exact coefficient_numerical_contradiction (by exact_mod_cast hd)
    (hlarge.trans (min_le_left _ _)) (hlarge.trans (min_le_right _ _)) hu

end Cotype

end

end OAI
