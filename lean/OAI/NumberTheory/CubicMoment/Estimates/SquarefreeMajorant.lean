import OAI.NumberTheory.CubicMoment.Estimates.DispersionPoisson
import OAI.NumberTheory.CubicGram.LatticeCounts

namespace OAI

/-!
# The squarefree majorant in corrected dispersion

Only the positive variance term is majorized. The mixed and model terms
retain their actual Möbius-square weights.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def truncatedSquareDivisorSum (C : Finset Eisenstein) (a : Eisenstein) : ℝ :=
  ∑ c ∈ C, if c^2 ∣ a then (idealMoebius c : ℝ) else 0

lemma truncatedSquareDivisorSum_eq_one (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C) {a : Eisenstein} (ha : Squarefree a) :
    truncatedSquareDivisorSum C a = 1 := by
  unfold truncatedSquareDivisorSum
  calc
    _ = if (1 : Eisenstein)^2 ∣ a then (idealMoebius 1 : ℝ) else 0 := by
      apply Finset.sum_eq_single 1
      · intro c hc hc1
        have hd : ¬c^2 ∣ a := by
          intro hd
          exact hc1 (primary_unit_eq_one (ha c (by simpa only [pow_two] using hd)) (hC c hc))
        simp [hd]
      · exact fun hn => (hn h1).elim
    _ = 1 := by simp [idealMoebius]

/-- This majorizes the true squarefree indicator and is exactly one on
squarefree elements. It applies to every truncation containing one. -/
theorem squarefree_le_truncated_majorant (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C) (a : Eisenstein) :
    (idealMoebius a : ℝ)^2 ≤ (truncatedSquareDivisorSum C a)^2 := by
  rw [idealMoebius_sq]
  by_cases ha : Squarefree a
  · rw [ite_eq_left ha,truncatedSquareDivisorSum_eq_one C hC h1 ha]
    norm_num
  · rw [ite_eq_right ha]
    exact sq_nonneg _

/-- Expansion before collecting pairs by their least common multiple. -/
theorem truncatedSquareDivisorSum_sq (C : Finset Eisenstein) (a : Eisenstein) :
    (truncatedSquareDivisorSum C a)^2 =
      ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c : ℝ)*(idealMoebius d : ℝ)*
        (if c^2 ∣ a ∧ d^2 ∣ a then (1 : ℝ) else 0) := by
  rw [truncatedSquareDivisorSum,pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc' : c^2 ∣ a <;> by_cases hd' : d^2 ∣ a <;> simp [hc',hd']

/-- The concrete norm truncation used by corrected dispersion. -/
def squareDivisorTruncation (D : ℝ) : Finset Eisenstein :=
  (nonzeroNormBall D).filter primary

lemma squareDivisorTruncation_primary (D : ℝ) {c : Eisenstein}
    (hc : c ∈ squareDivisorTruncation D) : primary c := (Finset.mem_filter.mp hc).2

lemma one_mem_squareDivisorTruncation {D : ℝ} (hD : 1 ≤ D) :
    (1 : Eisenstein) ∈ squareDivisorTruncation D := by
  simp only [squareDivisorTruncation,Finset.mem_filter,mem_nonzeroNormBall,norm_one_eq]
  exact ⟨⟨hD,one_ne_zero⟩,primary_one⟩

/-- The positive term alone is enlarged in the corrected square. The two
remaining terms keep their original squarefree weights. -/
theorem corrected_squarefree_majorant (A C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c) (h1 : 1 ∈ C)
    (W : Eisenstein → ℝ) (hW : ∀ a ∈ A, 0 ≤ W a)
    (F M : Eisenstein → ℂ) :
    (∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖F a-M a‖^2) ≤
      (∑ a ∈ A, (truncatedSquareDivisorSum C a)^2*W a*‖F a‖^2) -
        2*(∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*(star (F a)*M a).re) +
        ∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖M a‖^2 := by
  have he (x y : ℂ) : ‖x-y‖^2 = ‖x‖^2-2*(star x*y).re+‖y‖^2 := by
    simpa only [RCLike.inner_apply,starRingEnd_apply,mul_comm,RCLike.re_eq_complex_re,RCLike.re_eq_complex_re] using
      norm_sub_sq (𝕜 := ℂ) x y
  have hp : (∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖F a‖^2) ≤
      ∑ a ∈ A, (truncatedSquareDivisorSum C a)^2*W a*‖F a‖^2 := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (squarefree_le_truncated_majorant C hC h1 a) (hW a ha))
      (sq_nonneg _)
  have hx : (∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖F a-M a‖^2) =
      (∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖F a‖^2) -
        2*(∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*(star (F a)*M a).re) +
        ∑ a ∈ A, (idealMoebius a : ℝ)^2*W a*‖M a‖^2 := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [he]
    ring
  rw [hx]
  linarith

end CubicFirstMoment

end

end OAI
