import Mathlib

namespace OAI
open scoped BigOperators
open Complex ComplexConjugate

namespace Problem337

lemma re_finset_sum {α : Type*} (s : Finset α) (f : α → ℂ) :
    (∑ a ∈ s, f a).re = ∑ a ∈ s, (f a).re :=
  map_sum Complex.reAddGroupHom f s

/-- Expand a finite complex second moment into pairwise correlations. -/
theorem finite_complex_second_moment_identity {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) :
    (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) =
      ∑ t ∈ T, ∑ s ∈ T, (∑ u ∈ U, z u t * conj (z u s)).re := by
  have hpoint (u : α) : ‖∑ t ∈ T, z u t‖ ^ 2 =
      ∑ t ∈ T, ∑ s ∈ T, (z u t * conj (z u s)).re := by
    calc
      ‖∑ t ∈ T, z u t‖ ^ 2 =
          ((∑ t ∈ T, z u t) * conj (∑ t ∈ T, z u t)).re := by
            rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      _ = _ := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum, re_finset_sum]
        rw [Finset.sum_comm]
  simp_rw [hpoint, re_finset_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]

/-- Unit phases have a second moment bounded by their diagonal contribution
plus a uniform bound for all off-diagonal correlations. -/
theorem finite_complex_second_moment_bound {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) (E : ℝ)
    (hunit : ∀ u ∈ U, ∀ t ∈ T, ‖z u t‖ = 1)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * conj (z u s)‖ ≤ E) :
    (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) ≤
      (U.card : ℝ) * T.card + (T.card : ℝ) * (T.card - 1 : ℝ) * E := by
  classical
  rw [finite_complex_second_moment_identity]
  have hentry (t : β) (ht : t ∈ T) (s : β) (hs : s ∈ T) :
      (∑ u ∈ U, z u t * conj (z u s)).re ≤
        E + if t = s then (U.card : ℝ) - E else 0 := by
    by_cases hts : t = s
    · subst s
      have hd : (∑ u ∈ U, z u t * conj (z u t)).re = U.card := by
        simp only [re_finset_sum, Complex.mul_conj, Complex.ofReal_re]
        calc
          (∑ u ∈ U, Complex.normSq (z u t)) = ∑ _u ∈ U, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Complex.normSq_eq_norm_sq, hunit u hu t ht]
            norm_num
          _ = _ := by simp
      simp [hd]
    · simpa [hts] using (Complex.re_le_norm (∑ u ∈ U, z u t * conj (z u s))).trans
        (hcorr t ht s hs hts)
  calc
    (∑ t ∈ T, ∑ s ∈ T, (∑ u ∈ U, z u t * conj (z u s)).re) ≤
        ∑ t ∈ T, ∑ s ∈ T, (E + if t = s then (U.card : ℝ) - E else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      exact Finset.sum_le_sum (fun s hs => hentry t ht s hs)
    _ = (T.card : ℝ) * ((T.card : ℝ) * E + (U.card : ℝ) - E) := by
      have hrow (t : β) (ht : t ∈ T) :
          (∑ s ∈ T, (E + if t = s then (U.card : ℝ) - E else 0)) =
            (T.card : ℝ) * E + (U.card : ℝ) - E := by
        simp [Finset.sum_add_distrib, ht]
        ring
      simp_rw [Finset.sum_congr rfl hrow]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by ring

/-- A normalized form of the off-diagonal second-moment bound. -/
theorem finite_complex_second_moment_normalized {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) (E : ℝ)
    (hU : U.Nonempty) (hT : T.Nonempty) (hE : 0 ≤ E)
    (hunit : ∀ u ∈ U, ∀ t ∈ T, ‖z u t‖ = 1)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * conj (z u s)‖ ≤ E) :
    (∑ u ∈ U, ‖(∑ t ∈ T, z u t) / (T.card : ℂ)‖ ^ 2) / (U.card : ℝ) ≤
      1 / (T.card : ℝ) + E / (U.card : ℝ) := by
  have hu : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have ht : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hraw := finite_complex_second_moment_bound U T z E hunit hcorr
  have hweak : (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) ≤
      (U.card : ℝ) * T.card + (T.card : ℝ) ^ 2 * E := by
    nlinarith
  simp only [norm_div, Complex.norm_natCast, div_pow]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ hu).mpr
  apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
  have heq : ((1 / (T.card : ℝ) + E / (U.card : ℝ)) * U.card) * (T.card : ℝ)^2 =
      (U.card : ℝ) * T.card + (T.card : ℝ)^2 * E := by
    field_simp
  rw [heq]
  exact hweak

end Problem337

end OAI
