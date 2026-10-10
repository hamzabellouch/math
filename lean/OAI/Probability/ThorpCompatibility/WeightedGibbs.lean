import Mathlib
import OAI.Probability.ThorpCompatibility.Model
import OAI.Probability.ThorpCompatibility.FiniteLaw
import OAI.Probability.ThorpCompatibility.Entropy

namespace OAI

open scoped Classical
namespace ThorpCompatibility

end ThorpCompatibility

namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma exists_mass_pos (P : Law α) : ∃ x, 0 < P.mass x := by
  by_contra h
  push Not at h
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => h x)
  simp only [P.total, Finset.sum_const_zero] at hh
  linarith

lemma uniformMean_rpow_pos [Nonempty α] (P : Law α) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) (p : ℝ) :
    0 < uniformMean (fun x => (w x)^p) := by
  obtain ⟨x,hx⟩ := P.exists_mass_pos
  have hwx : 0 < w x := lt_of_le_of_ne (hw x) (by
    intro he
    exact hx.ne' (hs x he.symm))
  unfold uniformMean
  apply div_pos
  · exact lt_of_lt_of_le (Real.rpow_pos_of_pos hwx p)
      (Finset.single_le_sum (fun y _ => Real.rpow_nonneg (hw y) p) (Finset.mem_univ x))
  · exact_mod_cast Fintype.card_pos

lemma weighted_gibbs_le [Nonempty α] (P : Law α) {θ : ℝ} (hθ : 0 < θ)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) :
    P.mean (fun x => Real.log (w x)) - θ*P.uniformDeficit ≤
      Real.log (marginalFactor θ w) := by
  have hZ : 0 < ∑ x, (w x)^(1/θ) := by
    have h := P.uniformMean_rpow_pos w hw hs (1/θ)
    exact (div_pos_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)).mp h
  have h := P.gibbs_le (fun x => (w x)^(1/θ))
    (fun x => Real.rpow_nonneg (hw x) _) hZ (by
      intro x hz
      by_cases hx : w x = 0
      · exact hs x hx
      · exact False.elim ((Real.rpow_pos_of_pos (lt_of_le_of_ne (hw x) (Ne.symm hx)) _).ne' hz))
  have he : P.mean (fun x => Real.log ((w x)^(1/θ))) =
      (1/θ)*P.mean (fun x => Real.log (w x)) := by
    rw [← P.mean_const_mul]
    apply P.mean_congr_support
    intro x hx
    apply Real.log_rpow
    exact lt_of_le_of_ne (hw x) (by intro he; exact hx.ne' (hs x he.symm))
  rw [he] at h
  have hmean := P.uniformMean_rpow_pos w hw hs (1/θ)
  simp only [marginalFactor, Real.rpow_eq_pow]
  rw [Real.log_rpow hmean, uniformMean,
    Real.log_div hZ.ne' (by exact_mod_cast Fintype.card_ne_zero)]
  have hh := mul_le_mul_of_nonneg_left h hθ.le
  have ht : θ*(1/θ) = 1 := by field_simp
  rw [mul_sub, ← mul_assoc, ht, one_mul] at hh
  unfold uniformDeficit
  nlinarith

lemma tilt_log_partition [Nonempty α] (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) :
    (Law.tilt a ha hZ).mean (fun x => Real.log (a x)) -
      (Law.tilt a ha hZ).uniformDeficit = Real.log (uniformMean a) := by
  let P := Law.tilt a ha hZ
  have he : P.mean (fun x => Real.log (P.mass x)) =
      P.mean (fun x => Real.log (a x)) - Real.log (∑ x, a x) := by
    rw [← P.mean_const (Real.log (∑ x, a x)), ← P.mean_sub]
    apply P.mean_congr_support
    intro x hx
    have hax : a x ≠ 0 := by intro hz; simp [P, Law.tilt, hz] at hx
    exact Real.log_div hax hZ.ne'
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change P.mean _ - P.uniformDeficit = _
  change P.mean _ - (Real.log (Fintype.card α) + P.mean (fun x => Real.log (P.mass x))) = _
  rw [he]
  unfold uniformMean
  rw [Real.log_div hZ.ne' hc]
  ring

end Law
end ThorpCompatibility

end OAI
