import Mathlib
import OAI.Probability.ThorpCompatibility.LogEstimates
import OAI.Probability.ThorpCompatibility.EntropyBounds
import OAI.Probability.ThorpCompatibility.RankAverages

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma random_order_exclusion {β : Type*} [Fintype β] {D : ℕ} (hD : 2 ≤ D)
    (B : Law β) (f : β → Fin D) (k : Fin D)
    (hα : 0 < B.prob (fun b => f b = k)) :
    1 - (1 + Real.log (D : ℝ)) / (D : ℝ) -
        B.prob (fun b => f b = k) * (1 + Real.log (D : ℝ)) ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean
        (fun e => -Real.log (B.prob (fun b => e k ≤ e (f b)))) := by
  let α := B.prob (fun b => f b = k)
  let F : Equiv.Perm (Fin D) → ℝ := fun e => B.prob (fun b => e k ≤ e (f b))
  have hF (e : Equiv.Perm (Fin D)) : α ≤ F e :=
    B.prob_mono (fun b hb => by simp [hb])
  have hD0 : (0 : ℝ) < D := by exact_mod_cast k.pos
  have hstep (t : Fin D) :
      -Real.log (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) -
        α / ((((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ))) ≤
          (rankLaw k t).mean (fun e => -Real.log (F e)) := by
    have hb : 0 < (((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) :=
      div_pos (by exact_mod_cast Nat.sub_pos_of_lt t.isLt) hD0
    have hm : α ≤ (rankLaw k t).mean F := by
      calc
        α = (rankLaw k t).mean (fun _ => α) := (Law.mean_const _ _).symm
        _ ≤ _ := Law.mean_mono _ hF
    have hpos : 0 < (rankLaw k t).mean F := lt_of_lt_of_le hα hm
    calc
      _ ≤ -Real.log ((((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) + α) :=
        neg_log_add_lower hb hα.le
      _ ≤ -Real.log ((rankLaw k t).mean F) := neg_le_neg
        (Real.log_le_log hpos (rankLaw_allowed_mean_le hD B f k t))
      _ ≤ _ := Law.neg_log_mean_le _ F (fun e _ => lt_of_lt_of_le hα (hF e)) hpos
  rw [← rankLaw_mean_average k]
  have hsim := div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hstep t)) hD0.le
  rw [Finset.sum_sub_distrib, sub_div,
    average_inverse_rank k.pos] at hsim
  have hbase := average_log_rank_lower k.pos
  have hharm := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) hα.le
  dsimp [α, F] at *
  linarith

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI
