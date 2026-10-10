import Mathlib
import OAI.Probability.ThorpCompatibility.HeavyColumns

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

noncomputable def jointRowDeficit {A D : ℕ} (Q : Law (Grid A D)) : ℝ :=
  (Q.map Prod.fst).uniformDeficit

noncomputable def rowDeficit {A D : ℕ} (Q : Law (Grid A D)) : ℝ :=
  ∑ i : Fin A, (Q.map (fun a => a.1 i)).uniformDeficit

noncomputable def colDeficit {A D : ℕ} (Q : Law (Grid A D)) : ℝ :=
  ∑ k : Fin D, (Q.map (fun a => a.2 k)).uniformDeficit

noncomputable def heavyTotal {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ) : ℝ :=
  ∑ k : Fin D, ∑ i : Fin A, Q.mean (entryHeavyMass Q H k i)

lemma rowDeficit_nonneg {A D : ℕ} (Q : Law (Grid A D)) : 0 ≤ rowDeficit Q :=
  Finset.sum_nonneg fun _ _ => Law.uniformDeficit_nonneg _

lemma colDeficit_nonneg {A D : ℕ} (Q : Law (Grid A D)) : 0 ≤ colDeficit Q :=
  Finset.sum_nonneg fun _ _ => Law.uniformDeficit_nonneg _

lemma heavyTotal_nonneg {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ) :
    0 ≤ heavyTotal Q H := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro i _
  exact Q.mean_nonneg (fun a => entryHeavyMass_nonneg Q H k i a)

lemma rowDeficit_le_joint {A D : ℕ} (Q : Law (Grid A D)) :
    rowDeficit Q ≤ jointRowDeficit Q := by
  have h := Q.entropy_tuple_le (fun i : Fin A => fun a => a.1 i)
  change (Q.map Prod.fst).entropy ≤ _ at h
  unfold rowDeficit jointRowDeficit
  simp only [Law.uniformDeficit_eq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : Real.log (Fintype.card (Rows A D) : ℝ) =
      A * Real.log (Fintype.card (Equiv.Perm (Fin D)) : ℝ) := by
    change Real.log (Fintype.card (Fin A → Equiv.Perm (Fin D)) : ℝ) = _
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  rw [hc]
  linarith

lemma clump_deficit_bound {A D : ℕ} (Q : Law (Grid A D)) (m : ℝ)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2) :
    Real.log m * Q.mean (fun a => (clumpCount (m^(1/100:ℝ)) a.1 : ℝ)) ≤
      400 * jointRowDeficit Q + 400 := by
  let f : Rows A D → ℝ := fun r => (1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r
  have h := (Q.map Prod.fst).entropy_moment_bound f
  have hpos : 0 < uniformMean (fun r => Real.exp (f r)) := by
    unfold uniformMean
    apply div_pos
    · exact Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
    · exact_mod_cast Fintype.card_pos
  have hlog : Real.log (uniformMean (fun r => Real.exp (f r))) ≤ 1 := by
    have h₂ := Real.log_le_log hpos hmgf
    have h₃ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  change _ ≤ jointRowDeficit Q + Real.log (uniformMean (fun r => Real.exp (f r))) at h
  rw [Law.mean_map] at h
  change Q.mean (fun a => (1/400 * Real.log m) * (clumpCount (m^(1/100:ℝ)) a.1 : ℝ)) ≤ _ at h
  rw [Law.mean_const_mul] at h
  nlinarith

lemma heavyTotal_log_bound {A D : ℕ} (Q : Law (Grid A D)) {m : ℝ}
    (hm : 0 < m) (hl : 200 ≤ Real.log m) :
    Real.log m * heavyTotal Q (m^(1/100:ℝ)) ≤ 200 * colDeficit Q := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin D))) =>
    column_heavy_bound Q k (Real.rpow_pos_of_pos hm (1/100:ℝ)))
  rw [← Finset.mul_sum] at h
  change (Real.log (m^(1/100:ℝ)) - 1) * heavyTotal Q (m^(1/100:ℝ)) ≤ colDeficit Q at h
  rw [Real.log_rpow hm] at h
  have hM := heavyTotal_nonneg Q (m^(1/100:ℝ))
  nlinarith

lemma absorb_entropy_losses {ell R r C M T J n E : ℝ}
    (hl : 1000 ≤ ell) (hr : 0 ≤ r) (hR : r ≤ R) (hC : 0 ≤ C)
    (hM : ell * M ≤ 200 * C) (hT : ell * T ≤ 400 * R + 400)
    (hJ : R + C + n - E - 3*M - T ≤ J) :
    n - E - 1 + (1 - 1000/ell) * (r+C) ≤ J := by
  have hl0 : 0 < ell := by linarith
  have hrR : 0 ≤ R := le_trans hr hR
  have hloss : 3*M + T - 1 ≤ 1000*(R+C)/ell := by
    apply (le_div_iff₀ hl0).mpr
    nlinarith
  have ht : 0 ≤ 1 - 1000/ell := sub_nonneg.mpr ((div_le_one hl0).mpr hl)
  have hmarg := mul_le_mul_of_nonneg_left hR ht
  have heq : 1000*(R+C)/ell = (1000/ell)*(R+C) := by ring
  rw [heq] at hloss
  nlinarith

end ThorpCompatibility

end OAI
