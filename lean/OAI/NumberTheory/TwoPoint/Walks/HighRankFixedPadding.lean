import OAI.NumberTheory.TwoPoint.Walks.TupleRankFiberSum
import OAI.NumberTheory.TwoPoint.Bounds.CrudeColumnPatterns

namespace OAI

/-! The full numerical column sum for fixed signs, padding and perfect positions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma outside_column_mass_bound {J R : ℕ} (P : Fin J → Finset ℕ)
    (template : ColumnPrimeAssignment J R P) (j : Fin J) (U s : ℝ)
    (hU : 1 ≤ U) (hs : 0 ≤ s) (hmass : ∀ l, primeHarmonicMass (P l) ≤ U) :
    (U ^ R * s) * (∏ l : {l : Fin J // l ≠ j},
      primeHarmonicMass (P l.val) ^ (univ.image (template l.val)).card) ≤
        U ^ (R * J) * s := by
  have hp : (∏ l : {l : Fin J // l ≠ j},
      primeHarmonicMass (P l.val) ^ (univ.image (template l.val)).card) ≤
      ∏ _l : {l : Fin J // l ≠ j}, U ^ R := by
    apply prod_le_prod₀
    · intro l _
      exact pow_nonneg (by unfold primeHarmonicMass; positivity) _
    · intro l _
      exact (pow_le_pow_left₀ (by unfold primeHarmonicMass; positivity) (hmass l.val) _).trans
        (pow_le_pow_right₀ hU (by
          simpa using (card_image_le (s := (univ : Finset (Fin R))) (f := template l.val))))
  calc
    _ ≤ (U ^ R * s) * ∏ _l : {l : Fin J // l ≠ j}, U ^ R :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (pow_nonneg (by linarith) _) hs)
    _ = (∏ _l : Fin J, U ^ R) * s := by
      rw [← prod_subtype (univ.erase j) (by simp) (fun _ => U ^ R)]
      rw [← mul_prod_erase univ (fun _ : Fin J => U ^ R) (mem_univ j)]
      ring
    _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin, ← pow_mul]

/-- Every column pattern is encoded internally. No rank probability,
numerical assignment count, or pattern-cover hypothesis is assumed. -/
theorem high_rank_fixed_padding_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P))
    (hR : 0 < R) (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (h Q D B H r : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hmass : ∀ l, primeHarmonicMass (P l) ≤ U) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ w ∈ F, ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hrank : ∀ w ∈ F,
      ¬ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r)
    (base : ColumnPrimeAssignment J R P → ℤ)
    (hlit : ∀ w ∈ F, ∀ i ∈ perfect, ((w j i).val : ℤ) ∣ base w +
      wordDisplacement h ((columnTupleWord w forward padding).take i.val)) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤
      (Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J) *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r) := by
  let fiber (c : CrudeColumnPatternCode J R) := F.filter (fun w =>
    ∀ l i k, decodeCrudeColumnPattern c l i k = decide (w l i = w l k))
  let saving := Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
    (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)
  have hsum : (∑ w ∈ F, columnReciprocalWeight w) ≤
      ∑ c, ∑ w ∈ fiber c, columnReciprocalWeight w := by
    calc
      _ ≤ ∑ w ∈ F, ∑ c : CrudeColumnPatternCode J R,
          if ∀ l i k, decodeCrudeColumnPattern c l i k = decide (w l i = w l k)
            then columnReciprocalWeight w else 0 := by
        apply sum_le_sum
        intro w hw
        obtain ⟨c, hc⟩ := crude_column_pattern_cover w
        have hs := single_le_sum (s := (univ : Finset (CrudeColumnPatternCode J R)))
          (f := fun d => if ∀ l i k, decodeCrudeColumnPattern d l i k = decide (w l i = w l k)
            then columnReciprocalWeight w else 0)
          (fun d _ => ite_nonneg (columnReciprocalWeight_nonneg _) le_rfl) (mem_univ c)
        simpa only [ite_eq_left hc] using hs
      _ = _ := by rw [sum_comm]; simp only [fiber, sum_filter]
  have hfiber (c : CrudeColumnPatternCode J R) :
      (∑ w ∈ fiber c, columnReciprocalWeight w) ≤ U ^ (R * J) * saving := by
    by_cases he : (fiber c).Nonempty
    · obtain ⟨v, hv⟩ := he
      have hp : ∀ w ∈ fiber c, ∀ l i k, w l i = w l k ↔ v l i = v l k := by
        intro w hw l i k
        exact decide_eq_decide.mp (((mem_filter.mp hw).2 l i k).symm.trans
          ((mem_filter.mp hv).2 l i k))
      have hb := same_column_patterns_high_rank_sum P (fiber c) v hp hR forward padding j
        h Q D B H r U hU hP hV (hmass j) hH hlo hbound hq
        (fun w hw => hd w (mem_filter.mp hw).1) perfect cut
        (fun w hw => hrank w (mem_filter.mp hw).1) base
        (fun w hw => hlit w (mem_filter.mp hw).1)
      exact hb.trans (outside_column_mass_bound P v j U saving hU (Real.sqrt_nonneg _) hmass)
    · simp only [not_nonempty_iff_eq_empty.mp he, sum_empty]
      exact mul_nonneg (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  apply hsum.trans
  calc
    _ ≤ ∑ _c : CrudeColumnPatternCode J R, U ^ (R * J) * saving :=
      sum_le_sum (fun c _ => hfiber c)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring

end TwoPointCorrelations

end OAI
