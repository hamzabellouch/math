import OAI.NumberTheory.TwoPoint.Walks.TupleRankCoordinate
import OAI.NumberTheory.TwoPoint.Bounds.CoordinateFiberSum

namespace OAI

/-! Sum the actual high-rank column while retaining reciprocal weights outside it. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem same_column_patterns_high_rank_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P)) (template : ColumnPrimeAssignment J R P)
    (hpattern : ∀ w ∈ F, ∀ j i k, w j i = w j k ↔ template j i = template j k)
    (hR : 0 < R) (forward : Fin R → Bool) (padding : Fin R → ℕ) (j : Fin J)
    (h Q D B H r : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hVU : primeHarmonicMass (P j) ≤ U) (hH : 0 < H)
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
      (U ^ R * Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
        (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)) *
      ∏ l : {l : Fin J // l ≠ j},
        primeHarmonicMass (P l.val) ^ (univ.image (template l.val)).card := by
  let weight (l : Fin J) (v : Fin R → P l) : ℝ :=
    ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹
  let saving := Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
    (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)
  have hw : ∀ l v, 0 ≤ weight l v := by intros; dsimp [weight]; positivity
  have hfiber : ∀ x ∈ F.image (outsideCoordinate j),
      (∑ v ∈ (F.filter (fun w => outsideCoordinate j w = x)).image (fun w => w j),
        weight j v) ≤ U ^ R * saving := by
    intro x hx
    obtain ⟨w, hwF, rfl⟩ := mem_image.mp hx
    exact tuple_rank_coordinate_sum P F w j
      (fun v hv a b => (hpattern v hv j a b).trans (hpattern w hwF j a b).symm)
      hR forward padding h Q D B H r U hU hP hV hVU hH hlo hbound hq
      (hd w hwF) perfect cut (hrank w hwF) base hlit
  have hout := same_family_patterns_reciprocal_sum (fun l : {l : Fin J // l ≠ j} => P l.val)
    (F.image (outsideCoordinate j)) (outsideCoordinate j template) (by
      intro x hx l a b
      obtain ⟨w, hwF, rfl⟩ := mem_image.mp hx
      exact hpattern w hwF l.val a b)
  have hb := coordinate_fiber_sum_bound F j weight hw (U ^ R * saving) hfiber
  change (∑ w ∈ F, columnReciprocalWeight w) ≤
    (U ^ R * saving) * ∑ x ∈ F.image (outsideCoordinate j),
      ∏ l : {l : Fin J // l ≠ j}, ∏ p ∈ univ.image (x l), (p.val : ℝ)⁻¹ at hb
  have hn : 0 ≤ U ^ R * saving :=
    mul_nonneg (pow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left hout hn)

end TwoPointCorrelations

end OAI
