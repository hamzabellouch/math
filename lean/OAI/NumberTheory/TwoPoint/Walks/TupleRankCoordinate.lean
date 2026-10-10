import OAI.NumberTheory.TwoPoint.Walks.TupleRankWitness
import OAI.NumberTheory.TwoPoint.Bounds.CoordinateFiberSum

namespace OAI

/-! Apply the selected rank estimate to one literal outside-coordinate fiber. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem tuple_rank_coordinate_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P)) (w : ColumnPrimeAssignment J R P)
    (j : Fin J)
    (hpattern : ∀ v ∈ F, ∀ a b, v j a = v j b ↔ w j a = w j b)
    (hR : 0 < R) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (h Q D B H r : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hVU : primeHarmonicMass (P j) ≤ U) (hH : 0 < H)
    (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ i, padding i ≤ Q)
    (hd : ∀ i, (∏ l ∈ univ.erase j, (w l i).val) ≤ D)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hrank : ¬ColumnLowRank (tupleColumnPattern w hR forward padding j) hR h perfect cut r)
    (base : ColumnPrimeAssignment J R P → ℤ)
    (hlit : ∀ v ∈ F, ∀ i ∈ perfect, ((v j i).val : ℤ) ∣ base v +
      wordDisplacement h ((columnTupleWord v forward padding).take i.val)) :
    (∑ v ∈ (F.filter (fun v => outsideCoordinate j v = outsideCoordinate j w)).image
        (fun v => v j), ∏ p ∈ univ.image v, (p.val : ℝ)⁻¹) ≤
      U ^ R * Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
        (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r) := by
  let G := (F.filter (fun z => outsideCoordinate j z = outsideCoordinate j w)).image (fun z => z j)
  have hupdate (v : Fin R → P j) (hv : v ∈ G) : Function.update w j v ∈ F := by
    obtain ⟨z, hz, hzv⟩ := mem_image.mp hv
    have he := update_eq_of_outside_eq j w z (mem_filter.mp hz).2.symm
    rw [hzv] at he
    rw [he]
    exact (mem_filter.mp hz).1
  have hp : ∀ v ∈ G, ∀ a b, v a = v b ↔ w j a = w j b := by
    intro v hv a b
    have ht := hpattern (Function.update w j v) (hupdate v hv) a b
    simpa only [Function.update_self] using ht
  have htest : ∀ y, patternResample (w j) y ∈ G → ∀ i ∈ perfect,
      ((y (patternCoordinate (w j) i)).val : ℤ) ∣
        base (Function.update w j (patternResample (w j) y)) +
          wordDisplacement h
            ((columnTupleWord (Function.update w j (patternResample (w j) y)) forward padding).take i.val) := by
    intro y hy i hi
    have hl := hlit _ (hupdate _ hy) i hi
    simpa only [Function.update_self, patternResample] using hl
  have hb := tuple_not_low_rank_reciprocal_sum w hR forward padding j G hp
    h Q D B H hP hV hH hlo hbound hq hd perfect cut r hrank
    (fun y => base (Function.update w j (patternResample (w j) y))) htest
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (pow_le_pow_left₀ hV.le hVU _).trans
    (pow_le_pow_right₀ hU (by
      simpa using (card_image_le (s := (univ : Finset (Fin R))) (f := w j))))

end TwoPointCorrelations

end OAI
