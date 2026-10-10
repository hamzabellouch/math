import OAI.Combinatorics.EditApproximation.Binary.BinaryScaleGrid
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadComposition
import OAI.Combinatorics.EditApproximation.Binary.BinaryCachedShellWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Inline initial-cone evaluation reads the gathered previous-pass seed
words explicitly. Each query seed is loaded once per routine and each
visited center load contributes its measured lookup cost. -/

namespace EditApproximation
namespace BinaryFraction



def initialGridPlainWithWork {n : ℕ} (P : ℕ) (A : BinaryFraction)
    (U : TargetInterval n → ℕ) (radius : ℕ) (q : TargetInterval n) (b : ℕ) :
    List (TargetInterval n) × ℕ :=
  let spacing := seedGridSpacingWithWork b P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi
  let selected := filterWithWork (fun r => initialCenterGuardWithWork b (U r) A) points.1
  (selected.1, spacing.2 + points.2 + selected.2 + 2)

theorem initialGridReadWithWork_eq_cost {n : ℕ} (P : ℕ) (A : BinaryFraction)
    (read : TargetInterval n → List Bool × ℕ) (radius : ℕ) (q : TargetInterval n) (b R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (initialGridReadWithWork P A read radius q b).1 =
      (initialGridPlainWithWork P A (fun r => bitWordValue (read r).1) radius q b).1 ∧
    (initialGridReadWithWork P A read radius q b).2 ≤
      (initialGridPlainWithWork P A (fun r => bitWordValue (read r).1) radius q b).2 * (R + 1) := by
  let spacing := seedGridSpacingWithWork b P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi
  have h := filterWithWork_add_read
    (fun r => initialCenterGuardWithWork b (bitWordValue (read r).1) A)
    (fun r => (read r).2) points.1 R (fun r _ => hR r)
  constructor
  · simpa only [initialGridReadWithWork, initialGridPlainWithWork, spacing, points] using h.1
  · change spacing.2 + points.2 + _ + 2 ≤ (spacing.2 + points.2 + _ + 2) * (R + 1)
    nlinarith only [h.2]



theorem initialCentersReadWithWork_eq_cost {n : ℕ} (N P : ℕ) (A : BinaryFraction)
    (read : TargetInterval n → List Bool × ℕ) (q : TargetInterval n) (R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (initialCentersReadWithWork N P A read q).1 =
      (initialCentersWithWork N P A (fun r => bitWordValue (read r).1) q).1 ∧
    (initialCentersReadWithWork N P A read q).2 ≤
      (initialCentersWithWork N P A (fun r => bitWordValue (read r).1) q).2 * (R + 2) := by
  let Uq := bitWordValue (read q).1
  let scales := dyadicScalesWithWork N
  let active := filterWithWork (fun b => initialScaleGuardWithWork Uq b A) scales.1
  let plain := initialGridPlainWithWork P A (fun r => bitWordValue (read r).1) Uq q
  have h := arithmeticFlatMapWithWork_factor (initialGridReadWithWork P A read Uq q)
    plain active.1 (R + 1) (by omega)
    (fun b _ => (initialGridReadWithWork_eq_cost P A read Uq q b R hR).1)
    (fun b _ => (initialGridReadWithWork_eq_cost P A read Uq q b R hR).2)
  have hq := hR q
  refine ⟨h.1, ?_⟩
  change (read q).2 + scales.2 + active.2 + _ + 3 ≤
    (scales.2 + active.2 + (arithmeticFlatMapWithWork plain active.1).2 + 3) * (R + 2)
  nlinarith only [h.2, hq]



theorem initialConeReadWithWork_eq_cost {n : ℕ} (sourceLength : ℕ)
    (read : TargetInterval n → List Bool × ℕ) (a L : BinaryFraction)
    (query center : TargetInterval n) (R : ℕ) (hR : (read center).2 ≤ R) :
    (initialConeReadWithWork sourceLength read a L query center).1 =
      (initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L query center).1 ∧
    (initialConeReadWithWork sourceLength read a L query center).2 ≤
      (initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L query center).2 + R := by
  constructor
  · rfl
  · have heq : initialConeWithWork sourceLength (fun _ => bitWordValue (read center).1) a L query center =
        initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L query center := rfl
    change (read center).2 + _ ≤ _ + R
    rw [heq]
    omega



theorem initialMinimumReadWithWork_eq_cost {n : ℕ} (sourceLength : ℕ)
    (read : TargetInterval n → List Bool × ℕ) (N F : ℕ) (a : BinaryFraction)
    (query : TargetInterval n) (centers : List (TargetInterval n)) (R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (initialMinimumReadWithWork sourceLength read N F a query centers).1 =
      (initialMinimumWithWork sourceLength (fun r => bitWordValue (read r).1) N F a query centers).1 ∧
    (initialMinimumReadWithWork sourceLength read N F a query centers).2 ≤
      (initialMinimumWithWork sourceLength (fun r => bitWordValue (read r).1) N F a query centers).2 *
        (R + 2) := by
  let L := canonicalMulWithWork (nat 32) (nat F)
  have hmap := arithmeticMapWithWork_extra
    (initialConeReadWithWork sourceLength read a L.1 query)
    (initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L.1 query)
    (fun _ => R) centers
    (fun r _ => (initialConeReadWithWork_eq_cost sourceLength read a L.1 query r R (hR r)).1)
    (fun r _ => (initialConeReadWithWork_eq_cost sourceLength read a L.1 query r R (hR r)).2)
  have hs : (centers.map (fun _ => R)).sum = centers.length * R := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at hmap
  have hlen := arithmeticMapWithWork_length_le_cost
    (initialConeWithWork sourceLength (fun r => bitWordValue (read r).1) a L.1 query) centers
  have hquery := hR query
  unfold initialMinimumReadWithWork initialMinimumWithWork
  dsimp only
  split_ifs
  · constructor
    · rfl
    · nlinarith only [hquery]
  · constructor
    · simp only [L, hmap.1]
    · dsimp only
      rw [show (canonicalMulWithWork (nat 32) (nat F)) = L from rfl, hmap.1]
      have hprod := Nat.mul_le_mul_right R hlen
      nlinarith only [hmap.2, hquery, hprod]



theorem initialProgramReadWithWork_eq_cost {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (read : TargetInterval n → List Bool × ℕ) (query : TargetInterval n) (R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (initialProgramReadWithWork sourceLength N P F A a read query).1 =
      (initialProgramWithWork sourceLength N P F A a (fun r => bitWordValue (read r).1) query).1 ∧
    (initialProgramReadWithWork sourceLength N P F A a read query).2 ≤
      (initialProgramWithWork sourceLength N P F A a (fun r => bitWordValue (read r).1) query).2 *
        (R + 2) := by
  have hc := initialCentersReadWithWork_eq_cost N P A read query R hR
  have hm := initialMinimumReadWithWork_eq_cost sourceLength read N F a query
    (initialCentersWithWork N P A (fun r => bitWordValue (read r).1) query).1 R hR
  unfold initialProgramReadWithWork initialProgramWithWork
  dsimp only
  rw [hc.1]
  constructor
  · exact hm.1
  · nlinarith only [hc.2, hm.2]

theorem finishCachedWithWork_read_factor (read plain : BinaryFraction × ℕ)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining K : ℕ)
    (hK : 1 ≤ K) (hvalue : read.1 = plain.1) (hcost : read.2 ≤ plain.2 * K) :
    (finishCachedWithWork read base hbase remaining).1 =
      (finishCachedWithWork plain base hbase remaining).1 ∧
    (finishCachedWithWork read base hbase remaining).2 ≤
      (finishCachedWithWork plain base hbase remaining).2 * K := by
  unfold finishCachedWithWork
  dsimp only
  rw [hvalue]
  refine ⟨rfl, ?_⟩
  nlinarith only [hK, hcost]



theorem cachedInitialProgramReadWithWork_eq_cost {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (read : TargetInterval n → List Bool × ℕ) (query : TargetInterval n) (R : ℕ)
    (hR : ∀ r, (read r).2 ≤ R) :
    (cachedInitialProgramReadWithWork sourceLength N P F A a read query).1 =
      (cachedInitialProgramWithWork sourceLength N P F A a (fun r => bitWordValue (read r).1) query).1 ∧
    (cachedInitialProgramReadWithWork sourceLength N P F A a read query).2 ≤
      (cachedInitialProgramWithWork sourceLength N P F A a (fun r => bitWordValue (read r).1) query).2 *
        (R + 2) := by
  have h := initialProgramReadWithWork_eq_cost sourceLength N P F A a read query R hR
  exact finishCachedWithWork_read_factor _ _ [true] (by decide) 0 (R + 2) (by omega) h.1 h.2

end BinaryFraction
end EditApproximation

end OAI
