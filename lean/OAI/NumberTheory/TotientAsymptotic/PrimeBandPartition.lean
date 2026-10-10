import OAI.NumberTheory.TotientAsymptotic.PrimeBandProducts

namespace OAI

/-! Exact reconstruction from adjacent prime-factor bands. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma partBetween_split (n : ℕ) {U V W : ℝ} (hUV : U ≤ V) (hVW : V ≤ W) :
    partBetween n U V*partBetween n V W=partBetween n U W := by
  apply Nat.eq_of_mul_eq_mul_left (partBelow_pos n U)
  calc
    partBelow n U*(partBetween n U V*partBetween n V W) =
        (partBelow n U*partBetween n U V)*partBetween n V W := by ring
    _ = partBelow n V*partBetween n V W := by rw [partBelow_band_split n hUV]
    _ = partBelow n W := partBelow_band_split n hVW
    _ = _ := (partBelow_band_split n (hUV.trans hVW)).symm

lemma partBetween_self (n : ℕ) (U : ℝ) : partBetween n U U=1 := by
  have he : n.primeFactorsList.filter (fun p : ℕ => U < (p:ℝ) ∧ (p:ℝ) ≤ U)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro p _
    simp only [Bool.not_eq_true,decide_eq_false_iff_not,not_and]
    exact not_le_of_gt
  simp only [partBetween,he,List.prod_nil]

lemma descending_chain_zero (Y : ℕ → ℝ) (k : ℕ)
    (hY : ∀ j < k,Y (j+1) ≤ Y j) : Y k ≤ Y 0 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    exact (hY k (by omega)).trans (ih (fun j hj => hY j (by omega)))

lemma partBetween_adjacent_product (n : ℕ) (Y : ℕ → ℝ) (k : ℕ)
    (hY : ∀ j < k,Y (j+1) ≤ Y j) :
    (∏ j ∈ Finset.range k,partBetween n (Y (j+1)) (Y j))=partBetween n (Y k) (Y 0) := by
  induction k with
  | zero => simp [partBetween_self]
  | succ k ih =>
    have hk0 := descending_chain_zero Y k (fun j hj => hY j (by omega))
    rw [Finset.prod_range_succ,ih (fun j hj => hY j (by omega)),mul_comm]
    exact partBetween_split n (hY k (by omega)) hk0

end TotientAsymptotic

end

end OAI
