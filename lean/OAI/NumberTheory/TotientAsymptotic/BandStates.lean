import OAI.NumberTheory.TotientAsymptotic.PrimeBandProducts

namespace OAI

/-! Finite factor states for the successive cutoffs in Ford's iteration. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def factorProduct {b : ℕ} (t : ShiftedPair b) : ℕ := ∏ j,t.left j

def lowerState {b : ℕ} (t : ShiftedPair b) (U : ℝ) : ShiftedPair b where
  left j := partBelow (t.left j) U
  right j := partBelow (t.right j) U
  remainder := t.remainder

def stateBand {b k : ℕ} (hk : k ≤ b) (t : ShiftedPair b) (U V : ℝ) : PairedFactors k :=
  (fun j => partBetween (t.left (Fin.castLE hk j)) U V,
   fun j => partBetween (t.right (Fin.castLE hk j)) U V)

lemma fin_prod_initial {b k : ℕ} (hk : k ≤ b) (f : Fin b → ℕ)
    (hf : ∀ j : Fin b,k ≤ j.val → f j=1) :
    (∏ j : Fin b,f j)=∏ j : Fin k,f (Fin.castLE hk j) := by
  classical
  let A := (Finset.univ : Finset (Fin k)).image (Fin.castLE hk)
  have he : (∏ j ∈ A,f j)=∏ j : Fin b,f j := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro j hj hjA
    apply hf j
    by_contra h
    have hjk : j.val < k := Nat.lt_of_not_ge h
    exact hjA (Finset.mem_image.mpr ⟨⟨j.val,hjk⟩,Finset.mem_univ _,Fin.ext rfl⟩)
  rw [← he,Finset.prod_image]
  intro j hj l hl h
  exact Fin.ext (congrArg (fun z : Fin b => z.val) h)

lemma stateBand_product {b k : ℕ} (hk : k ≤ b) (t : ShiftedPair b) (U V : ℝ)
    (hpos : ∀ j,t.left j ≠ 0)
    (ht : ∀ j : Fin b,k ≤ j.val → (largestPrimeFactor (t.left j):ℝ) ≤ U) :
    pairedProduct (stateBand hk t U V)=partBetween (factorProduct t) U V := by
  rw [factorProduct,partBetween_prod _ _ (fun j _ => hpos j)]
  exact (fin_prod_initial hk _ (fun j hj => partBetween_eq_one_of_largest_le (ht j hj))).symm

lemma lowerState_recover {b k : ℕ} (hk : k ≤ b) {U V : ℝ} (hUV : U ≤ V)
    {t s : ShiftedPair b}
    (ht : ∀ j,partBelow (t.left j) V=t.left j ∧ partBelow (t.right j) V=t.right j)
    (hs : ∀ j,partBelow (s.left j) V=s.left j ∧ partBelow (s.right j) V=s.right j)
    (htail : ∀ j : Fin b,k ≤ j.val →
      partBetween (t.left j) U V=1 ∧ partBetween (t.right j) U V=1)
    (stail : ∀ j : Fin b,k ≤ j.val →
      partBetween (s.left j) U V=1 ∧ partBetween (s.right j) U V=1)
    (hlow : lowerState t U=lowerState s U) (hband : stateBand hk t U V=stateBand hk s U V) : t=s := by
  have hleft (j : Fin b) : t.left j=s.left j := by
    have hlu : partBelow (t.left j) U=partBelow (s.left j) U :=
      congrArg (fun z : ShiftedPair b => z.left j) hlow
    have hbu : partBetween (t.left j) U V=partBetween (s.left j) U V := by
      by_cases hj : j.val < k
      · exact congrArg (fun f : PairedFactors k => f.1 ⟨j.val,hj⟩) hband
      · rw [(htail j (Nat.le_of_not_gt hj)).1,(stail j (Nat.le_of_not_gt hj)).1]
    rw [← (ht j).1,← (hs j).1,← partBelow_band_split _ hUV,← partBelow_band_split _ hUV,hlu,hbu]
  have hright (j : Fin b) : t.right j=s.right j := by
    have hlu : partBelow (t.right j) U=partBelow (s.right j) U :=
      congrArg (fun z : ShiftedPair b => z.right j) hlow
    have hbu : partBetween (t.right j) U V=partBetween (s.right j) U V := by
      by_cases hj : j.val < k
      · exact congrArg (fun f : PairedFactors k => f.2 ⟨j.val,hj⟩) hband
      · rw [(htail j (Nat.le_of_not_gt hj)).2,(stail j (Nat.le_of_not_gt hj)).2]
    rw [← (ht j).2,← (hs j).2,← partBelow_band_split _ hUV,← partBelow_band_split _ hUV,hlu,hbu]
  have hrem₀ := congrArg (fun z : ShiftedPair b => z.remainder) hlow
  have hrem : t.remainder=s.remainder := hrem₀
  cases t
  cases s
  have hl := funext hleft
  have hr := funext hright
  cases hl
  cases hr
  cases hrem
  rfl

end TotientAsymptotic

end

end OAI
