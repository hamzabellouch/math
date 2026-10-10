import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedBucket
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedPreparedSeparator

namespace OAI

/-! # A residue bucket using the already-prepared separator tables -/

namespace LowSpaceSubsetSum.BudgetedPreparedBucket

variable {n g : ℕ}

def run (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (B : ℕ) (blocks : List (StoredSeparatorCheck.Block n g)) (target : ℤ) (budget : ℕ) :=
  BudgetedBucket.run D FL FR hFL hFR B
    (BudgetedSeparatorArrays.execute (2 ^ n) target blocks) budget

noncomputable def checkBill (D : RepresentationBucketData n g)
    (families : Fin 4 → Array (Finset (Fin g)))
    (left right : Array (StoredEntry n)) : ℕ :=
  inputScale D.right.input ^ 6 *
    ((D.coordinates.check families D.target (left.map StoredEntry.semantic).toList
      (right.map StoredEntry.semantic).toList).scans + left.size + right.size + 1)

noncomputable def allowance (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (B : ℕ) (families : Fin 4 → Array (Finset (Fin g))) : ℕ :=
  BudgetedBucket.allowance D FL FR hFL hFR B (checkBill D families)

theorem value (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (hleft : D.left.maskRestriction = MaskRestriction.empty) (B : ℕ)
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (budget : ℕ) (v : Bool) (remaining : ℕ)
    (h : (run D FL FR hFL hFR B (PreparedSeparatorContext.prepare rows families hsize).1
      D.target budget).1 = some (v, remaining)) :
    v = D.run B (fun i => (families i).map SeparatorStoredMasks.decode) ∧ remaining ≤ budget := by
  apply BudgetedBucket.value D FL FR hFL hFR hleft B
    (fun i => (families i).map SeparatorStoredMasks.decode) _ ?_ budget v remaining h
  intro a b budget v remaining hv
  refine ⟨?_, (BudgetedSeparatorArrays.account _ _ _ a b budget).2 v remaining hv |>.1⟩
  simpa only [RepresentationBucketData.check, Array.toList_map] using
    BudgetedPreparedSeparator.value D.coordinates rows hrows families hsize
      (2 ^ n) rfl D.target a b budget v remaining hv

theorem complete (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (B : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g) (budget : ℕ)
    (hb : allowance D FL FR hFL hFR B
      (fun i => (families i).map SeparatorStoredMasks.decode) ≤ budget) :
    ∃ v remaining,
      (run D FL FR hFL hFR B (PreparedSeparatorContext.prepare rows families hsize).1
        D.target budget).1 = some (v, remaining) := by
  apply BudgetedBucket.complete D FL FR hFL hFR B _
    (checkBill D (fun i => (families i).map SeparatorStoredMasks.decode)) ?_ ?_ hn budget hb
  · intro a b budget hbudget
    have ha := BudgetedPreparedSeparator.allowance D.right.input hn hg D.coordinates
      rows hrows families hsize (2 ^ n) rfl D.target a b
    have hbudget' : BudgetedSeparatorArrays.allowance (2 ^ n) D.target
        (PreparedSeparatorContext.prepare rows families hsize).1 a b ≤ budget := by
      apply ha.trans
      simpa only [checkBill, Array.toList_map] using hbudget
    exact ⟨_, _, BudgetedSeparatorArrays.complete _ _ _ _ _ _ hbudget'⟩
  · intro a b budget v remaining hv
    simpa only [checkBill, Array.toList_map] using
      BudgetedPreparedSeparator.remaining_bound D.right.input hn hg D.coordinates
        rows hrows families hsize (2 ^ n) rfl D.target a b budget v remaining hv

theorem remaining (D : RepresentationBucketData n g) (FL FR : IndexedMask n)
    (hFL : FL.semantic = D.left.signs) (hFR : FR.semantic = D.right.signs)
    (B : ℕ) (hn : 10000 ≤ n) (hg : g ≤ n)
    (rows : Fin 4 → Vector (Fin n) g)
    (hrows : ∀ i j, (rows i)[j] = D.coordinates.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g)))
    (hsize : ∀ i, (families i).size ≤ 11 * 2 ^ g)
    (budget : ℕ) (v : Bool) (rest : ℕ)
    (h : (run D FL FR hFL hFR B (PreparedSeparatorContext.prepare rows families hsize).1
      D.target budget).1 = some (v, rest)) :
    budget ≤ rest + allowance D FL FR hFL hFR B
      (fun i => (families i).map SeparatorStoredMasks.decode) := by
  apply BudgetedBucket.remaining D FL FR hFL hFR B _
    (checkBill D (fun i => (families i).map SeparatorStoredMasks.decode)) ?_ hn budget v rest h
  intro a b budget v remaining hv
  simpa only [checkBill, Array.toList_map] using
    BudgetedPreparedSeparator.remaining_bound D.right.input hn hg D.coordinates
      rows hrows families hsize (2 ^ n) rfl D.target a b budget v remaining hv

end LowSpaceSubsetSum.BudgetedPreparedBucket

end OAI
