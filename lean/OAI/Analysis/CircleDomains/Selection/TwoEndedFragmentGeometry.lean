import OAI.Analysis.CircleDomains.Selection.FirstExitFragmentGeometry
import OAI.Analysis.CircleDomains.Selection.LastEntryCuts

namespace OAI

/-! The middle interval and both families of endpoint fragments are
pairwise disjoint. This is the common budget geometry for two-ended splicing. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

abbrev CollarFragmentIndex := Option (ℕ ⊕ ℕ)

def collarFragmentLeft {α : Type*} (a b : ℕ → α) : CollarFragmentIndex → α
  | none => a 0
  | some (.inl j) => a (j+1)
  | some (.inr j) => b j

def collarFragmentRight {α : Type*} (a b : ℕ → α) : CollarFragmentIndex → α
  | none => b 0
  | some (.inl j) => a j
  | some (.inr j) => b (j+1)

theorem monotone_interval_interiors {α : Type*} [LinearOrder α] (b : ℕ → α) (hb : Monotone b) :
    Pairwise (Disjoint on fun j => Ioo (b j) (b (j+1))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (hi.2.trans_le (hb (Nat.add_one_le_iff.mpr hlt))).not_ge hj.1.le
  · exact (hj.2.trans_le (hb (Nat.add_one_le_iff.mpr hgt))).not_ge hi.1.le

theorem twoEnded_interval_interiors_disjoint {α : Type*} [LinearOrder α]
    (a b : ℕ → α) (ha : Antitone a) (hb : Monotone b) (hab : a 0 < b 0) :
    Pairwise (Disjoint on fun i => Ioo (collarFragmentLeft a b i) (collarFragmentRight a b i)) := by
  intro i j hij
  have hleft (k : ℕ) : a k ≤ a 0 := ha (Nat.zero_le k)
  have hright (k : ℕ) : b 0 ≤ b k := hb (Nat.zero_le k)
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases j with
      | inl k =>
        exact disjoint_left.mpr (fun _ ht hs =>
          (hs.2.trans_le (hleft k)).not_ge ht.1.le)
      | inr k =>
        exact disjoint_left.mpr (fun _ ht hs =>
          (ht.2.trans_le (hright k)).not_ge hs.1.le)
  | some i =>
    cases i with
    | inl k =>
      cases j with
      | none =>
        exact disjoint_left.mpr (fun _ ht hs =>
          (ht.2.trans_le (hleft k)).not_ge hs.1.le)
      | some j =>
        cases j with
        | inl l =>
          exact antitone_interval_interiors a ha (fun h => hij (by rw [h]))
        | inr l =>
          exact disjoint_left.mpr (fun _ ht hs =>
            (ht.2.trans_le ((hleft k).trans (hab.le.trans (hright l)))).not_ge hs.1.le)
    | inr k =>
      cases j with
      | none =>
        exact disjoint_left.mpr (fun _ ht hs =>
          (hs.2.trans_le (hright k)).not_ge ht.1.le)
      | some j =>
        cases j with
        | inl l =>
          exact disjoint_left.mpr (fun _ ht hs =>
            (hs.2.trans_le ((hleft l).trans (hab.le.trans (hright k)))).not_ge ht.1.le)
        | inr l =>
          exact monotone_interval_interiors b hb (fun h => hij (by rw [h]))

variable {X : Type*} [MetricSpace X]

theorem lastEntryTime_monotone (γ : C(PathTime, X)) (W : ℕ → Set X)
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W) (hstart : γ ⊥ ∉ W 0) :
    Monotone (fun j => lastEntryTime γ (W j)) := by
  have h := firstExitTime_antitone (reversedPath γ) W hW hanti
    ((reversedPath_one γ).symm ▸ hstart)
  intro i j hij
  exact unitInterval.symm_le_symm.mpr (h hij)

theorem lastEntryFragments_strict (γ : C(PathTime, X)) (W : ℕ → Set X)
    (hW : ∀j, IsOpen (W j)) (hnest : ∀j, closure (W (j+1)) ⊆ W j)
    {n : ℕ} (hstart : γ ⊥ ∉ W 0) (hend : γ ⊤ ∈ W (n+1)) {j : ℕ} (hj : j ≤ n) :
    lastEntryTime γ (W j) < lastEntryTime γ (W (j+1)) := by
  have hanti : Antitone W := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  exact lastEntry_strict_nested γ (hW (j+1)) (hW j) (hnest j)
    (fun h => hstart (hanti (Nat.zero_le j) h)) (hanti (Nat.add_le_add_right hj 1) hend)

end CircleDomainRigidity

end

end OAI
