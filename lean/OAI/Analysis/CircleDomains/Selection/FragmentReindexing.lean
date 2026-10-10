import OAI.Analysis.CircleDomains.Selection.LastEntryFragmentArray

namespace OAI

/-! A cofinal reindexing preserves each fixed actual fragment eventually;
only the deliberately unused early triangular entries can differ. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem firstExitFragmentArray_reindex_eventually
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X) (s : ℕ → ℕ) (hs : ∀n, n ≤ s n)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) < firstExitTime (Γ n).1.val (V j))
    (hcutS : ∀n j, j ≤ n → firstExitTime (Γ (s n)).1.val (V (j+1)) < firstExitTime (Γ (s n)).1.val (V j))
    (j : ℕ) : ∀ᶠn in atTop,
    firstExitFragmentArray d hU (fun n => Γ (s n)) V hcutS n j =
      firstExitFragmentArray d hU Γ V hcut (s n) j := by
  filter_upwards [eventually_ge_atTop j] with n hn
  rw [firstExitFragmentArray_eq d hU _ _ hcutS hn,
    firstExitFragmentArray_eq d hU _ _ hcut (hn.trans (hs n))]

theorem lastEntryFragmentArray_reindex_eventually
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X) (s : ℕ → ℕ) (hs : ∀n, n ≤ s n)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hcutS : ∀n j, j ≤ n → lastEntryTime (Γ (s n)).1.val (W j) < lastEntryTime (Γ (s n)).1.val (W (j+1)))
    (j : ℕ) : ∀ᶠn in atTop,
    lastEntryFragmentArray d hU (fun n => Γ (s n)) W hcutS n j =
      lastEntryFragmentArray d hU Γ W hcut (s n) j := by
  filter_upwards [eventually_ge_atTop j] with n hn
  rw [lastEntryFragmentArray_eq d hU _ _ hcutS hn,
    lastEntryFragmentArray_eq d hU _ _ hcut (hn.trans (hs n))]

end CircleDomainRigidity

end

end OAI
