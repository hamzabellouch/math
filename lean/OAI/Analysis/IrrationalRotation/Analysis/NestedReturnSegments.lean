import Mathlib.Data.Nat.Find
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

namespace OAI

namespace Invariant233.NestedReturnSegments

variable {X : Type*} (f : X → X) {A B : Set X} {x : X}

theorem return_segment_fits {r h H : ℕ} (hr : r < H)
    (hH : f^[H] x ∈ A)
    (havoid : ∀ t : ℕ, 0 < t → t < h → f^[t] (f^[r] x) ∉ A) :
    r + h ≤ H := by
  by_contra hbad
  have hpos : 0 < H - r := Nat.sub_pos_of_lt hr
  have hsmall : H - r < h := by omega
  have hnot := havoid (H - r) hpos hsmall
  apply hnot
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hr)]
  exact hH

theorem nested_return_segment_fits {r h H : ℕ} (hBA : B ⊆ A) (hr : r < H)
    (hH : f^[H] x ∈ B)
    (havoid : ∀ t : ℕ, 0 < t → t < h → f^[t] (f^[r] x) ∉ A) :
    r + h ≤ H :=
  return_segment_fits f hr (hBA hH) havoid

theorem exists_contained_first_return_segment {H k : ℕ}
    (hx : x ∈ A) (hH : f^[H] x ∈ A) (hk : k < H) :
    ∃ r h : ℕ, r ≤ k ∧ k < r + h ∧ r + h ≤ H ∧
      f^[r] x ∈ A ∧ 0 < h ∧ f^[h] (f^[r] x) ∈ A ∧
      ∀ t : ℕ, 0 < t → t < h → f^[t] (f^[r] x) ∉ A := by
  classical
  let P : ℕ → Prop := fun r => f^[r] x ∈ A
  let r := Nat.findGreatest P k
  have hr : r ≤ k := Nat.findGreatest_le k
  have hrA : f^[r] x ∈ A :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le k) (by simpa [P] using hx)
  have hrH : r < H := by omega
  have hpos : 0 < H - r := Nat.sub_pos_of_lt hrH
  have hend : f^[H - r] (f^[r] x) ∈ A := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hrH)]
    exact hH
  have hex : ∃ h : ℕ, 0 < h ∧ f^[h] (f^[r] x) ∈ A :=
    ⟨H - r, hpos, hend⟩
  let h := Nat.find hex
  have hh : 0 < h ∧ f^[h] (f^[r] x) ∈ A := Nat.find_spec hex
  have hbound : h ≤ H - r := Nat.find_min' hex ⟨hpos, hend⟩
  have hcover : k < r + h := by
    by_contra hbad
    have hle : r + h ≤ k := by omega
    have hlt : r < r + h := by omega
    have hnot : ¬P (r + h) := Nat.findGreatest_is_greatest hlt hle
    apply hnot
    dsimp [P]
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact hh.2
  refine ⟨r, h, hr, hcover, by omega, hrA, hh.1, hh.2, ?_⟩
  intro t ht hth hmem
  exact Nat.find_min hex hth ⟨ht, hmem⟩

theorem exists_nested_first_return_segment {H k : ℕ}
    (hBA : B ⊆ A) (hx : x ∈ B) (hH : f^[H] x ∈ B) (hk : k < H) :
    ∃ r h : ℕ, r ≤ k ∧ k < r + h ∧ r + h ≤ H ∧
      f^[r] x ∈ A ∧ 0 < h ∧ f^[h] (f^[r] x) ∈ A ∧
      ∀ t : ℕ, 0 < t → t < h → f^[t] (f^[r] x) ∉ A :=
  exists_contained_first_return_segment f (hBA hx) (hBA hH) hk

theorem first_return_time_unique {y : X} {h j : ℕ}
    (hh : 0 < h) (hj : 0 < j)
    (hhA : f^[h] y ∈ A) (hjA : f^[j] y ∈ A)
    (havoid : ∀ t : ℕ, 0 < t → t < h → f^[t] y ∉ A)
    (javoid : ∀ t : ℕ, 0 < t → t < j → f^[t] y ∉ A) : h = j := by
  apply Nat.le_antisymm
  · by_contra hbad
    exact havoid j hj (by omega) hjA
  · by_contra hbad
    exact javoid h hh (by omega) hhA

theorem first_return_segment_start_unique {r h s j k : ℕ}
    (hr : r ≤ k) (hrk : k < r + h) (hs : s ≤ k) (hsk : k < s + j)
    (hrA : f^[r] x ∈ A) (hsA : f^[s] x ∈ A)
    (havoid : ∀ t : ℕ, 0 < t → t < h → f^[t] (f^[r] x) ∉ A)
    (javoid : ∀ t : ℕ, 0 < t → t < j → f^[t] (f^[s] x) ∉ A) :
    r = s := by
  apply Nat.le_antisymm
  · by_contra hbad
    have hsr : s < r := by omega
    have hfit := return_segment_fits f hsr hrA javoid
    omega
  · by_contra hbad
    have hrs : r < s := by omega
    have hfit := return_segment_fits f hrs hsA havoid
    omega

theorem first_return_segment_unique {r h s j k : ℕ}
    (hr : r ≤ k) (hrk : k < r + h) (hs : s ≤ k) (hsk : k < s + j)
    (hrA : f^[r] x ∈ A) (hsA : f^[s] x ∈ A)
    (hhA : f^[h] (f^[r] x) ∈ A) (hjA : f^[j] (f^[s] x) ∈ A)
    (havoid : ∀ t : ℕ, 0 < t → t < h → f^[t] (f^[r] x) ∉ A)
    (javoid : ∀ t : ℕ, 0 < t → t < j → f^[t] (f^[s] x) ∉ A) :
    r = s ∧ h = j := by
  have hrs := first_return_segment_start_unique f hr hrk hs hsk hrA hsA havoid javoid
  subst s
  exact ⟨rfl, first_return_time_unique f (by omega) (by omega) hhA hjA havoid javoid⟩

end Invariant233.NestedReturnSegments

end OAI
