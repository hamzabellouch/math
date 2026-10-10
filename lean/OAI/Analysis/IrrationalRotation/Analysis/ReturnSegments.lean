import Mathlib

namespace OAI

namespace Invariant233.ReturnSegments

variable {X : Type*} (f : X → X)

def IsFirstReturn (B : Set X) (x : X) (h : ℕ) : Prop :=
  x ∈ B ∧ 0 < h ∧ f^[h] x ∈ B ∧
    ∀ k : ℕ, 0 < k → k < h → f^[k] x ∉ B

variable {f}

theorem IsFirstReturn.le_return {B : Set X} {x : X} {h k : ℕ}
    (hh : IsFirstReturn f B x h) (hk : 0 < k) (hret : f^[k] x ∈ B) :
    h ≤ k := by
  by_contra h
  exact hh.2.2.2 k hk (by omega) hret

theorem IsFirstReturn.unique {B : Set X} {x : X} {h k : ℕ}
    (hh : IsFirstReturn f B x h) (hk : IsFirstReturn f B x k) : h = k := by
  exact le_antisymm (hh.le_return hk.2.1 hk.2.2.1)
    (hk.le_return hh.2.1 hh.2.2.1)

theorem exists_firstReturn_le {B : Set X} {x : X} {H : ℕ}
    (hx : x ∈ B) (hH : 0 < H) (hret : f^[H] x ∈ B) :
    ∃ h : ℕ, IsFirstReturn f B x h ∧ h ≤ H := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ f^[k] x ∈ B := ⟨H, hH, hret⟩
  refine ⟨Nat.find hex, ⟨hx, (Nat.find_spec hex).1,
    (Nat.find_spec hex).2, ?_⟩, Nat.find_min' hex ⟨hH, hret⟩⟩
  intro k hk hkh hmem
  exact Nat.find_min hex hkh ⟨hk, hmem⟩

theorem segment_fits_of_endpoint {B C : Set X} (hCB : C ⊆ B)
    {x : X} {H r h : ℕ} (hret : f^[H] x ∈ C) (hr : r < H)
    (hfirst : IsFirstReturn f B (f^[r] x) h) : r + h ≤ H := by
  have hdiff : 0 < H - r := by omega
  have heq : f^[H - r] (f^[r] x) = f^[H] x := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : r ≤ H)]
  have hle := hfirst.le_return hdiff (heq ▸ hCB hret)
  omega

theorem nested_segment_fits {B C : Set X} (hCB : C ⊆ B)
    {x : X} {H r h : ℕ} (hnew : IsFirstReturn f C x H) (hr : r < H)
    (hold : IsFirstReturn f B (f^[r] x) h) : r + h ≤ H :=
  segment_fits_of_endpoint hCB hnew.2.2.1 hr hold

theorem exists_firstReturn_at_visit {B C : Set X} (hCB : C ⊆ B)
    {x : X} {H r : ℕ} (hret : f^[H] x ∈ C) (hr : r < H)
    (hvisit : f^[r] x ∈ B) :
    ∃! h : ℕ, IsFirstReturn f B (f^[r] x) h ∧ r + h ≤ H := by
  have heq : f^[H - r] (f^[r] x) = f^[H] x := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : r ≤ H)]
  obtain ⟨h, hh, hbound⟩ := exists_firstReturn_le hvisit
    (by omega : 0 < H - r) (heq ▸ hCB hret)
  refine ⟨h, ⟨hh, by omega⟩, ?_⟩
  intro k hk
  exact hk.1.unique hh

theorem IsFirstReturn.no_internal_visit {B : Set X} {x : X} {r h t : ℕ}
    (hh : IsFirstReturn f B (f^[r] x) h) (hrt : r < t) (hth : t < r + h) :
    f^[t] x ∉ B := by
  have heq : f^[t - r] (f^[r] x) = f^[t] x := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega : r ≤ t)]
  rw [← heq]
  exact hh.2.2.2 (t - r) (by omega) (by omega)

theorem segment_unique {B : Set X} {x : X} {r h s k t : ℕ}
    (hr : IsFirstReturn f B (f^[r] x) h)
    (hs : IsFirstReturn f B (f^[s] x) k)
    (hrt : r ≤ t) (htr : t < r + h) (hst : s ≤ t) (hts : t < s + k) :
    r = s ∧ h = k := by
  have hrs : r = s := by
    apply le_antisymm
    · by_contra hnot
      exact hs.no_internal_visit (x := x) (r := s) (h := k) (t := r)
        (by omega : s < r) (by omega : r < s + k) hr.1
    · by_contra hnot
      exact hr.no_internal_visit (x := x) (r := r) (h := h) (t := s)
        (by omega : r < s) (by omega : s < r + h) hs.1
  refine ⟨hrs, ?_⟩
  subst s
  exact hr.unique hs

theorem exists_unique_segment {B C : Set X} (hCB : C ⊆ B)
    {x : X} {H t : ℕ} (hx : x ∈ B) (hret : f^[H] x ∈ C) (ht : t < H) :
    ∃! s : ℕ × ℕ, IsFirstReturn f B (f^[s.1] x) s.2 ∧
      s.1 ≤ t ∧ t < s.1 + s.2 ∧ s.1 + s.2 ≤ H := by
  classical
  let P : ℕ → Prop := fun r => f^[r] x ∈ B
  let r : ℕ := Nat.findGreatest P t
  have hrt : r ≤ t := Nat.findGreatest_le t
  have hvisit : f^[r] x ∈ B :=
    Nat.findGreatest_spec (P := P) (Nat.zero_le t) (by simpa [P] using hx)
  obtain ⟨h, ⟨hh, hfit⟩, _⟩ :=
    exists_firstReturn_at_visit hCB hret (by omega : r < H) hvisit
  have htr : t < r + h := by
    by_contra hnot
    have hreturn : P (r + h) := by
      dsimp [P]
      rw [Nat.add_comm r h, Function.iterate_add_apply]
      exact hh.2.2.1
    have hmax : r + h ≤ r := Nat.le_findGreatest (by omega) hreturn
    have hpos := hh.2.1
    omega
  refine ⟨(r, h), ⟨hh, hrt, htr, hfit⟩, ?_⟩
  rintro ⟨s, k⟩ ⟨hs, hst, hts, _⟩
  obtain ⟨hrs, hhk⟩ := segment_unique hs hh hst hts hrt htr
  exact Prod.ext hrs hhk

theorem nested_return_concatenation {B C : Set X} (hCB : C ⊆ B)
    {x : X} {H : ℕ} (hnew : IsFirstReturn f C x H) :
    ∀ t < H, ∃! s : ℕ × ℕ, IsFirstReturn f B (f^[s.1] x) s.2 ∧
      s.1 ≤ t ∧ t < s.1 + s.2 ∧ s.1 + s.2 ≤ H := by
  intro t ht
  exact exists_unique_segment hCB (hCB hnew.1) hnew.2.2.1 ht

end Invariant233.ReturnSegments

end OAI
