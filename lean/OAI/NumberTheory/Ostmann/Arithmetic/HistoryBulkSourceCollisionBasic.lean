import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagramParametersBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceCollision
open Construction HistoryBulkDiagramParameters

theorem prime_pairwise_iff_nodup (xs : List ℕ) (hp : ∀ p ∈ xs, p.Prime) :
    xs.Pairwise Nat.Coprime ↔ xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.pairwise_cons, List.nodup_cons]
    have ha := hp a (by simp)
    have ht : ∀ p ∈ xs, p.Prime := fun p h => hp p (by simp [h])
    rw [ih ht]
    constructor
    · rintro ⟨hc, hn⟩
      exact ⟨fun h => (Nat.coprime_primes ha ha).mp (hc a h) rfl, hn⟩
    · rintro ⟨ha', hn⟩
      exact ⟨fun p h => (Nat.coprime_primes ha (ht p h)).mpr
        (fun he => ha' (he ▸ h)), hn⟩

theorem nonbulk_eq_of_erase_eq {xs ys : List SmallSlot}
    (h : xs.map eraseBulkValue = ys.map eraseBulkValue) :
    xs.filter (fun a => a.role ≠ .bulk) = ys.filter (fun a => a.role ≠ .bulk) := by
  have he (zs : List SmallSlot) :
      (zs.map eraseBulkValue).filter (fun a => a.role ≠ .bulk) =
        zs.filter (fun a => a.role ≠ .bulk) := by
    induction zs with
    | nil => rfl
    | cons a zs ih =>
      by_cases ha : a.role = .bulk <;> simpa [eraseBulkValue, ha] using ih
  rw [← he xs, ← he ys, h]

theorem small_outside_pairwise_of_bulk
    (xs : List SmallSlot) (outside : List ℕ)
    (hbulk : ((xs.filter (fun a => a.role = .bulk)).map SmallSlot.value).Pairwise Nat.Coprime)
    (hfixed : (((xs.filter (fun a => a.role ≠ .bulk)).map SmallSlot.value) ++ outside).Pairwise Nat.Coprime)
    (hcross : ∀ a ∈ xs, a.role = .bulk →
      ∀ b ∈ xs, b.role ≠ .bulk → Nat.Coprime a.value b.value)
    (hout : ∀ a ∈ xs, a.role = .bulk → ∀ p ∈ outside, Nat.Coprime a.value p) :
    (xs.map SmallSlot.value ++ outside).Pairwise Nat.Coprime := by
  induction xs with
  | nil => simpa using hfixed
  | cons a xs ih =>
    have hc : ∀ b ∈ xs, b.role = .bulk →
        ∀ c ∈ xs, c.role ≠ .bulk → Nat.Coprime b.value c.value :=
      fun b hb hbr c hc hcr => hcross b (by simp [hb]) hbr c (by simp [hc]) hcr
    have ho : ∀ b ∈ xs, b.role = .bulk → ∀ p ∈ outside, Nat.Coprime b.value p :=
      fun b hb hbr p hp => hout b (by simp [hb]) hbr p hp
    change (a.value :: (xs.map SmallSlot.value ++ outside)).Pairwise Nat.Coprime
    apply List.pairwise_cons.mpr
    by_cases ha : a.role = .bulk
    · have hb := hbulk
      simp only [List.filter_cons, ha, decide_true, ite_true,
        List.map_cons, List.pairwise_cons] at hb
      have hf : ((xs.filter (fun a => a.role ≠ .bulk)).map SmallSlot.value ++ outside).Pairwise Nat.Coprime := by
        simpa [ha] using hfixed
      refine ⟨?_, ih hb.2 hf hc ho⟩
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hp
        by_cases hbr : b.role = .bulk
        · exact hb.1 _ (List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hbmem, by simpa using hbr⟩, rfl⟩)
        · exact hcross a (by simp) ha b (by simp [hbmem]) hbr
      · exact hout a (by simp) ha p hp
    · have hf := hfixed
      have ha' : decide (a.role ≠ .bulk) = true := decide_eq_true ha
      simp only [List.filter_cons, ha', ite_true, List.map_cons, List.cons_append, List.pairwise_cons] at hf
      have hb : ((xs.filter (fun a => a.role = .bulk)).map SmallSlot.value).Pairwise Nat.Coprime := by
        simpa [ha] using hbulk
      refine ⟨?_, ih hb hf.2 hc ho⟩
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hp
        by_cases hbr : b.role = .bulk
        · exact (hcross b (by simp [hbmem]) hbr a (by simp) ha).symm
        · exact hf.1 _ (List.mem_append_left outside (List.mem_map.mpr
            ⟨b, List.mem_filter.mpr ⟨hbmem, by simpa using hbr⟩, rfl⟩))
      · exact hf.1 p (List.mem_append_right _ hp)

theorem small_outside_pairwise_of_reference
    (xs ys : List SmallSlot) (outside : List ℕ)
    (herase : xs.map eraseBulkValue = ys.map eraseBulkValue)
    (href : (ys.map SmallSlot.value ++ outside).Pairwise Nat.Coprime)
    (hprime : ∀ a ∈ xs, a.value.Prime)
    (hbulk : ((xs.filter (fun a => a.role = .bulk)).map SmallSlot.value).Nodup)
    (hcross : ∀ a ∈ xs, a.role = .bulk →
      ∀ b ∈ xs, b.role ≠ .bulk → Nat.Coprime a.value b.value)
    (hout : ∀ a ∈ xs, a.role = .bulk → ∀ p ∈ outside, Nat.Coprime a.value p) :
    (xs.map SmallSlot.value ++ outside).Pairwise Nat.Coprime := by
  apply small_outside_pairwise_of_bulk xs outside
  · apply (prime_pairwise_iff_nodup _ ?_).mpr hbulk
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact hprime a (List.mem_filter.mp ha).1
  · rw [nonbulk_eq_of_erase_eq herase]
    exact href.sublist ((List.filter_sublist).map SmallSlot.value |>.append_right outside)
  · exact hcross
  · exact hout

end Ostmann.Arithmetic.HistoryBulkSourceCollision

end

end OAI
