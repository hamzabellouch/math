import OAI.Combinatorics.CompleteCrossing.Hill
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace OAI

/-! Residue fibers, same-page residues, and parity counts. -/

section

noncomputable section
namespace Paper170

theorem sameColorResidues_eq_intervals {n k : ℕ} (hn : 3 ≤ n)
    (hk : k ≤ n / 2) :
    sameColorResidues n k =
      Finset.Ico 0 (n / 2 - k) ∪ Finset.Ico (n / 2) (n - k) := by
  ext r
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range,
    residueColor, decide_eq_decide, Finset.mem_union, Finset.mem_Ico]
  by_cases hr : r < n
  · rw [Nat.mod_eq_of_lt hr]
    by_cases hrs : r + k < n
    · rw [Nat.mod_eq_of_lt hrs]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ r + k),
        Nat.mod_eq_of_lt (by omega : r + k - n < n)]
      omega
  · omega

theorem sameColorResidues_eq_intervals_large {n k : ℕ} (hn : 3 ≤ n)
    (hk : n / 2 < k) (hkn : k < n) :
    sameColorResidues n k =
      Finset.Ico (n - k) (n / 2) ∪ Finset.Ico (n + n / 2 - k) n := by
  ext r
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range,
    residueColor, decide_eq_decide, Finset.mem_union, Finset.mem_Ico]
  by_cases hr : r < n
  · rw [Nat.mod_eq_of_lt hr]
    by_cases hrs : r + k < n
    · rw [Nat.mod_eq_of_lt hrs]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega : n ≤ r + k),
        Nat.mod_eq_of_lt (by omega : r + k - n < n)]
      omega
  · omega

theorem sameColorResidues_card {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n - 2) :
    (sameColorResidues n k).card = n - 2 * min k (n - k) := by
  by_cases hh : k ≤ n / 2
  · rw [sameColorResidues_eq_intervals hn hh]
    have hd : Disjoint (Finset.Ico 0 (n / 2 - k)) (Finset.Ico (n / 2) (n - k)) := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_Ico]
      omega
    rw [Finset.card_union_of_disjoint hd, Nat.card_Ico, Nat.card_Ico,
      min_eq_left (by omega : k ≤ n - k)]
    omega
  · rw [sameColorResidues_eq_intervals_large hn (by omega) (by omega)]
    have hd : Disjoint (Finset.Ico (n - k) (n / 2)) (Finset.Ico (n + n / 2 - k) n) := by
      apply Finset.disjoint_left.mpr
      simp only [Finset.mem_Ico]
      omega
    rw [Finset.card_union_of_disjoint hd, Nat.card_Ico, Nat.card_Ico,
      min_eq_right (by omega : n - k ≤ k)]
    omega

@[simp] theorem residueColor_mod (n r : ℕ) : residueColor n (r % n) = residueColor n r := by
  simp [residueColor]

theorem residueColor_add_half {m : ℕ} (hm : 0 < m) (r : ℕ) :
    residueColor (2 * m) (r + m) = !residueColor (2 * m) r := by
  have hr := Nat.mod_lt r (by omega : 0 < 2 * m)
  simp only [residueColor, Nat.mul_div_right m (by decide : 0 < 2)]
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : m < 2 * m)]
  by_cases hh : r % (2 * m) < m
  · rw [Nat.mod_eq_of_lt (by omega : r % (2 * m) + m < 2 * m)]
    simp [hh, show ¬r % (2 * m) + m < m by omega]
  · rw [Nat.mod_eq_sub_mod (by omega : 2 * m ≤ r % (2 * m) + m),
      Nat.mod_eq_of_lt (by omega : r % (2 * m) + m - 2 * m < 2 * m)]
    simp [hh, show r % (2 * m) + m - 2 * m < m by omega]

theorem sameColorResidues_half_shift {m k r : ℕ} (hm : 0 < m)
    (hr : r < 2 * m) :
    r ∈ sameColorResidues (2 * m) k ↔
      (r + m) % (2 * m) ∈ sameColorResidues (2 * m) k := by
  simp only [sameColorResidues, Finset.mem_filter, Finset.mem_range, hr,
    Nat.mod_lt _ (by omega : 0 < 2 * m), true_and, residueColor_mod]
  rw [show residueColor (2 * m) ((r + m) % (2 * m) + k) =
      residueColor (2 * m) (r + k + m) by simp [residueColor, Nat.add_mod, Nat.add_right_comm]]
  rw [residueColor_add_half hm, residueColor_add_half hm]
  simp

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem residueFiber_card_odd {n b r : ℕ} (hn : Odd n) (hr : r < n) :
    (residueFiber n b r).card = 1 := by
  let f : Fin n → Fin n := fun a => ⟨(2 * a.val + b) % n, Nat.mod_lt _ (by omega)⟩
  have hi : Function.Injective f := by
    intro a c h
    have hmod : Nat.ModEq n (2 * a.val + b) (2 * c.val + b) := congrArg Fin.val h
    have he := (hmod.add_right_cancel' b).cancel_left_of_coprime hn.coprime_two_right
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt c.isLt] using he
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hi) ⟨r, hr⟩
  have hset : residueFiber n b r = {a.val} := by
    ext c
    simp only [residueFiber, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hcr⟩
      have he : f ⟨c, hc⟩ = f a := by
        rw [ha]
        exact Fin.ext hcr
      exact congrArg Fin.val (hi he)
    · rintro rfl
      exact ⟨a.isLt, congrArg Fin.val ha⟩
  rw [hset, Finset.card_singleton]

theorem add_mod_inj {n a c b : ℕ} (ha : a < n) (hc : c < n)
    (h : (a + b) % n = (c + b) % n) : a = c := by
  have he := Nat.ModEq.add_right_cancel' b h
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using he

theorem add_mod_surj {n r : ℕ} (hr : r < n) (b : ℕ) :
    ∃ a < n, (a + b) % n = r := by
  let f : Fin n → Fin n := fun a => ⟨(a.val + b) % n, Nat.mod_lt _ (by omega)⟩
  have hi : Function.Injective f := by
    intro a c h
    exact Fin.ext (add_mod_inj a.isLt c.isLt (congrArg Fin.val h))
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hi) ⟨r, hr⟩
  exact ⟨a.val, a.isLt, congrArg Fin.val ha⟩

theorem doubled_residue {m a b r : ℕ} :
    (2 * a + b) % (2 * m) = r ↔
      (a + b / 2) % m = r / 2 ∧ b % 2 = r % 2 := by
  have hh : (2 * a + b) % (2 * m) = b % 2 + 2 * ((a + b / 2) % m) := by
    rw [Nat.mod_mul]
    congr 1
    · omega
    · rw [show (2 * a + b) / 2 = a + b / 2 by omega]
  rw [hh]
  omega

theorem residueFiber_card_even {m b r : ℕ} (hm : 0 < m) (hr : r < 2 * m) :
    (residueFiber (2 * m) b r).card = if r % 2 = b % 2 then 2 else 0 := by
  by_cases hp : r % 2 = b % 2
  · rw [ite_eq_left hp]
    obtain ⟨a, ha, har⟩ := add_mod_surj (show r / 2 < m by omega) (b / 2)
    have hset : residueFiber (2 * m) b r = {a, a + m} := by
      ext c
      simp only [residueFiber, Finset.mem_filter, Finset.mem_range,
        Finset.mem_insert, Finset.mem_singleton, doubled_residue]
      constructor
      · rintro ⟨hc, hcr, _⟩
        have he : c % m = a := add_mod_inj (Nat.mod_lt _ hm) ha
          (by simpa only [Nat.add_mod, Nat.mod_mod] using hcr.trans har.symm)
        by_cases hcm : c < m
        · left
          simpa only [Nat.mod_eq_of_lt hcm] using he
        · right
          rw [Nat.mod_eq_sub_mod (by omega : m ≤ c),
            Nat.mod_eq_of_lt (by omega : c - m < m)] at he
          omega
      · rintro (rfl | rfl)
        · exact ⟨by omega, har, hp.symm⟩
        · refine ⟨by omega, ?_, hp.symm⟩
          simpa only [Nat.add_right_comm a m (b / 2), Nat.add_mod_right] using har
    rw [hset, Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  · rw [ite_eq_right hp]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a
    simp only [residueFiber, Finset.mem_filter, Finset.mem_range, doubled_residue]
    rintro ⟨_, _, he⟩
    exact hp he.symm

end Paper170

end
end

section

noncomputable section
namespace Paper170

theorem parity_balance_of_involution (s : Finset ℕ) (f : ℕ → ℕ) (c : ℕ)
    (hmap : ∀ r ∈ s, f r ∈ s) (hinv : ∀ r ∈ s, f (f r) = r)
    (hpar : ∀ r ∈ s, (f r + c) % 2 ≠ (r + c) % 2) :
    (s.filter (fun r => (r + c) % 2 = 0)).card =
      (s.filter (fun r => (r + c) % 2 = 1)).card := by
  apply Finset.card_nbij' f f
  · intro r hr
    obtain ⟨hs, he⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hmap r hs, by have := hpar r hs; omega⟩
  · intro r hr
    obtain ⟨hs, he⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨hmap r hs, by have := hpar r hs; omega⟩
  · intro r hr
    exact hinv r (Finset.mem_filter.mp hr).1
  · intro r hr
    exact hinv r (Finset.mem_filter.mp hr).1

theorem interval_parity_balance {a b : ℕ} (heven : Even (b - a)) (c : ℕ) :
    ((Finset.Ico a b).filter (fun r => (r + c) % 2 = 0)).card =
      ((Finset.Ico a b).filter (fun r => (r + c) % 2 = 1)).card := by
  obtain ⟨t, ht⟩ := heven
  let f : ℕ → ℕ := fun r => if (r - a) % 2 = 0 then r + 1 else r - 1
  apply parity_balance_of_involution (Finset.Ico a b) f c
  · intro r hr
    simp only [Finset.mem_Ico] at hr ⊢
    dsimp [f]
    split_ifs <;> omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    dsimp [f]
    split_ifs <;> omega
  · intro r hr
    simp only [Finset.mem_Ico] at hr
    dsimp [f]
    split_ifs <;> omega

theorem firstGapParity_balance {k : ℕ} (hk : Odd k) (b : ℕ) :
    (firstGapParity k b 0).card = (firstGapParity k b 1).card := by
  have heven : Even (k - 1) := by
    rw [Nat.even_iff]
    obtain ⟨t, ht⟩ := hk
    omega
  have heq : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    obtain ⟨t, ht⟩ := hk
    omega
  simpa only [firstGapParity, heq] using interval_parity_balance heven b

theorem parity_balance_union (s t : Finset ℕ) (hd : Disjoint s t)
    (hs : (s.filter (fun r => r % 2 = 0)).card = (s.filter (fun r => r % 2 = 1)).card)
    (ht : (t.filter (fun r => r % 2 = 0)).card = (t.filter (fun r => r % 2 = 1)).card) :
    ((s ∪ t).filter (fun r => r % 2 = 0)).card =
      ((s ∪ t).filter (fun r => r % 2 = 1)).card := by
  have hdis (p : ℕ) : Disjoint (s.filter (fun r => r % 2 = p))
      (t.filter (fun r => r % 2 = p)) := hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  simp only [Finset.filter_union, Finset.card_union_of_disjoint (hdis 0),
    Finset.card_union_of_disjoint (hdis 1), hs, ht]

theorem sameColorResidues_parity_balance {m k : ℕ} (hm : 0 < m)
    (hk : 2 ≤ k) (hkn : k ≤ 2 * m - 2) (hparity : Odd m ∨ Even k) :
    (sameColorResiduesParity (2 * m) k 0).card =
      (sameColorResiduesParity (2 * m) k 1).card := by
  by_cases hmo : Odd m
  · obtain ⟨t, ht⟩ := hmo
    let f : ℕ → ℕ := fun r => if r < m then r + m else r - m
    have hform (r : ℕ) (hr : r < 2 * m) : f r = (r + m) % (2 * m) := by
      dsimp [f]
      split_ifs with h
      · rw [Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    apply parity_balance_of_involution (sameColorResidues (2 * m) k) f 0
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      rw [hform r hrl]
      exact (sameColorResidues_half_shift hm hrl).mp hr
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      dsimp [f]
      split_ifs <;> omega
    · intro r hr
      have hrl : r < 2 * m := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
      dsimp [f]
      split_ifs <;> omega
  · have hme : Even m := Nat.not_odd_iff_even.mp hmo
    have hke : Even k := hparity.resolve_left hmo
    have hm₂ : 3 ≤ 2 * m := by omega
    have even_diff (a b : ℕ) (ha : Even a) (hb : Even b) : Even (a - b) := by
      rw [Nat.even_iff] at *
      omega
    unfold sameColorResiduesParity
    by_cases hhalf : k ≤ m
    · rw [sameColorResidues_eq_intervals hm₂ (by simpa using hhalf)]
      simp only [Nat.mul_div_right m (by decide : 0 < 2)]
      apply parity_balance_union
      · apply Finset.disjoint_left.mpr
        simp only [Finset.mem_Ico]
        omega
      · simpa using interval_parity_balance (a := 0) (b := m - k)
          (by simpa using even_diff m k hme hke) 0
      · have he : Even (2 * m - k - m) := by
          apply even_diff _ _ (even_diff _ _ (by simp) hke) hme
        simpa using interval_parity_balance he 0
    · rw [sameColorResidues_eq_intervals_large hm₂ (by simpa using Nat.lt_of_not_ge hhalf) (by omega)]
      simp only [Nat.mul_div_right m (by decide : 0 < 2)]
      apply parity_balance_union
      · apply Finset.disjoint_left.mpr
        simp only [Finset.mem_Ico]
        omega
      · have he : Even (m - (2 * m - k)) := even_diff _ _ hme (even_diff _ _ (by simp) hke)
        simpa using interval_parity_balance he 0
      · have he : Even (2 * m - (2 * m + m - k)) :=
          even_diff _ _ (by simp) (even_diff _ _
            (by simpa only [two_mul, add_assoc] using hme.add hme |>.add hme) hke)
        simpa using interval_parity_balance he 0

end Paper170

end
end

end OAI
