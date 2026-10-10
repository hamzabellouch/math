import OAI.NumberTheory.EgyptianFractions.Defs

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CountingPadding

def pad {k : ℕ} (n : Fin (k + 1) → ℕ) : Fin (k + 2) → ℕ :=
  Fin.snoc (Fin.snoc (fun i : Fin k => n i.castSucc) (n (Fin.last k) + 1))
    (n (Fin.last k) * (n (Fin.last k) + 1))

lemma strictMono_snoc {α : Type*} [LinearOrder α] {k : ℕ}
    (f : Fin k → α) (a : α) (hf : StrictMono f) (ha : ∀ i, f i < a) :
    StrictMono (Fin.snoc f a) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last => exact False.elim (not_lt_of_ge (Fin.le_last j) hij)
  | cast i =>
    cases j using Fin.lastCases with
    | last => simpa using ha i
    | cast j => simpa using hf (show i < j from hij)

lemma pad_strictMono {k : ℕ} (n : Fin (k + 1) → ℕ)
    (hn : StrictMono n) (hmax : 1 < n (Fin.last k)) : StrictMono (pad n) := by
  apply strictMono_snoc
  · apply strictMono_snoc
    · intro i j hij
      exact hn (show i.castSucc < j.castSucc from hij)
    · intro i
      exact lt_trans (hn i.castSucc_lt_last) (Nat.lt_succ_self _)
  · intro i
    cases i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      nlinarith
    | cast i =>
      simp only [Fin.snoc_castSucc]
      have hi := hn i.castSucc_lt_last
      nlinarith

lemma pad_positive {k : ℕ} (n : Fin (k + 1) → ℕ)
    (hn : ∀ i, 1 ≤ n i) : ∀ i, 1 ≤ pad n i := by
  intro i
  cases i using Fin.lastCases with
  | last =>
    simp only [pad, Fin.snoc_last]
    have h := hn (Fin.last k)
    nlinarith
  | cast i =>
    cases i using Fin.lastCases with
    | last => simp [pad]
    | cast i => simpa [pad] using hn i.castSucc

lemma pad_sum {k : ℕ} (n : Fin (k + 1) → ℕ)
    (hmax : 0 < n (Fin.last k)) :
    (∑ i : Fin (k + 2), (1 : ℚ) / (pad n i : ℚ)) =
      ∑ i : Fin (k + 1), (1 : ℚ) / (n i : ℚ) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [pad, Fin.snoc_castSucc, Fin.snoc_last, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hn : (n (Fin.last k) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmax)
  have hn1 : (n (Fin.last k) : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pad_injective {k : ℕ} : Function.Injective (@pad k) := by
  intro n m h
  have hparts := Fin.snoc_injective2 h
  have hparts' := Fin.snoc_injective2 hparts.1
  have hlast : n (Fin.last k) = m (Fin.last k) := Nat.add_right_cancel hparts'.2
  funext i
  cases i using Fin.lastCases with
  | last => exact hlast
  | cast i => exact congr_fun hparts'.1 i

lemma last_gt_one {k : ℕ} (hk : 1 ≤ k) (n : Fin (k + 1) → ℕ)
    (hn : IsOneExpansion n) : 1 < n (Fin.last k) := by
  let i : Fin k := ⟨0, hk⟩
  exact lt_of_le_of_lt (hn.1 i.castSucc) (hn.2.1 i.castSucc_lt_last)

lemma pad_isOneExpansion {k : ℕ} (hk : 1 ≤ k) (n : Fin (k + 1) → ℕ)
    (hn : IsOneExpansion n) : IsOneExpansion (pad n) := by
  refine ⟨pad_positive n hn.1, pad_strictMono n hn.2.1 (last_gt_one hk n hn), ?_⟩
  rw [pad_sum n (lt_of_lt_of_le Nat.zero_lt_one (hn.1 _))]
  exact hn.2.2

lemma F_succ_le {k : ℕ} (hk : 1 ≤ k) (hfinite : Set.Finite (OneExpansions (k + 2))) :
    F (k + 1) ≤ F (k + 2) := by
  refine Set.ncard_le_ncard_of_injOn (@pad k) ?_ pad_injective.injOn hfinite
  intro n hn
  exact pad_isOneExpansion hk n hn

lemma F_le_succ {k : ℕ} (hk : 2 ≤ k) (hfinite : Set.Finite (OneExpansions (k + 1))) :
    F k ≤ F (k + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact F_succ_le (by omega) hfinite

lemma F_le_of_le (hfinite : ∀ k, Set.Finite (OneExpansions k))
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : F a ≤ F b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact le_trans ih (F_le_succ (by omega) (hfinite _))

end Problem337.CountingPadding

end

end OAI
