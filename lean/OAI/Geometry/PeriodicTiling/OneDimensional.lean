import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.QuotientGroup
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace PeriodicTilingThree

def oneDValue (b : Fin 2) : ℤ := (b.val : ℤ)

private theorem oneDValue_injective : Function.Injective oneDValue := by
  intro a b h
  apply Fin.ext
  unfold oneDValue at h
  omega

def OneDConv (T : Finset ℤ) (a : ℤ → Fin 2) : Prop :=
  ∀ z : ℤ, (∑ t ∈ T, oneDValue (a (z - t))) = 1

def oneDWindow (M : ℕ) (a : ℤ → Fin 2) (n : ℤ) : Fin M → Fin 2 :=
  fun i => a (n + (i.val : ℤ))

def OneDBlockEq (M : ℕ) (a : ℤ → Fin 2) (n m : ℤ) : Prop :=
  ∀ i : ℤ, 0 ≤ i → i < (M : ℤ) → a (n + i) = a (m + i)

private theorem oneDBlockEq_of_window_eq {M : ℕ} {a : ℤ → Fin 2} {n m : ℤ}
    (h : oneDWindow M a n = oneDWindow M a m) : OneDBlockEq M a n m := by
  intro i hi hiM
  have hcast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi
  have hbound : i.toNat < M := by omega
  have he := congrFun h (⟨i.toNat, hbound⟩ : Fin M)
  simpa only [oneDWindow, hcast] using he

def oneDIndicator (A : Set ℤ) (n : ℤ) : Fin 2 := by
  classical
  exact if n ∈ A then 1 else 0

theorem oneDConv_of_tiles {T : Finset ℤ} {A : Set ℤ} (hTile : Tiles T A) :
    OneDConv T (oneDIndicator A) := by
  classical
  intro z
  obtain ⟨t₀, ht₀, huniq⟩ := tiles_iff_unique_tile.mp hTile z
  calc
    (∑ t ∈ T, oneDValue (oneDIndicator A (z - t))) =
        oneDValue (oneDIndicator A (z - t₀.val)) := by
      apply Finset.sum_eq_single t₀.val
      · intro t ht hne
        have hnot : z - t ∉ A := by
          intro hmem
          have he := congrArg Subtype.val (huniq (⟨t, ht⟩ : ↥T) hmem)
          exact hne he
        simp [oneDIndicator, hnot, oneDValue]
      · intro hnot
        exact (hnot t₀.property).elim
    _ = 1 := by simp [oneDIndicator, ht₀, oneDValue]

theorem oneD_right_recurrence {T : Finset ℤ} {a : ℤ → Fin 2}
    (lo : ℤ) (M : ℕ) (hlo : lo ∈ T) (hConv : OneDConv T a) (n : ℤ) :
    oneDValue (a (n + (M : ℤ))) =
      1 - ∑ t ∈ T.erase lo, oneDValue (a (n + (M : ℤ) + lo - t)) := by
  have hs := Finset.sum_erase_add T
    (fun t => oneDValue (a (n + (M : ℤ) + lo - t))) hlo
  rw [hConv (n + (M : ℤ) + lo)] at hs
  have harg : n + (M : ℤ) + lo - lo = n + (M : ℤ) := by omega
  rw [harg] at hs
  omega

theorem oneD_left_recurrence {T : Finset ℤ} {a : ℤ → Fin 2}
    (lo : ℤ) (M : ℕ) (hhi : lo + (M : ℤ) ∈ T)
    (hConv : OneDConv T a) (n : ℤ) :
    oneDValue (a (n - 1)) =
      1 - ∑ t ∈ T.erase (lo + (M : ℤ)),
        oneDValue (a (n + (M : ℤ) + lo - 1 - t)) := by
  have hs := Finset.sum_erase_add T
    (fun t => oneDValue (a (n + (M : ℤ) + lo - 1 - t))) hhi
  rw [hConv (n + (M : ℤ) + lo - 1)] at hs
  have harg : n + (M : ℤ) + lo - 1 - (lo + (M : ℤ)) = n - 1 := by omega
  rw [harg] at hs
  omega

theorem oneD_block_eq_add_one {T : Finset ℤ} {a : ℤ → Fin 2}
    {lo : ℤ} {M : ℕ} (hlo : lo ∈ T)
    (hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ))
    (hConv : OneDConv T a) {n m : ℤ} (hBlock : OneDBlockEq M a n m) :
    OneDBlockEq M a (n + 1) (m + 1) := by
  have hsum :
      (∑ t ∈ T.erase lo, oneDValue (a (n + (M : ℤ) + lo - t))) =
      ∑ t ∈ T.erase lo, oneDValue (a (m + (M : ℤ) + lo - t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp ht
    obtain ⟨hlo', hhi'⟩ := hBounds t hmem
    have he := hBlock ((M : ℤ) + lo - t) (by omega) (by omega)
    have hn : n + ((M : ℤ) + lo - t) = n + (M : ℤ) + lo - t := by omega
    have hm : m + ((M : ℤ) + lo - t) = m + (M : ℤ) + lo - t := by omega
    rw [hn, hm] at he
    exact congrArg oneDValue he
  have hnext : a (n + (M : ℤ)) = a (m + (M : ℤ)) := by
    apply oneDValue_injective
    rw [oneD_right_recurrence lo M hlo hConv n,
      oneD_right_recurrence lo M hlo hConv m, hsum]
  intro i hi hiM
  by_cases hinner : i + 1 < (M : ℤ)
  · have he := hBlock (i + 1) (by omega) hinner
    have hn : n + (i + 1) = n + 1 + i := by omega
    have hm : m + (i + 1) = m + 1 + i := by omega
    simpa only [hn, hm] using he
  · have hieq : i + 1 = (M : ℤ) := by omega
    have hn : n + 1 + i = n + (M : ℤ) := by omega
    have hm : m + 1 + i = m + (M : ℤ) := by omega
    simpa only [hn, hm] using hnext

theorem oneD_block_eq_sub_one {T : Finset ℤ} {a : ℤ → Fin 2}
    {lo : ℤ} {M : ℕ} (hhi : lo + (M : ℤ) ∈ T)
    (hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ))
    (hConv : OneDConv T a) {n m : ℤ} (hBlock : OneDBlockEq M a n m) :
    OneDBlockEq M a (n - 1) (m - 1) := by
  have hsum :
      (∑ t ∈ T.erase (lo + (M : ℤ)),
        oneDValue (a (n + (M : ℤ) + lo - 1 - t))) =
      ∑ t ∈ T.erase (lo + (M : ℤ)),
        oneDValue (a (m + (M : ℤ) + lo - 1 - t)) := by
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp ht
    obtain ⟨hlo', hhi'⟩ := hBounds t hmem
    have he := hBlock ((M : ℤ) + lo - 1 - t) (by omega) (by omega)
    have hn : n + ((M : ℤ) + lo - 1 - t) = n + (M : ℤ) + lo - 1 - t := by omega
    have hm : m + ((M : ℤ) + lo - 1 - t) = m + (M : ℤ) + lo - 1 - t := by omega
    rw [hn, hm] at he
    exact congrArg oneDValue he
  have hprev : a (n - 1) = a (m - 1) := by
    apply oneDValue_injective
    rw [oneD_left_recurrence lo M hhi hConv n,
      oneD_left_recurrence lo M hhi hConv m, hsum]
  intro i hi hiM
  by_cases hiz : i = 0
  · simpa only [hiz, add_zero] using hprev
  · have he := hBlock (i - 1) (by omega) (by omega)
    have hn : n + (i - 1) = n - 1 + i := by omega
    have hm : m + (i - 1) = m - 1 + i := by omega
    simpa only [hn, hm] using he

theorem oneD_block_eq_add_int {T : Finset ℤ} {a : ℤ → Fin 2}
    {lo : ℤ} {M : ℕ} (hlo : lo ∈ T) (hhi : lo + (M : ℤ) ∈ T)
    (hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ))
    (hConv : OneDConv T a) {n m : ℤ} (hBlock : OneDBlockEq M a n m) :
    ∀ z : ℤ, OneDBlockEq M a (n + z) (m + z) := by
  have hpos : ∀ r : ℕ, OneDBlockEq M a (n + (r : ℤ)) (m + (r : ℤ)) := by
    intro r
    induction r with
    | zero => simpa only [Nat.cast_zero, add_zero] using hBlock
    | succ r ih =>
        have he := oneD_block_eq_add_one hlo hBounds hConv ih
        simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, add_assoc] using he
  have hneg : ∀ r : ℕ, OneDBlockEq M a (n - (r : ℤ)) (m - (r : ℤ)) := by
    intro r
    induction r with
    | zero => simpa only [Nat.cast_zero, sub_zero] using hBlock
    | succ r ih =>
        have he := oneD_block_eq_sub_one hhi hBounds hConv ih
        simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one, sub_sub] using he
  intro z
  cases z with
  | ofNat r => exact hpos r
  | negSucc r =>
      have hn : n + Int.negSucc r = n - ((r + 1 : ℕ) : ℤ) := by omega
      have hm : m + Int.negSucc r = m - ((r + 1 : ℕ) : ℤ) := by omega
      rw [hn, hm]
      exact hneg (r + 1)

theorem oneD_period_of_conv
    (T : Finset ℤ) (a : ℤ → Fin 2) (lo : ℤ) (M : ℕ) (hM : 0 < M)
    (hlo : lo ∈ T) (hhi : lo + (M : ℤ) ∈ T)
    (hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ))
    (hConv : OneDConv T a) :
    ∃ p : ℕ, 0 < p ∧ p ≤ 2 ^ M ∧ Function.Periodic a (p : ℤ) := by
  classical
  have hcard : Fintype.card (Fin M → Fin 2) < Fintype.card (Fin (2 ^ M + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    omega
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (2 ^ M + 1) => oneDWindow M a (i.val : ℤ)) hcard
  have derive : ∀ i j : Fin (2 ^ M + 1), i.val < j.val →
      oneDWindow M a (i.val : ℤ) = oneDWindow M a (j.val : ℤ) →
      ∃ p : ℕ, 0 < p ∧ p ≤ 2 ^ M ∧ Function.Periodic a (p : ℤ) := by
    intro i j hij hstate
    refine ⟨j.val - i.val, by omega, by have := j.isLt; omega, ?_⟩
    intro x
    have hBlock := oneDBlockEq_of_window_eq hstate
    have hshift := oneD_block_eq_add_int hlo hhi hBounds hConv hBlock (x - (i.val : ℤ))
    have he := hshift 0 (by omega) (by omega)
    have hn : (i.val : ℤ) + (x - (i.val : ℤ)) + 0 = x := by omega
    have hm : (j.val : ℤ) + (x - (i.val : ℤ)) + 0 =
        x + ((j.val - i.val : ℕ) : ℤ) := by omega
    rw [hn, hm] at he
    exact he.symm
  have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hneval with hij | hji
  · exact derive i j hij heq
  · exact derive j i hji heq.symm

theorem periodic_of_tiles_int
    (T : Finset ℤ) (hT : T.Nonempty) (A : Set ℤ) (hTile : Tiles T A) :
    ∃ p : ℕ, 0 < p ∧ Period A (p : ℤ) := by
  classical
  let lo : ℤ := T.min' hT
  let hi : ℤ := T.max' hT
  have hlo : lo ∈ T := T.min'_mem hT
  have hhi : hi ∈ T := T.max'_mem hT
  have hlohi : lo ≤ hi := T.min'_le hi hhi
  let M : ℕ := (hi - lo).toNat
  have hMcast : (M : ℤ) = hi - lo := Int.toNat_of_nonneg (by omega)
  have hmax : lo + (M : ℤ) ∈ T := by
    have he : lo + (M : ℤ) = hi := by omega
    rw [he]
    exact hhi
  have hBounds : ∀ t ∈ T, lo ≤ t ∧ t ≤ lo + (M : ℤ) := by
    intro t ht
    have hl : lo ≤ t := T.min'_le t ht
    have hr : t ≤ hi := T.le_max' t ht
    constructor <;> omega
  by_cases hzero : M = 0
  · have hall : ∀ z : ℤ, z ∈ A := by
      intro z
      obtain ⟨t, ht, _⟩ := tiles_iff_unique_tile.mp hTile (lo + z)
      obtain ⟨hl, hr⟩ := hBounds t.val t.property
      have hteq : t.val = lo := by omega
      simpa only [hteq, add_sub_cancel_left] using ht
    refine ⟨1, by omega, ?_⟩
    intro z
    exact ⟨fun _ => hall z, fun _ => hall (z + (1 : ℤ))⟩
  · have hM : 0 < M := Nat.pos_of_ne_zero hzero
    obtain ⟨p, hp, _, hperiod⟩ := oneD_period_of_conv T (oneDIndicator A) lo M hM
      hlo hmax hBounds (oneDConv_of_tiles hTile)
    refine ⟨p, hp, ?_⟩
    intro z
    have he := hperiod z
    constructor
    · intro hz
      by_contra hn
      simp [oneDIndicator, hz, hn] at he
    · intro hz
      by_contra hn
      simp [oneDIndicator, hz, hn] at he

theorem fullyPeriodic_of_nat_period
    (A : Set ℤ) (p : ℕ) (hp : 0 < p) (hPeriod : Period A (p : ℤ)) :
    FullyPeriodic A := by
  refine ⟨AddSubgroup.zmultiples (p : ℤ), ?_, ?_⟩
  · refine ⟨?_⟩
    simpa only [Int.index_zmultiples, Int.natAbs_natCast] using (Nat.ne_of_gt hp)
  · intro v hv
    obtain ⟨k, rfl⟩ := Int.mem_zmultiples_iff.mp hv
    have hFun : Function.Periodic (fun z : ℤ => z ∈ A) (p : ℤ) :=
      fun z => propext (hPeriod z)
    intro z
    have he : (z + (p : ℤ) * k ∈ A) = (z ∈ A) := by
      simpa only [Int.cast_id, id_def, mul_comm] using hFun.int_mul k z
    exact ⟨fun hz => Eq.mp he hz, fun hz => Eq.mpr he hz⟩

theorem fullyPeriodic_of_tiles_int
    (T : Finset ℤ) (hT : T.Nonempty) (A : Set ℤ) (hTile : Tiles T A) :
    FullyPeriodic A := by
  obtain ⟨p, hp, hPeriod⟩ := periodic_of_tiles_int T hT A hTile
  exact fullyPeriodic_of_nat_period A p hp hPeriod

theorem exists_fullyPeriodic_tiling_int
    (T : Finset ℤ) (hT : T.Nonempty) (hTile : ∃ A : Set ℤ, Tiles T A) :
    ∃ A : Set ℤ, Tiles T A ∧ FullyPeriodic A := by
  obtain ⟨A, hA⟩ := hTile
  exact ⟨A, hA, fullyPeriodic_of_tiles_int T hT A hA⟩

end PeriodicTilingThree

end

end OAI
