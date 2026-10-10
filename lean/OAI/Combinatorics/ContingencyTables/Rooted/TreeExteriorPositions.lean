import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace OAI

/-! # The narrow exterior tree intervals contain fewer than 2 gamma b positions -/

namespace ContingencyTables.TreeExteriorPositions

open scoped Classical

private lemma positive_integer_positions {C : Type*} [Fintype C] (q : C → ℤ)
    (hq : Function.Injective q) (delta : ℝ) (hd : 0 < delta) :
    ((Finset.univ.filter (fun c => 0 < q c ∧ (q c:ℝ) < delta)).card:ℝ) ≤ delta := by
  let S := Finset.univ.filter (fun c => 0 < q c ∧ (q c:ℝ) < delta)
  have hm : Set.MapsTo (fun c => (q c).toNat) S (Finset.Ico 1 (Nat.ceil delta)) := by
    intro c hc
    have hh := (Finset.mem_filter.mp hc).2
    have hn : (0:ℤ) ≤ q c := hh.1.le
    have hcast : ((q c).toNat:ℝ)=(q c:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    apply Finset.mem_Ico.mpr
    constructor
    · have hv := Int.toNat_of_nonneg hn
      have hpos : 0 < q c := hh.1
      have hcast : (1:ℤ) ≤ ((q c).toNat:ℤ) := by rw [hv]; omega
      exact_mod_cast hcast
    · have hhR : ((q c).toNat:ℝ) < (Nat.ceil delta:ℝ) := by rw [hcast]; exact hh.2.trans_le (Nat.le_ceil delta)
      exact_mod_cast hhR
  have hi : (S:Set C).InjOn (fun c => (q c).toNat) := by
    intro c hc c' hc' he
    apply hq
    have hh := (Finset.mem_filter.mp hc).2.1.le
    have hh' := (Finset.mem_filter.mp hc').2.1.le
    have h := congrArg (fun n : ℕ => (n:ℤ)) he
    simpa only [Int.toNat_of_nonneg hh,Int.toNat_of_nonneg hh'] using h
  have hc := Finset.card_le_card_of_injOn (fun c => (q c).toNat) hm hi
  rw [Nat.card_Ico] at hc
  have hceil : 1 ≤ Nat.ceil delta := Nat.one_le_ceil_iff.mpr hd
  have hceilR : ((Nat.ceil delta-1:ℕ):ℝ) ≤ delta := by
    rw [Nat.cast_sub hceil]
    have hh := Nat.ceil_lt_add_one hd.le
    push_cast
    linarith
  exact (by exact_mod_cast hc : (S.card:ℝ) ≤ (Nat.ceil delta-1:ℕ)).trans hceilR

noncomputable def positions (ell : ℤ) (b U : ℕ) (delta : ℝ) : Finset (Fin (U+1)) :=
  Finset.univ.filter (fun k =>
    ((ell+(k.val:ℤ)<0) ∧ -((ell+(k.val:ℤ):ℤ):ℝ)<delta) ∨
    (((b:ℤ)<ell+(k.val:ℤ)) ∧ (((ell+(k.val:ℤ):ℤ):ℝ)-b)<delta))

/-- Strict exterior distances avoid an additive rounding error even
when gamma*b is smaller than one. -/
theorem card_positions_le (ell : ℤ) (b U : ℕ) (delta : ℝ) (hd : 0 < delta) :
    ((positions ell b U delta).card:ℝ) ≤ 2*delta := by
  let L := Finset.univ.filter (fun k : Fin (U+1) =>
    0 < -(ell+(k.val:ℤ)) ∧ ((-(ell+(k.val:ℤ)):ℤ):ℝ)<delta)
  let R := Finset.univ.filter (fun k : Fin (U+1) =>
    0 < ell+(k.val:ℤ)-(b:ℤ) ∧ ((ell+(k.val:ℤ)-(b:ℤ):ℤ):ℝ)<delta)
  have hL : (L.card:ℝ) ≤ delta := by
    apply positive_integer_positions (fun k : Fin (U+1) => -(ell+(k.val:ℤ))) _ delta hd
    intro k k' he
    dsimp only at he
    apply Fin.ext
    have hh : (k.val:ℤ)=(k'.val:ℤ) := by omega
    exact_mod_cast hh
  have hR : (R.card:ℝ) ≤ delta := by
    apply positive_integer_positions (fun k : Fin (U+1) => ell+(k.val:ℤ)-(b:ℤ)) _ delta hd
    intro k k' he
    dsimp only at he
    apply Fin.ext
    have hh : (k.val:ℤ)=(k'.val:ℤ) := by omega
    exact_mod_cast hh
  have he : positions ell b U delta=L∪R := by
    ext k
    simp only [positions,L,R,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
      neg_pos,sub_pos,Int.cast_neg,Int.cast_sub,Int.cast_natCast]
  rw [he]
  have hc : ((L∪R).card:ℝ) ≤ (L.card:ℝ)+(R.card:ℝ) := by exact_mod_cast Finset.card_union_le L R
  linarith

end ContingencyTables.TreeExteriorPositions

end OAI
