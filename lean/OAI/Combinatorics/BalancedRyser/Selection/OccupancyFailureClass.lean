import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Profiles.Profile

namespace OAI

noncomputable section

namespace Balanced
open scoped _root_.Balanced

open Filter MeasureTheory
open scoped Topology

universe u

def survivingLineOccupancy {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (D : Finset (Line F)) (l : Line F) : ℝ :=
  ((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)

def occupancyFailureClass (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ)
    (high : Bool) : ProfileClass.{u} :=
  fun F _ _ _ D C =>
    IsProfilePair k D C ∧
    a * (Fintype.card F : ℝ) ≤ (C.card : ℝ) ∧
    deletionMultiplicityTV k D ≤ ε (Fintype.card F) ∧
    ∀ l ∈ C, if high then Real.exp (-(k : ℝ)) + lam ≤ survivingLineOccupancy D l
      else survivingLineOccupancy D l ≤ Real.exp (-(k : ℝ)) - lam

theorem occupancyFailureClass_valid (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool) :
    ProfileClassValid k (occupancyFailureClass.{u} k a lam ε high) := by
  intro F _ _ _ D C h
  exact h.1

theorem occupancyFailureClass_sizeGap (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool) :
    ProfileClassSizeGap a (occupancyFailureClass.{u} k a lam ε high) := by
  intro F _ _ _ D C h
  exact Or.inr h.2.1

theorem occupancyFailureClass_limit_density_lower
    (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool)
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, occupancyFailureClass k a lam ε high (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) : a ≤ c := by
  apply ge_of_tendsto hlim.1
  apply Eventually.of_forall
  intro n
  exact (le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F n))).2 (hclass n).2.1

theorem occupancyFailureClass_limit_density_le_one
    (k : ℕ) (a lam : ℝ) (ε : ℕ → ℝ) (high : Bool)
    {F : ℕ → Type u} [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (D C : ∀ n, Finset (Line (F n)))
    (hclass : ∀ n, occupancyFailureClass k a lam ε high (F n) (D n) (C n))
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) : c ≤ 1 := by
  apply le_of_tendsto hlim.1
  apply Eventually.of_forall
  intro n
  apply (div_le_one (by exact_mod_cast Fintype.card_pos (α := F n))).2
  exact_mod_cast (hclass n).1.2.2

theorem exists_common_sign_subset {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) (μ lam : ℝ) (m : ℕ)
    (hsize : 2 * m ≤ S.card) (hdev : ∀ x ∈ S, lam ≤ |f x - μ|) :
    ∃ high : Bool, ∃ C : Finset α, C ⊆ S ∧ C.card = m ∧
      ∀ x ∈ C, if high then μ + lam ≤ f x else f x ≤ μ - lam := by
  classical
  let A := S.filter (fun x => μ + lam ≤ f x)
  by_cases hA : m ≤ A.card
  · obtain ⟨C, hC, hcard⟩ := Finset.exists_subset_card_eq hA
    refine ⟨true, C, fun x hx => (Finset.mem_filter.mp (hC hx)).1, hcard, ?_⟩
    intro x hx
    exact (Finset.mem_filter.mp (hC hx)).2
  · let B := S.filter (fun x => ¬ (μ + lam ≤ f x))
    have hpart : A.card + B.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (fun x => μ + lam ≤ f x)
    have hB : m ≤ B.card := by omega
    obtain ⟨C, hC, hcard⟩ := Finset.exists_subset_card_eq hB
    refine ⟨false, C, fun x hx => (Finset.mem_filter.mp (hC hx)).1, hcard, ?_⟩
    intro x hx
    obtain ⟨hxS, hxA⟩ := Finset.mem_filter.mp (hC hx)
    have hd := hdev x hxS
    rcases le_abs.mp hd with hpos | hneg
    · exact False.elim (hxA (by linarith))
    · change f x ≤ μ - lam
      linarith

theorem occupancyFailureClass_witness_of_exceptional
    (k : ℕ) {η lam : ℝ} (_hη : 0 ≤ η) (hηone : η ≤ 1)
    (ε : ℕ → ℝ) (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (D : DeletionSet F k)
    (hlarge : 4 ≤ η * (Fintype.card F : ℝ))
    (hbad : η * (Fintype.card F : ℝ) ≤
      ((exceptionalOccupancyLines k lam D.val).card : ℝ))
    (hTV : deletionMultiplicityTV k D.val ≤ ε (Fintype.card F)) :
    ∃ high : Bool, ∃ C : Finset (Line F),
      occupancyFailureClass k (η / 4) lam ε high F D.val C := by
  classical
  let q : ℝ := Fintype.card F
  let m : ℕ := ⌊η * q / 2⌋₊
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hmle : (m : ℝ) ≤ η * q / 2 := Nat.floor_le (by positivity)
  have hmlt : η * q / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2m : 2 * m ≤ (exceptionalOccupancyLines k lam D.val).card := by
    have hh : (2 : ℝ) * m ≤ ((exceptionalOccupancyLines k lam D.val).card : ℝ) := by
      change η * q ≤ _ at hbad
      linarith
    exact_mod_cast hh
  have hdev : ∀ l ∈ exceptionalOccupancyLines k lam D.val,
      lam ≤ |survivingLineOccupancy D.val l - Real.exp (-(k : ℝ))| := by
    intro l hl
    exact (Finset.mem_filter.mp hl).2.2
  obtain ⟨high, C, hC, hcard, hsign⟩ := exists_common_sign_subset
    (exceptionalOccupancyLines k lam D.val) (survivingLineOccupancy D.val)
    (Real.exp (-(k : ℝ))) lam m h2m hdev
  refine ⟨high, C, ⟨D.property, ?_, ?_⟩, ?_, hTV, hsign⟩
  · apply Finset.disjoint_left.mpr
    intro l hlD hlC
    exact (Finset.mem_filter.mp (hC hlC)).2.1 hlD
  · rw [hcard]
    have hh : (m : ℝ) ≤ q := by nlinarith [mul_le_mul_of_nonneg_right hηone hq]
    change (m : ℝ) ≤ (Fintype.card F : ℝ) at hh
    exact_mod_cast hh
  · rw [hcard]
    change (η / 4) * q ≤ (m : ℝ)
    change 4 ≤ η * q at hlarge
    nlinarith

end Balanced

end

end OAI
