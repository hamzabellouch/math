import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Profiles.Profile

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem exists_common_sign_subset_or {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℝ) (μ lam : ℝ) (m : ℕ)
    (hbad : ∀ x ∈ S, lam ≤ |f x - μ|) (hm : 2 * m ≤ S.card) :
    ∃ C ⊆ S, C.card = m ∧
      ((∀ x ∈ C, μ + lam ≤ f x) ∨ (∀ x ∈ C, f x ≤ μ - lam)) := by
  classical
  let H := S.filter (fun x => μ + lam ≤ f x)
  let L := S.filter (fun x => ¬ μ + lam ≤ f x)
  have hsum : H.card + L.card = S.card :=
    Finset.card_filter_add_card_filter_not _
  by_cases hH : m ≤ H.card
  · obtain ⟨C, hC, hcard⟩ := Finset.exists_subset_card_eq hH
    refine ⟨C, hC.trans (Finset.filter_subset _ _), hcard, Or.inl ?_⟩
    intro x hx
    exact (Finset.mem_filter.mp (hC hx)).2
  · have hL : m ≤ L.card := by omega
    obtain ⟨C, hC, hcard⟩ := Finset.exists_subset_card_eq hL
    refine ⟨C, hC.trans (Finset.filter_subset _ _), hcard, Or.inr ?_⟩
    intro x hx
    obtain ⟨hxS, hxH⟩ := Finset.mem_filter.mp (hC hx)
    rcases le_abs.mp (hbad x hxS) with h | h <;> linarith

theorem exceptionalOccupancyLines_common_sign
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (k : ℕ) (lam : ℝ) (D : Finset (Line F)) (m : ℕ)
    (hm : 2 * m ≤ (exceptionalOccupancyLines k lam D).card) :
    ∃ C : Finset (Line F), C.card = m ∧ Disjoint D C ∧
      ((∀ l ∈ C, Real.exp (-(k : ℝ)) + lam ≤
          ((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) ∨
       (∀ l ∈ C, ((linePoints l ∩ uncoveredBy D).card : ℝ) /
          (Fintype.card F : ℝ) ≤ Real.exp (-(k : ℝ)) - lam)) := by
  classical
  obtain ⟨C, hC, hcard, hsign⟩ := exists_common_sign_subset_or
    (exceptionalOccupancyLines k lam D)
    (fun l => ((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ))
    (Real.exp (-(k : ℝ))) lam m
    (fun l hl => (Finset.mem_filter.mp hl).2.2) hm
  refine ⟨C, hcard, ?_, hsign⟩
  rw [Finset.disjoint_left]
  intro l hlD hlC
  exact (Finset.mem_filter.mp (hC hlC)).2.1 hlD

theorem occupancy_floor_size_bounds (η : ℝ) (q : ℕ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : 4 ≤ η * (q : ℝ)) :
    (η / 4) * (q : ℝ) ≤ (⌊η * (q : ℝ) / 2⌋₊ : ℝ) ∧
      ⌊η * (q : ℝ) / 2⌋₊ ≤ q := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hx : 0 ≤ η * (q : ℝ) / 2 :=
    div_nonneg (mul_nonneg hη.le hq0) (by norm_num)
  have hlo := Nat.lt_floor_add_one (η * (q : ℝ) / 2)
  have hhi := Nat.floor_le hx
  refine ⟨by nlinarith, ?_⟩
  have hηq : η * (q : ℝ) ≤ q := by nlinarith
  have hle : (⌊η * (q : ℝ) / 2⌋₊ : ℝ) ≤ q := by nlinarith
  exact_mod_cast hle

theorem exists_order_for_occupancy_gap (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → 4 ≤ η * (q : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / η)
  refine ⟨N, ?_⟩
  intro q hq
  have hN' : 4 < (N : ℝ) * η := (div_lt_iff₀ hη).mp hN
  have hq' : (N : ℝ) ≤ q := by exact_mod_cast hq
  nlinarith

theorem exceptionalOccupancyLines_profile_witness
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (k : ℕ) (lam η : ℝ) (D : Finset (Line F))
    (hD : IsDeletionSet k D) (hη : 0 < η) (hη1 : η ≤ 1)
    (hq : 4 ≤ η * (Fintype.card F : ℝ))
    (hbad : η * (Fintype.card F : ℝ) ≤
      ((exceptionalOccupancyLines k lam D).card : ℝ)) :
    ∃ C : Finset (Line F), IsProfilePair k D C ∧
      (η / 4) * (Fintype.card F : ℝ) ≤ (C.card : ℝ) ∧
      ((∀ l ∈ C, Real.exp (-(k : ℝ)) + lam ≤
          ((linePoints l ∩ uncoveredBy D).card : ℝ) / (Fintype.card F : ℝ)) ∨
       (∀ l ∈ C, ((linePoints l ∩ uncoveredBy D).card : ℝ) /
          (Fintype.card F : ℝ) ≤ Real.exp (-(k : ℝ)) - lam)) := by
  have hx : 0 ≤ η * (Fintype.card F : ℝ) / 2 := by positivity
  have hfloor := Nat.floor_le hx
  have hm : 2 * ⌊η * (Fintype.card F : ℝ) / 2⌋₊ ≤
      (exceptionalOccupancyLines k lam D).card := by
    have h : (2 : ℝ) * (⌊η * (Fintype.card F : ℝ) / 2⌋₊ : ℝ) ≤
        (exceptionalOccupancyLines k lam D).card := by linarith
    exact_mod_cast h
  obtain ⟨C, hcard, hdisj, hsign⟩ :=
    exceptionalOccupancyLines_common_sign k lam D _ hm
  obtain ⟨hlo, hhi⟩ := occupancy_floor_size_bounds η (Fintype.card F) hη hη1 hq
  refine ⟨C, ⟨hD, hdisj, ?_⟩, ?_, hsign⟩
  · simpa only [hcard] using hhi
  · simpa only [hcard] using hlo

end Balanced

end OAI
