import OAI.LinearAlgebra.MatrixMultiplication.Recovery.Staggering
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.FiniteSchedule

open Staggering

def lotTick {K : ℕ} (j : Fin K) (stage : Fin 3) : ℕ := j.val + stage.val

theorem lotTick_lt {K : ℕ} (j : Fin K) (stage : Fin 3) :
    lotTick j stage < K + 2 := by
  have hj := j.isLt
  have hs := stage.isLt
  dsimp [lotTick]
  omega

def stageActive (K tick : ℕ) (stage : Fin 3) : Prop :=
  stage.val ≤ tick ∧ tick < K + stage.val

instance (K tick : ℕ) (stage : Fin 3) : Decidable (stageActive K tick stage) :=
  inferInstanceAs (Decidable (stage.val ≤ tick ∧ tick < K + stage.val))

theorem stageActive_iff_unique_lot (K tick : ℕ) (stage : Fin 3) :
    stageActive K tick stage ↔ ∃! j : Fin K, lotTick j stage = tick := by
  constructor
  · rintro ⟨hle, hlt⟩
    refine ⟨⟨tick - stage.val, by omega⟩, ?_, ?_⟩
    · dsimp [lotTick]
      omega
    · intro j hj
      apply Fin.ext
      dsimp [lotTick] at hj ⊢
      omega
  · rintro ⟨j, hj, _⟩
    have hjlt := j.isLt
    dsimp [stageActive, lotTick] at *
    omega

theorem lot_active_at_its_tick {K : ℕ} (j : Fin K) (stage : Fin 3) :
    stageActive K (lotTick j stage) stage := by
  have hj := j.isLt
  dsimp [stageActive, lotTick]
  omega

def tickCapacity (K : ℕ) (a b c : Capacity) (tick : ℕ) : Capacity := fun i =>
  (if stageActive K tick 0 then a i else 0) +
    (if stageActive K tick 1 then b i else 0) +
    (if stageActive K tick 2 then c i else 0)

theorem tickCapacity_first (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c 0 = a := by
  funext i
  have h0 : 0 < K := by omega
  simp [tickCapacity, stageActive, h0]

theorem tickCapacity_second (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c 1 = fun i => a i + b i := by
  funext i
  have h1 : 1 < K := by omega
  have h2 : 1 < K + 1 := by omega
  simp [tickCapacity, stageActive, h1, h2]

theorem tickCapacity_interior (K tick : ℕ) (ht : 2 ≤ tick) (htK : tick < K)
    (a b c : Capacity) :
    tickCapacity K a b c tick = fun i => a i + b i + c i := by
  funext i
  have h1 : 1 ≤ tick := by omega
  have ht1 : tick < K + 1 := by omega
  have ht2 : tick < K + 2 := by omega
  simp [tickCapacity, stageActive, ht, htK, h1, ht1, ht2]

theorem tickCapacity_penultimate (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c K = fun i => b i + c i := by
  funext i
  have h1 : 1 ≤ K := by omega
  simp [tickCapacity, stageActive, hK, h1]

theorem tickCapacity_last (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) :
    tickCapacity K a b c (K + 1) = c := by
  funext i
  have h1 : 2 ≤ K + 1 := by omega
  simp [tickCapacity, stageActive, h1]

theorem sum_tick_minima (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) (full : ℝ)
    (hfull : ∀ i, a i + b i + c i = full) :
    (∑ tick ∈ Finset.range (K + 2), minCapacity (tickCapacity K a b c tick)) =
      (K - 2 : ℕ) * full + minCapacity a + minCapacity (fun i => a i + b i) +
        minCapacity (fun i => b i + c i) + minCapacity c := by
  let f : ℕ → ℝ := fun tick => minCapacity (tickCapacity K a b c tick)
  have hhead : ∑ tick ∈ Finset.range 2, f tick =
      minCapacity a + minCapacity (fun i => a i + b i) := by
    simp [f, Finset.sum_range_succ, tickCapacity_first K hK,
      tickCapacity_second K hK]
  have hinterior : (∑ tick ∈ Finset.range (K - 2), f (2 + tick)) =
      (K - 2 : ℕ) * full := by
    calc
      _ = ∑ _tick ∈ Finset.range (K - 2), full := by
        apply Finset.sum_congr rfl
        intro tick htick
        have hlt := Finset.mem_range.mp htick
        dsimp [f]
        rw [tickCapacity_interior K (2 + tick) (by omega) (by omega)]
        simp [minCapacity, hfull]
      _ = _ := by simp
  have htail : (∑ tick ∈ Finset.range 2, f (K + tick)) =
      minCapacity (fun i => b i + c i) + minCapacity c := by
    simp [f, Finset.sum_range_succ, tickCapacity_penultimate K hK,
      tickCapacity_last K hK]
  change (∑ tick ∈ Finset.range (K + 2), f tick) = _
  rw [Finset.sum_range_add f K 2, htail]
  have hsplit : (∑ tick ∈ Finset.range K, f tick) =
      (∑ tick ∈ Finset.range 2, f tick) +
        ∑ tick ∈ Finset.range (K - 2), f (2 + tick) := by
    have hKsum : 2 + (K - 2) = K := by omega
    simpa only [hKsum] using Finset.sum_range_add f 2 (K - 2)
  rw [hsplit, hhead, hinterior]
  ring

theorem finite_schedule_yield (K : ℕ) (hK : 2 ≤ K) (a b c : Capacity) (full : ℝ)
    (hfull : ∀ i, a i + b i + c i = full) :
    (∑ tick ∈ Finset.range (K + 2), minCapacity (tickCapacity K a b c tick)) =
      (K : ℝ) * full - boundaryDeficit a b c full := by
  rw [sum_tick_minima K hK a b c full hfull]
  exact Staggering.finite_schedule_yield a b c full K hK

theorem fixed_lot_boundary_limit {Y beta w S R : ℝ}
    (hfixed : ∀ K : ℕ, 2 ≤ K → Y - beta / (K : ℝ) + w * S / 3 ≤ R) :
    Y + w * S / 3 ≤ R := by
  by_contra hnot
  have hgap : 0 < Y + w * S / 3 - R := by linarith
  obtain ⟨K, hK⟩ := exists_nat_gt (max (beta / (Y + w * S / 3 - R)) (2 : ℝ))
  have hKtwo : (2 : ℝ) < (K : ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
  have hKnat : 2 ≤ K := Nat.ofNat_le_cast.mp hKtwo.le
  have hKpos : (0 : ℝ) < (K : ℝ) := by linarith
  have hsmall : beta / (K : ℝ) < Y + w * S / 3 - R := by
    apply (div_lt_iff₀ hKpos).2
    have hquot : beta / (Y + w * S / 3 - R) < (K : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hK
    simpa only [mul_comm] using (div_lt_iff₀ hgap).1 hquot
  have hbound := hfixed K hKnat
  linarith

end MatrixMultiplication.FiniteSchedule

end

end OAI
