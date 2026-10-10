import Mathlib
import OAI.Combinatorics.UniformKServer.ConditionalRanks
import OAI.Combinatorics.UniformKServer.CoarseBridge

namespace OAI

                                
section

/-! The actual rank processes of a finite hidden count law on its positive
support. No martingale or allocation estimate is part of the data. -/
noncomputable section
namespace UniformKServer.StarRanks
open Finset ConditionalLaw RankData
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

structure Data (Ω ι : Type*) [Fintype Ω] [Fintype ι] (k : ℕ) where
  weight : Ω → ℝ
  positive : ∀ ω, 0 < weight ω
  total : ∑ ω, weight ω = 1
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  count : ℕ → Ω → ι → ℕ
  bound : ∀ t ω, ∑ i, count t ω i ≤ k

def input (d : Data Ω ι k) (i : ι) (j : Fin k) : RankTracking.Input Ω :=
  ConditionalRank.input d.weight (fun ω => le_of_lt (d.positive ω)) d.total
    d.filtration d.refines (fun t ω => d.count t ω i) j

def parentInput (d : Data Ω ι k) (j : Fin k) : RankTracking.Input Ω :=
  ConditionalRank.input d.weight (fun ω => le_of_lt (d.positive ω)) d.total
    d.filtration d.refines (fun t ω => ∑ i, d.count t ω i) j

def held (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  CoarseData.heldSize (input d i) t ω

def flags (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) (j : Fin k) : Bool :=
  RankData.core (input d i j) t ω

def coreInput (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : ℝ :=
  SyntheticCore.input (fun j => (input d i j).posterior t ω) (flags d t ω i)

theorem mass_pos (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    0 < ConditionalLaw.mass d.weight (d.filtration t) ω :=
  lt_of_lt_of_le (d.positive ω) (weight_le_mass (fun v => le_of_lt (d.positive v)) _ _)

theorem child_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : d.count t ω i ≤ k :=
  (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans (d.bound t ω)

theorem size_sum (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    (∑ i, totalSize (fun j => (input d i j).posterior t ω)) ≤
      totalSize (fun j => (parentInput d j).posterior t ω) :=
  ConditionalRanks.size_superadditivity d.weight (fun v => le_of_lt (d.positive v))
    (d.filtration t) ω (ne_of_gt (mass_pos d t ω)) (d.count t) k (d.bound t)

theorem rank_sum (d : Data Ω ι k) (t : ℕ) (ω : Ω) {β : ℝ}
    (hβ : RankFunctions.allowed β) :
    (∑ i, totalRank β (fun j => (input d i j).posterior t ω)) ≤
      totalRank β (fun j => (parentInput d j).posterior t ω) :=
  ConditionalRanks.rank_superadditivity d.weight (fun v => le_of_lt (d.positive v))
    (d.filtration t) ω (ne_of_gt (mass_pos d t ω)) (d.count t) k (d.bound t) β hβ

theorem parent_size_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    totalSize (fun j => (parentInput d j).posterior t ω) ≤ k := by
  have h := ConditionalRanks.size_le_mean d.weight (fun v => le_of_lt (d.positive v))
    (d.filtration t) ω (ne_of_gt (mass_pos d t ω)) (fun v => ∑ i, d.count t v i) k (d.bound t)
  apply h.trans
  calc
    _ ≤ ∑ v, kernel d.weight (d.filtration t) ω v * (k:ℝ) := by
      apply sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (by change ((∑ i, d.count t v i : ℕ):ℝ) ≤ (k:ℝ); exact_mod_cast d.bound t v)
        (kernel_nonneg (fun v => le_of_lt (d.positive v)) _ _ _)
    _ = k := by
      rw [←sum_mul,ConditionalRanks.normalized_kernel _ _ _ (ne_of_gt (mass_pos d t ω)),one_mul]

theorem held_nonneg (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) : 0 ≤ held d t ω i :=
  CoarseData.heldSize_nonneg _ _ _

theorem held_sum (d : Data Ω ι k) (t : ℕ) (ω : Ω) :
    (∑ i, held d t ω i) ≤ 2*k := by
  have h : (∑ i, held d t ω i) ≤
      (11/10)*(∑ i, totalSize (fun j => (input d i j).posterior t ω)) := by
    rw [mul_sum]
    exact sum_le_sum fun i _ => CoarseBridge.held_bound _ _ _
  have hs := size_sum d t ω
  have hp := parent_size_bound d t ω
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem held_min (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι)
    (hp : 0 < held d t ω i) : (9/100000:ℝ) ≤ held d t ω i :=
  CoarseBridge.held_min _ _ _ hp

theorem zero_flags (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι)
    (hz : held d t ω i=0) (j : Fin k) : flags d t ω i j=false :=
  CoarseBridge.held_zero_flags _ _ _ hz j

theorem core_bound (d : Data Ω ι k) (t : ℕ) (ω : Ω) (i : ι) :
    coreInput d t ω i ≤ 40*held d t ω i :=
  CoarseBridge.core_input_bound _ _ _

end UniformKServer.StarRanks

end


end

end OAI
