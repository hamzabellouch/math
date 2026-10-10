import Mathlib
import OAI.Combinatorics.UniformKServer.ConditionalRank
import OAI.Combinatorics.UniformKServer.RankData
import OAI.Combinatorics.UniformKServer.RankSuperadditivity

namespace OAI

                                       
section

/-! The source rank and size inequalities for the actual finite conditional
 law, with normalization proved on every positive-ConditionalLaw.mass history.  Null histories
 are not silently assigned a normalized law. -/
noncomputable section
namespace UniformKServer.ConditionalRanks
open Finset ConditionalLaw RankData
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def rankProbability (w : Ω → ℝ) (F : Setoid Ω) (N : Ω → ℕ) (ω : Ω) (j : ℕ) : ℝ :=
  posterior w F (fun v => ConditionalRank.indicator (N v) j) ω

theorem normalized_kernel (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω)
    (hm : ConditionalLaw.mass w F ω ≠ 0) : ∑ v, kernel w F ω v = 1 := by
  rw [kernel_sum,div_self hm]

def countInput (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v) (F : Setoid Ω) (ω : Ω)
    (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ι → ℕ) (k : ℕ) (hN : ∀ v, ∑ i, N v i ≤ k) :
    RankSuperadditivity.Input Ω ι k where
  μ := kernel w F ω
  nonneg := kernel_nonneg hw F ω
  total := normalized_kernel w F ω hm
  N := N
  bound := hN

theorem rankProbability_eq (w : Ω → ℝ) (F : Setoid Ω) (N : Ω → ℕ) (ω : Ω) (j : ℕ) :
    rankProbability w F N ω j = RankSuperadditivity.countRank (kernel w F ω) N j := rfl

theorem conditional_convex_superadditivity (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v)
    (F : Setoid Ω) (ω : Ω) (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ι → ℕ) (k : ℕ)
    (hN : ∀ v, ∑ i, N v i ≤ k) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc (0:ℝ) 1) f) (h1 : f 1=0) :
    (∑ i, ∑ j : Fin k, f (rankProbability w F (fun v => N v i) ω j)) ≤
      ∑ j : Fin k, f (rankProbability w F (fun v => ∑ i, N v i) ω j) := by
  have h := RankSuperadditivity.rank_superadditivity (countInput w hw F ω hm N k hN) f hf h1
  simp only [RankSuperadditivity.rankSum,countInput] at h
  simp_rw [← Fin.sum_univ_eq_sum_range] at h
  exact h

theorem size_superadditivity (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v)
    (F : Setoid Ω) (ω : Ω) (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ι → ℕ) (k : ℕ)
    (hN : ∀ v, ∑ i, N v i ≤ k) :
    (∑ i, totalSize (fun j : Fin k => rankProbability w F (fun v => N v i) ω j)) ≤
      totalSize (fun j : Fin k => rankProbability w F (fun v => ∑ i, N v i) ω j) := by
  exact conditional_convex_superadditivity w hw F ω hm N k hN sizeRank
    (sizeRank_convex.subset (Set.subset_univ _) (convex_Icc _ _)) sizeRank_one

theorem rank_superadditivity (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v)
    (F : Setoid Ω) (ω : Ω) (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ι → ℕ) (k : ℕ)
    (hN : ∀ v, ∑ i, N v i ≤ k) (β : ℝ) (hβ : RankFunctions.allowed β) :
    (∑ i, totalRank β (fun j : Fin k => rankProbability w F (fun v => N v i) ω j)) ≤
      totalRank β (fun j : Fin k => rankProbability w F (fun v => ∑ i, N v i) ω j) := by
  apply conditional_convex_superadditivity w hw F ω hm N k hN (RankFunctions.rank β)
    ((RankFunctions.rank_convex hβ).subset (Set.subset_univ _) (convex_Icc _ _))
  exact RankFunctions.rank_beyond (by norm_num [RankFunctions.sstar])

theorem sum_complements (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω)
    (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ℕ) (k : ℕ) (hN : ∀ v, N v ≤ k) :
    (∑ j : Fin k, (1-rankProbability w F N ω j)) = posterior w F (fun v => (N v:ℝ)) ω := by
  have hn := normalized_kernel w F ω hm
  calc
    _ = ∑ j ∈ range k, ∑ v, kernel w F ω v*(1-ConditionalRank.indicator (N v) j) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro j _
      simp only [rankProbability,posterior,mul_sub,mul_one,sum_sub_distrib,hn]
    _ = ∑ v, kernel w F ω v*(∑ j ∈ range k, (1-ConditionalRank.indicator (N v) j)) := by
      rw [sum_comm]
      simp only [mul_sum]
    _ = _ := by
      unfold posterior
      apply sum_congr rfl
      intro v _
      rw [sum_sub_distrib,ConditionalRank.indicator_sum (hN v)]
      simp

theorem size_le_mean (w : Ω → ℝ) (hw : ∀ v, 0 ≤ w v) (F : Setoid Ω) (ω : Ω)
    (hm : ConditionalLaw.mass w F ω ≠ 0) (N : Ω → ℕ) (k : ℕ) (hN : ∀ v, N v ≤ k) :
    totalSize (fun j : Fin k => rankProbability w F N ω j) ≤
      posterior w F (fun v => (N v:ℝ)) ω := by
  rw [←sum_complements w F ω hm N k hN]
  apply sum_le_sum
  intro j _
  exact sizeRank_le_complement ⟨posterior_nonneg hw
    (fun v => (ConditionalRank.indicator_range (N v) j).1) F ω,
    posterior_le_one hw (fun v => (ConditionalRank.indicator_range (N v) j).2) F ω⟩

theorem root_probability_zero (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) (k : ℕ) (j : Fin k) :
    rankProbability w F (fun _ => k) ω j = 0 := by
  unfold rankProbability posterior ConditionalRank.indicator
  simp only [ite_eq_right (Nat.not_le.mpr j.isLt),mul_zero,sum_const_zero]

theorem root_size_rank (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) (k : ℕ) (β : ℝ) :
    totalSize (fun j : Fin k => rankProbability w F (fun _ => k) ω j) = k ∧
    totalRank β (fun j : Fin k => rankProbability w F (fun _ => k) ω j) = k := by
  simp [totalSize,totalRank,root_probability_zero,sizeRank_zero,RankFunctions.rank_zero]

/-- The required first rank is zero on positive-weight atoms of the observed
 history; no assertion is inserted for impossible hidden configurations. -/
theorem required_probability_zero (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) (N : Ω → ℕ)
    (hN : ∀ v, F.r ω v → w v ≠ 0 → 1 ≤ N v) : rankProbability w F N ω 0 = 0 := by
  unfold rankProbability posterior
  apply sum_eq_zero
  intro v _
  by_cases hf : F.r ω v
  · by_cases hw : w v = 0
    · simp only [kernel,ite_eq_left hf,hw,zero_div,zero_mul]
    · have hn := hN v hf hw
      simp only [ConditionalRank.indicator,ite_eq_right (by omega : ¬N v ≤ 0),mul_zero]
  · simp only [kernel,ite_eq_right hf,zero_mul]

theorem required_rank_lower (w : Ω → ℝ) (F : Setoid Ω) (ω : Ω) (N : Ω → ℕ)
    (hN : ∀ v, F.r ω v → w v ≠ 0 → 1 ≤ N v) (k : ℕ) (hk : 0 < k)
    (β : ℝ) (hβ : RankFunctions.allowed β) :
    1 ≤ totalRank β (fun j : Fin k => rankProbability w F N ω j) := by
  have h := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin k))) =>
    RankFunctions.rank_nonneg (p:=rankProbability w F N ω j) hβ) (mem_univ (⟨0,hk⟩ : Fin k))
  simpa only [totalRank,required_probability_zero w F ω N hN,RankFunctions.rank_zero] using h

end UniformKServer.ConditionalRanks

end


end

end OAI
