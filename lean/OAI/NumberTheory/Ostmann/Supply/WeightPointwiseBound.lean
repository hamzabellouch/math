import OAI.NumberTheory.Ostmann.Supply.ContractingKernel
import OAI.NumberTheory.Ostmann.Supply.TruncatedWeight

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators

theorem card_retained_subsets_le {ι : Type*} (P : Finset ι) (K : ℕ) :
    (P.powerset.filter (fun s => s.card≤K)).card ≤ (K+1)*(P.card+1)^K := by
  classical
  have hsub : P.powerset.filter (fun s => s.card≤K) ⊆
      (Finset.range (K+1)).biUnion (fun j => P.powersetCard j) := by
    intro s hs
    obtain ⟨hsp,hcard⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_biUnion.mpr ⟨s.card,Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hsp,rfl⟩⟩
  calc
    _ ≤ ((Finset.range (K+1)).biUnion (fun j => P.powersetCard j)).card := Finset.card_le_card hsub
    _ ≤ ∑j∈Finset.range (K+1),(P.powersetCard j).card := Finset.card_biUnion_le
    _ ≤ ∑_j∈Finset.range (K+1),(P.card+1)^K := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.card_powersetCard]
      apply (Nat.choose_le_pow P.card j).trans
      have hjK : j≤K := by have := Finset.mem_range.mp hj; omega
      gcongr <;> omega
    _ = _ := by simp

theorem truncatedWeight_le_card_bound {ι : Type*} (P : Finset ι) (b : ι→ℝ) (K : ℕ)
    (hb : ∀i∈P,|b i|≤1) :
    truncatedWeight P b K ≤ (K+1:ℝ)^2*(P.card+1:ℝ)^(2*K) := by
  classical
  have hnorm : |truncatedSubsetSum P b K|≤((K+1)*(P.card+1)^K:ℕ) := by
    calc
      _ ≤ ∑s∈P.powerset.filter (fun s => s.card≤K),|∏i∈s,b i| :=
        by simpa only [truncatedSubsetSum,Real.norm_eq_abs] using
          (norm_sum_le (P.powerset.filter (fun s => s.card≤K)) (fun s => ∏i∈s,b i))
      _ ≤ ∑_s∈P.powerset.filter (fun s => s.card≤K),(1:ℝ) := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏_i∈s,(1:ℝ) := Finset.prod_le_prod₀ (fun i hi => abs_nonneg _)
            (fun i hi => hb i (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1 hi))
          _ = 1 := by simp
      _ = ((P.powerset.filter (fun s => s.card≤K)).card:ℝ) := by simp
      _ ≤ ((K+1)*(P.card+1)^K:ℕ) := by exact_mod_cast card_retained_subsets_le P K
  have hsq := pow_le_pow_left₀ (abs_nonneg (truncatedSubsetSum P b K)) hnorm 2
  unfold truncatedWeight
  rw [sq_abs] at hsq
  convert hsq using 1
  push_cast
  ring

theorem sparseKernel_pointwise_le_one {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (x : ZMod p) :
    |localKernel S sparseKernelScale x|≤1 := by
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr (NeZero.pos p)
  have hcard : ((largeSpectrum S).card:ℝ)≤p := by
    exact_mod_cast (show (largeSpectrum S).card≤p by
      simpa only [ZMod.card p] using Finset.card_le_univ (largeSpectrum S))
  apply (localKernel_norm_le S sparseKernelScale x).trans
  rw [abs_of_nonneg sparseKernelScale_nonneg]
  apply (div_le_iff₀ hp0).mpr
  calc
    _ ≤ 1*((largeSpectrum S).card:ℝ) :=
      mul_le_mul_of_nonneg_right sparseKernelScale_le_one (Nat.cast_nonneg _)
    _ ≤ _ := by simpa using hcard

theorem truncatedKernelWeight_pointwise_le {ι : Type*} (P : Finset ι)
    (p : ι→ℕ) [∀i,NeZero (p i)] (S : ∀i,Finset (ZMod (p i)))
    (x : ∀i,ZMod (p i)) (K : ℕ) :
    truncatedWeight P (fun i => localKernel (S i) sparseKernelScale (x i)) K ≤
      (K+1:ℝ)^2*(P.card+1:ℝ)^(2*K) :=
  truncatedWeight_le_card_bound P _ K (fun i _ => sparseKernel_pointwise_le_one (S i) (x i))

end Ostmann.Supply

end

end OAI
