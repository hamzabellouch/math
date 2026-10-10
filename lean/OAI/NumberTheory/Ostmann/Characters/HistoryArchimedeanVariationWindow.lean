import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Finset.Max
import OAI.NumberTheory.Ostmann.Characters.HistoryArchimedeanVariationBoundary

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sampled_convex_window (S : Set ℝ) (hS : Convex ℝ S) (Q a N : ℕ) :
    (∀ n : ℕ, n ≤ N → ((Q*n+a : ℕ) : ℝ) ∉ S) ∨
    ∃ lo hi : ℕ, lo ≤ hi ∧ hi ≤ N ∧
      ∀ n : ℕ, n ≤ N →
        (((Q*n+a : ℕ) : ℝ) ∈ S ↔ lo ≤ n ∧ n ≤ hi) := by
  classical
  let F := (Finset.range (N+1)).filter (fun n => ((Q*n+a : ℕ) : ℝ) ∈ S)
  have hmem (n : ℕ) : n ∈ F ↔ n ≤ N ∧ ((Q*n+a : ℕ) : ℝ) ∈ S := by
    simp only [F,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
  by_cases hn : F.Nonempty
  · let lo := F.min' hn
    let hi := F.max' hn
    have hlo : lo ∈ F := Finset.min'_mem F hn
    have hhi : hi ∈ F := Finset.max'_mem F hn
    have hlhi : lo ≤ hi := Finset.min'_le F hi hhi
    right
    refine ⟨lo,hi,hlhi,(hmem hi).mp hhi |>.1,?_⟩
    intro n hnN
    constructor
    · intro hx
      have hm := (hmem n).mpr ⟨hnN,hx⟩
      exact ⟨Finset.min'_le F n hm,Finset.le_max' F n hm⟩
    · intro hln
      have hl := (hmem lo).mp hlo |>.2
      have hh := (hmem hi).mp hhi |>.2
      apply hS.ordConnected.out hl hh
      constructor
      · exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left Q hln.1) a
      · exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left Q hln.2) a
  · left
    intro n hnN hx
    exact hn ⟨n,(hmem n).mpr ⟨hnN,hx⟩⟩

theorem progressionVariation_congr (N : ℕ) (f g : ℕ → ℂ)
    (hfg : ∀ n : ℕ, n ≤ N → f n=g n) :
    progressionVariation f N=progressionVariation g N := by
  unfold progressionVariation
  rw [hfg (N-1) (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_range.mp hn
  rw [hfg (n+1) (by omega),hfg n (by omega)]

def sampledSetWeight (S : Set ℝ) (Q a : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if ((Q*n+a : ℕ) : ℝ) ∈ S then f n else 0

theorem progressionVariation_const_mul (c : ℂ) (f : ℕ → ℂ) (N : ℕ) :
    progressionVariation (fun n => c*f n) N=‖c‖*progressionVariation f N := by
  unfold progressionVariation
  simp_rw [← mul_sub,norm_mul]
  rw [← Finset.mul_sum]
  ring

end Ostmann.Characters

end

end OAI
