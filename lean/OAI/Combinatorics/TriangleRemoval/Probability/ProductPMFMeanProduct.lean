import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.FiniteMean
import OAI.Combinatorics.TriangleRemoval.Probability.ProductPMF

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

theorem productPMF_mean_product {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V]
    (ρ : K → PMF V) (w : K → V → ℝ) :
    pmfMean (productPMF ρ) (fun ω => ∏ k, w k (ω k)) =
      ∏ k, pmfMean (ρ k) (w k) := by
  simp only [pmfMean, productPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k v => (ρ k v).toReal * w k v)).symm

theorem prospective_block_product {X K V : Type*} [Fintype X] [Fintype K]
    [DecidableEq K] [Fintype V] (π : PMF X) (ρ : K → PMF V)
    (F : X → ℝ) (w : K → X → V → ℝ) :
    pmfMean π (fun x => pmfMean (productPMF ρ)
      (fun ω => F x * ∏ k, w k x (ω k))) =
    pmfMean π (fun x => F x * ∏ k, pmfMean (ρ k) (w k x)) := by
  apply pmfMean_congr
  intro x _
  rw [pmfMean_const_mul, productPMF_mean_product]

theorem uniform_prospective_failure (N : ℕ) [NeZero N] (t : ℕ) (q : Fin N → ℝ) :
    pmfMean (PMF.uniformOfFintype (Fin N))
      (fun u => if u.val < t then 1 - q u else 1) =
      1 - (∑ u : Fin N, if u.val < t then q u else 0) / (N : ℝ) := by
  have hpt : (fun u : Fin N => if u.val < t then 1 - q u else 1) =
      (fun u : Fin N => 1 - (if u.val < t then q u else 0)) := by
    funext u
    split_ifs <;> simp
  rw [hpt, pmfMean_sub, pmfMean_const]
  congr 1
  simp only [pmfMean, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.card_fin, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem offpattern_product_bound {K : Type*} [DecidableEq K]
    (C S : Finset K) (hSC : S ⊆ C) (hS : S.card ≤ 2) (f : K → ℝ) (b : ℝ)
    (hf : ∀ k ∈ C, (7 / 8 : ℝ) ≤ f k) (hfull : ∏ k ∈ C, f k ≤ (9 / 8 : ℝ) * b) :
    ∏ k ∈ C \ S, f k ≤ 2 * b := by
  have hn : ∀ k ∈ C, 0 ≤ f k := fun k hk => le_trans (by norm_num) (hf k hk)
  have hp : (7 / 8 : ℝ) ^ S.card ≤ ∏ k ∈ S, f k := by
    simpa only [Finset.prod_const] using Finset.prod_le_prod₀
      (fun k (_ : k ∈ S) => by norm_num : ∀ k ∈ S, (0 : ℝ) ≤ 7 / 8)
      (fun k hk => hf k (hSC hk))
  have hp' : (49 / 64 : ℝ) ≤ ∏ k ∈ S, f k := by
    have hc : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
    rcases hc with h | h | h <;> rw [h] at hp <;> norm_num at hp ⊢ <;> linarith
  have ho : 0 ≤ ∏ k ∈ C \ S, f k := Finset.prod_nonneg
    (fun k hk => hn k (Finset.mem_sdiff.mp hk).1)
  have he : (∏ k ∈ S, f k) * (∏ k ∈ C \ S, f k) = ∏ k ∈ C, f k := by
    rw [mul_comm, Finset.prod_sdiff hSC]
  have hb : 0 ≤ b := by
    have hh : 0 ≤ ∏ k ∈ C, f k := Finset.prod_nonneg hn
    linarith
  have hm := mul_le_mul_of_nonneg_right hp' ho
  rw [he] at hm
  linarith

end SharpTerminalLeave

end

end OAI
