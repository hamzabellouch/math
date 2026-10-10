import OAI.Combinatorics.SquareDifference.EulerBudget

namespace OAI

section

open Finset Filter

open scoped BigOperators Topology

namespace SquareDifference

lemma exists_exceptional_threshold :
    ∃P : ℕ,64≤P ∧ ∀{p : ℕ} [Fact p.Prime],P≤p →
      max tupleMassThreshold tupleConditionalThreshold≤(p:ℝ) ∧
      tupleReflectionThreshold≤(p:ℝ) ∧ tupleEta p≤1/(p:ℝ)^4 := by
  have he := eventually_rpow_dominate tupleExceptionalConstant (-(81:ℝ)/16) (-4) (by norm_num)
  have ht : ∀ᶠ p : ℕ in atTop,
      max (max tupleMassThreshold tupleConditionalThreshold) tupleReflectionThreshold≤(p:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨P,hP⟩ := eventually_atTop.mp (he.and ht)
  refine ⟨max P 64,le_max_right _ _,?_⟩
  intro p _ hp
  have hp' := hP p ((le_max_left _ _).trans hp)
  have hm := (le_max_left _ _).trans hp'.2
  have hr := (le_max_right _ _).trans hp'.2
  refine ⟨hm,hr,?_⟩
  have hh := (tupleEta_le ((le_max_left _ _).trans hm)).trans hp'.1
  simpa only [Real.rpow_neg (Nat.cast_nonneg _),show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast,one_div] using hh

section Budget

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

lemma primeProduct_one_le {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (B : Finset J) : 1≤(∏j∈B,p j:ℝ) :=
  one_le_prod₀ (fun j _ => by exact_mod_cast (Fact.out : (p j).Prime).one_lt.le)

lemma tupleEta_le_one_of_fourth {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), Fact (Nat.Prime (p j))] (h : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4) (j : J) : tupleEta (p j)≤1 := by
  apply (h j).trans
  apply (div_le_one (pow_pos (by exact_mod_cast (Fact.out : (p j).Prime).pos) 4)).mpr
  exact one_le_pow₀ (by exact_mod_cast (Fact.out : (p j).Prime).one_lt.le)

lemma exceptional_weight_budget (hinj : Function.Injective p) (hp : ∀j,5≤p j)
    (heta : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4) :
    (∑B∈(univ : Finset (Finset J)).erase ∅,(∏j∈B,p j:ℝ)*exceptionalProduct p B)≤1/4 := by
  have hb := weighted_exceptional_budget (univ : Finset J) p hinj.injOn (fun j _ => hp j)
    (fun j => (p j:ℝ)*tupleEta (p j))
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (tupleEta_nonneg _)) (fun j _ => ?_)
  · simpa only [powerset_univ,prod_mul_distrib,exceptionalProduct] using hb
  · have h0 : (p j:ℝ)≠0 := by exact_mod_cast (Fact.out : (p j).Prime).ne_zero
    calc
      _ ≤ (p j:ℝ)*(1/(p j:ℝ)^4) := mul_le_mul_of_nonneg_left (heta j) (Nat.cast_nonneg _)
      _ = _ := by field_simp

lemma exceptional_large_tail (hinj : Function.Injective p) (hp : ∀j,5≤p j)
    (heta : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4) (N : ℕ) (hN : 0<N) (t : ℝ) :
    (∑B∈((univ : Finset (Finset J)).erase ∅).filter (fun B => (N:ℝ)^t<(∏j∈B,p j:ℝ)),exceptionalProduct p B)≤
      (N:ℝ)^(-t)/4 := by
  let S := ((univ : Finset (Finset J)).erase ∅).filter (fun B => (N:ℝ)^t<(∏j∈B,p j:ℝ))
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he : (N:ℝ)^(-t)*(N:ℝ)^t=1 := by rw [←Real.rpow_add hn,neg_add_cancel,Real.rpow_zero]
  calc
    _ ≤ ∑B∈S,(N:ℝ)^(-t)*((∏j∈B,p j:ℝ)*exceptionalProduct p B) := by
      apply sum_le_sum
      intro B hB
      have hq := (mem_filter.mp hB).2.le
      have hh : 1≤(N:ℝ)^(-t)*(∏j∈B,p j:ℝ) := by
        rw [←he]; exact mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hn.le _)
      simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hh (exceptionalProduct_nonneg p B)
    _ = (N:ℝ)^(-t)*∑B∈S,(∏j∈B,p j:ℝ)*exceptionalProduct p B := (mul_sum ..).symm
    _ ≤ (N:ℝ)^(-t)*(1/4) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn.le _)
      apply le_trans _ (exceptional_weight_budget p hinj hp heta)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun B _ _ =>
        mul_nonneg (prod_nonneg (fun j _ => Nat.cast_nonneg _)) (exceptionalProduct_nonneg p B))
    _ = _ := by ring

lemma exceptional_small_power_budget (hinj : Function.Injective p) (hp : ∀j,5≤p j)
    (heta : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4) (S : Finset (Finset J))
    (hS : S⊆(univ : Finset (Finset J)).erase ∅) (a : ℝ) (ha : a≤1) :
    (∑B∈S,exceptionalProduct p B*(∏j∈B,p j:ℝ)^a)≤1/4 := by
  calc
    _ ≤ ∑B∈S,(∏j∈B,p j:ℝ)*exceptionalProduct p B := by
      apply sum_le_sum
      intro B _
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_right _ (exceptionalProduct_nonneg p B)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (primeProduct_one_le p B) ha
    _ ≤ _ := le_trans (sum_le_sum_of_subset_of_nonneg hS (fun B _ _ =>
        mul_nonneg (prod_nonneg (fun j _ => Nat.cast_nonneg _)) (exceptionalProduct_nonneg p B)))
      (exceptional_weight_budget p hinj hp heta)

end Budget

end SquareDifference

end

end OAI
