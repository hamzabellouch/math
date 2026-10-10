import OAI.Combinatorics.DiscreteConvexity.CoveringRegularization
import OAI.Combinatorics.DiscreteConvexity.CoveringSampledFamilies
import OAI.Combinatorics.DiscreteConvexity.Bernoulli

namespace OAI

/-!
# The cost of sampled ordered pairs

The expectation is bounded by counting pair unions with multiplicity. Its
deterministic bound uses the actual regularized edge family and the sharp
`2^r` extension estimate, rather than the coarser tuple-extension estimate.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem regular_pair_weight_sum_le {H : Family V} {rho T : ℝ} {r : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r) :
    (∑ p : PairIndex (regularEdges H rho r T), rho ^ (pairUnion p).card) ≤
      (H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T := by
  classical
  let K := regularEdges H rho r T
  have hK : K ⊆ H := regularEdges_subset H rho r T
  have hinner (a : K) :
      (∑ b : K, rho ^ (a.val ∪ b.val).card) ≤ rho ^ r * ((2 : ℝ) ^ r * T) := by
    have ha : a.val.card = r := hH a.val (hK a.property)
    have hext : (∑ b : K, rho ^ (b.val \ a.val).card) ≤ (2 : ℝ) ^ r * T := by
      rw [Finset.sum_coe_sort K (fun b : Finset V => rho ^ (b \ a.val).card)]
      exact regular_extension_le_two_pow hrho hT hH ha
    calc
      (∑ b : K, rho ^ (a.val ∪ b.val).card) =
          ∑ b : K, rho ^ r * rho ^ (b.val \ a.val).card := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.union_comm, ← Finset.card_sdiff_add_card, pow_add, ha]
        exact mul_comm _ _
      _ = rho ^ r * ∑ b : K, rho ^ (b.val \ a.val).card :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ rho ^ r * ((2 : ℝ) ^ r * T) :=
        mul_le_mul_of_nonneg_left hext (pow_nonneg hrho _)
  have hcard : (K.card : ℝ) ≤ (H.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hK
  have hfactor : 0 ≤ rho ^ r * ((2 : ℝ) ^ r * T) :=
    mul_nonneg (pow_nonneg hrho _) (mul_nonneg (pow_nonneg (by norm_num) _) hT)
  calc
    (∑ p : PairIndex K, rho ^ (pairUnion p).card) =
        ∑ a : K, ∑ b : K, rho ^ (a.val ∪ b.val).card := by
      simp only [PairIndex, Fintype.sum_prod_type, pairUnion]
    _ ≤ ∑ _a : K, rho ^ r * ((2 : ℝ) ^ r * T) :=
      Finset.sum_le_sum (fun a _ => hinner a)
    _ = (K.card : ℝ) * (rho ^ r * ((2 : ℝ) ^ r * T)) := by simp
    _ ≤ (H.card : ℝ) * (rho ^ r * ((2 : ℝ) ^ r * T)) :=
      mul_le_mul_of_nonneg_right hcard hfactor
    _ = (H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T := by ring

/-- The actual independent pair sample has small expected generator cost.
No identification of equal unions is made at the probability-index level. -/
theorem expectation_sampledFamily_le {H : Family V} {rho T p : ℝ} {r : ℕ}
    (hrho : 0 ≤ rho) (hT : 0 ≤ T) (hH : ∀ e ∈ H, e.card = r)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliLaw (α := PairIndex (regularEdges H rho r T)) p hp0 hp1).expectation
        (fun sample => cost rho (sampledFamily (regularEdges H rho r T) sample)) ≤
      p * ((H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T) := by
  classical
  let K := regularEdges H rho r T
  let μ := bernoulliLaw (α := PairIndex K) p hp0 hp1
  calc
    μ.expectation (fun sample => cost rho (sampledFamily K sample)) ≤
        μ.expectation (fun sample => ∑ pair ∈ sample, rho ^ (pairUnion pair).card) :=
      μ.expectation_mono (fun sample => cost_sampledFamily_le K sample hrho)
    _ = p * ∑ pair : PairIndex K, rho ^ (pairUnion pair).card :=
      bernoulliLaw_expect_sum_mem p hp0 hp1 (fun pair => rho ^ (pairUnion pair).card)
    _ ≤ p * ((H.card : ℝ) * rho ^ r * (2 : ℝ) ^ r * T) :=
      mul_le_mul_of_nonneg_left (regular_pair_weight_sum_le hrho hT hH) hp0

end TalagrandDiscreteConvexity.Covering

end OAI
