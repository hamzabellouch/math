import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestLearningIncidence

namespace OAI

section
namespace SharpLogRamsey.Incidence
open Finset
open scoped BigOperators Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Finite K] [FiniteDimensional K V]
variable [Fintype (Projectivization K V)]
variable [Fintype (Projectivization K (Module.Dual K V))]

theorem sparse_product_bound_two {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V)))
    (hsparse : (incidenceCount S T : ℝ) ≤ (S.card : ℝ)*T.card/(20*Nat.card K)) :
    (S.card : ℝ)*T.card ≤ 2*(Nat.card K : ℝ)^(n+3) := by
  let q : ℝ := Nat.card K
  let v : ℝ := ∑ i ∈ range (n+3), q^i
  let k : ℝ := ∑ i ∈ range (n+2), q^i
  let a : ℝ := (S.card : ℝ)*T.card
  have hq : 2 ≤ q := by
    have hh : 2 ≤ Nat.card K := Finite.one_lt_card
    change (2:ℝ) ≤ (Nat.card K:ℝ)
    exact_mod_cast hh
  have hk : 1+q ≤ k := by
    calc
      _ = ∑ i ∈ range 2, q^i := by norm_num [sum_range_succ]
      _ ≤ ∑ i ∈ range (n+2), q^i :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (by intros; positivity)
  have hgeom : v = q*k+1 := geom_sum_succ
  have hv : 0 < v := by nlinarith
  have hp : 4/(5*q) ≤ k/v := by
    apply (div_le_div_iff₀ (by positivity) hv).mpr
    nlinarith
  have ha : 0 ≤ a := by positivity
  have hdev : 3*a/(4*q) ≤ k/v*a-(incidenceCount S T : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hp ha
    change (incidenceCount S T : ℝ) ≤ a/(20*q) at hsparse
    have hid : (4/(5*q))*a = 16*(a/(20*q)) := by ring
    have hid' : 3*a/(4*q) = 15*(a/(20*q)) := by ring
    rw [hid] at hmul
    rw [hid']
    have hnon : 0 ≤ a/(20*q) := by positivity
    linarith
  have hsq := projective_mixing_sq hdim S T
  change ((incidenceCount S T : ℝ) - k/v*S.card*T.card)^2 ≤ q^(n+1)*S.card*T.card at hsq
  have hsq' : (3*a/(4*q))^2 ≤ q^(n+1)*a := by
    have hdnon : 0 ≤ k/v*a-(incidenceCount S T : ℝ) :=
      (by positivity : 0 ≤ 3*a/(4*q)).trans hdev
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ 3*a/(4*q)) hdnon).mpr hdev
    nlinarith [hsq]
  have hpow : q^(n+3) = q^(n+1)*q^2 := by rw [← pow_add]
  rw [hpow]
  by_cases haz : a = 0
  · change a ≤ _; rw [haz]; positivity
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hq0 : q ≠ 0 := by linarith
  have hcancel : (3*a/(4*q))^2 * (16*q^2) = 9*a^2 := by
    calc
      _ = (9*a^2/(16*q^2))*(16*q^2) := by ring
      _ = 9*a^2 := div_mul_cancel₀ _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hq0))
  have hmult := mul_le_mul_of_nonneg_right hsq' (by positivity : 0 ≤ 16*q^2)
  rw [hcancel] at hmult
  change a ≤ _
  nlinarith [hmult]

lemma sparse_smaller_square {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (hsmall : S.card≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤(S.card:ℝ)*T.card/(20*Nat.card K)) :
    (S.card:ℝ)^2≤2*(Nat.card K:ℝ)^(n+3) := by
  have hh : (S.card:ℝ)≤T.card := by exact_mod_cast hsmall
  calc
    _ = (S.card:ℝ)*S.card := pow_two _
    _ ≤ (S.card:ℝ)*T.card := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ _ := sparse_product_bound_two hdim S T hsparse

end SharpLogRamsey.Incidence

end

end OAI
