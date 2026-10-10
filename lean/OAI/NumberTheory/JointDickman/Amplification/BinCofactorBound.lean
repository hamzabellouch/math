import OAI.NumberTheory.JointDickman.Amplification.FiniteWeightCofactorComplete
import OAI.NumberTheory.JointDickman.Amplification.BinLowFrequency

namespace OAI

/-! # Cofactor cancellation for the actual finite-prime weighted bin labels -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma bin_prime_above_first_root {J : ℕ} (hJ : 0 < J) {x : ℝ} (hx : 1 ≤ x)
    (i : Fin (J-1)) {p : ℕ} (hp : p ∈ primeBin x J (i.val+1)) :
    p.Prime ∧ x^((1:ℝ)/J) < (p:ℝ) := by
  have hh := (mem_primeBin_iff (by linarith : 0 ≤ x) J (i.val+1) p).mp hp
  refine ⟨hh.1,lt_of_le_of_lt ?_ hh.2.1⟩
  apply Real.rpow_le_rpow_of_exponent_le hx
  have hJr : (0:ℝ) ≤ J := by exact_mod_cast hJ.le
  apply div_le_div_of_nonneg_right _ hJr
  push_cast
  linarith [show (0:ℝ) ≤ i.val by positivity]

lemma binLabel_small_prime_power {J : ℕ} (hJ : 0 < J) {x : ℝ} (hx : 1 ≤ x)
    (ζ : Fin (J-1) → ℂ) {p : ℕ} (hp : p.Prime)
    (hpx : (p:ℝ) ≤ x^((1:ℝ)/J)) (k : ℕ) :
    binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ (p^k) = 1 := by
  apply binLabel_eq_one_of_no_factor _ _ (pow_ne_zero _ hp.ne_zero)
  intro i q hq hqp
  obtain ⟨hqprime,hqx⟩ := bin_prime_above_first_root hJ hx i hq
  have heq : q=p := ((Nat.dvd_prime hp).mp (hqprime.dvd_of_dvd_pow hqp)).resolve_left hqprime.ne_one
  subst q
  linarith

lemma binLabel_fixed_product_invariant {J : ℕ} (hJ : 0 < J) {x : ℝ} (hx : 1 ≤ x)
    (ζ : Fin (J-1) → ℂ) (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    (hEx : ∀ p ∈ E, (p:ℝ) ≤ x^((1:ℝ)/J)) :
    ∀ D ∈ E.powerset, ∀ n : ℕ, 0 < n →
      binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ ((∏ p ∈ D,p)*n) =
      binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n := by
  intro D hD n _
  apply binLabel_mul_invariant _ _
    (ne_of_gt (prod_pos (fun p hp => (hE p (mem_powerset.mp hD hp)).pos)))
  intro i q hq hqd
  obtain ⟨hqprime,hqx⟩ := bin_prime_above_first_root hJ hx i hq
  obtain ⟨p,hp,hqp⟩ := (hqprime.prime.dvd_finsetProd_iff id).mp hqd
  have heq : q=p := ((Nat.dvd_prime (hE p (mem_powerset.mp hD hp))).mp hqp).resolve_left hqprime.ne_one
  have hpx := hEx p (mem_powerset.mp hD hp)
  subst q
  linarith

/-- The functions here are exactly the manuscript's bin labels with a fixed
finite-prime weight. Only the explicit prime-scale inequalities remain. -/
theorem bin_cofactor_away_zero {J : ℕ} (hJ : 0 < J) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∃ K : ℕ, 0 < T ∧ 2 ≤ K ∧
    ∀ (N : ℕ) (a x : ℝ), 1 ≤ a → 1 ≤ x → K ≤ ⌊(N:ℝ)/a⌋₊ →
      (⌊(2*N:ℝ)/a⌋₊:ℝ)^c ≤ x^((1:ℝ)/J) →
      (∀ p ∈ E, (p:ℝ) ≤ x^((1:ℝ)/J)) →
      ∀ (ζ : Fin (J-1) → ℂ), (∀ i, ‖ζ i‖ ≤ 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧
        (⌊(2*N:ℝ)/a⌋₊:ℝ)^c < (p:ℝ) ∧ (p:ℝ) ≤ (⌊(N:ℝ)/a⌋₊:ℝ)) →
      Disjoint E P → ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ t : ℝ, T ≤ |t| → |t| ≤ (⌊(2*N:ℝ)/a⌋₊:ℝ)^2 →
      ‖mrtCofactorPolynomial P
        (finiteWeightedCoefficient
          (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w) N a t‖ ≤ ε := by
  obtain ⟨T,K,hT,hK,hbound⟩ := finite_weight_count_window_away_zero hc hc1 E hE hε
  refine ⟨T,K,hT,hK,?_⟩
  intro N a x ha hx hm hcut hEx ζ hζ P hP hdis w hw t htlo hthi
  apply hbound N a ha hm _ (binLabel_isMultiplicative _ _)
    (norm_binLabel_le_one_of_norm_le _ ζ hζ) ?_
    (binLabel_fixed_product_invariant hJ hx ζ E hE hEx) P hP hdis w hw t htlo hthi
  intro p k hp hpc _
  exact binLabel_small_prime_power hJ hx ζ hp (hpc.trans hcut) k

end JointDickman

end OAI
