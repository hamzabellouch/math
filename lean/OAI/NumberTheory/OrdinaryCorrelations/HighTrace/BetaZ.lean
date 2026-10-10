import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace OrdinaryCorrelations.SignedTrace

def betaZ : ℝ := (1 + 1)⁻¹
def theta : ℝ := betaZ ^ 2

@[simp] lemma betaZ_value : betaZ = (1 / 2 : ℝ) := by norm_num [betaZ]
@[simp] lemma theta_value : theta = (1 / 4 : ℝ) := by norm_num [theta]

variable {p ℓ : ℕ} [NeZero p]

def activeResidue (b : Fin ℓ → ℤ) (i : Fin ℓ) : ZMod p := -(b i : ZMod p)

def departureCount (b : Fin ℓ → ℤ) (a : ZMod p) : ℕ :=
  (univ.filter (fun i => a = activeResidue b i)).card

def centerPrimeFactor (b : Fin ℓ → ℤ) (d : Fin ℓ → ℕ) (a : ZMod p) : ℝ :=
  ∏ i, ((if p ∣ d i then
    (if a = activeResidue b i then (1 : ℝ) else 0) - theta / p else 1) *
    betaZ ^ (if a = activeResidue b i then (1 : ℕ) else 0))

def primeMean (f : ZMod p → ℝ) : ℝ := (p : ℝ)⁻¹ * ∑ a, f a

lemma departureCount_sum (b : Fin ℓ → ℤ) :
    ∑ a : ZMod p, departureCount b a = ℓ := by
  simpa [departureCount, eq_comm] using
    sum_card_fiberwise_eq_card_filter (univ : Finset (Fin ℓ))
      (univ : Finset (ZMod p)) (activeResidue b)

omit [NeZero p] in
lemma normalization_product (b : Fin ℓ → ℤ) (a : ZMod p) :
    (∏ i : Fin ℓ, betaZ ^ (if a = activeResidue b i then (1 : ℕ) else 0)) =
      betaZ ^ departureCount b a := by
  rw [prod_pow_eq_pow_sum]
  exact congrArg (fun n => betaZ ^ n) (sum_boole _ _)

omit [NeZero p] in
lemma centerPrimeFactor_singleton (b : Fin ℓ → ℤ) (d : Fin ℓ → ℕ)
    (e : Fin ℓ) (he : ∀ i, p ∣ d i ↔ i = e) (a : ZMod p) :
    centerPrimeFactor b d a =
      ((if a = activeResidue b e then (1 : ℝ) else 0) - theta / p) *
        betaZ ^ departureCount b a := by
  rw [centerPrimeFactor, prod_mul_distrib, normalization_product]
  congr 1
  have hp := prod_eq_single (s := (univ : Finset (Fin ℓ)))
    (f := fun i => if p ∣ d i then
      (if a = activeResidue b i then (1 : ℝ) else 0) - theta / p else 1)
    e (fun i _ hi => ite_eq_right (fun h => hi ((he i).mp h))) (by simp)
  simpa [he e] using hp

lemma singleton_mean_exact (b : Fin ℓ → ℤ) (d : Fin ℓ → ℕ)
    (e : Fin ℓ) (he : ∀ i, p ∣ d i ↔ i = e)
    (h₂ : departureCount b (activeResidue b e : ZMod p) = 2) :
    primeMean (p := p) (centerPrimeFactor b d) =
      theta / (p : ℝ)^2 *
        (1 - theta + ∑ a ∈ (univ : Finset (ZMod p)).erase (activeResidue b e),
          (1 - betaZ ^ departureCount b a)) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hsum : (∑ a : ZMod p, betaZ ^ departureCount b a) =
      theta + ∑ a ∈ (univ : Finset (ZMod p)).erase (activeResidue b e),
        betaZ ^ departureCount b a := by
    rw [← sum_erase_add _ _ (mem_univ (activeResidue b e))]
    rw [h₂]
    dsimp [theta]
    ring
  have haunt : Fintype.card (ZMod p) = p := ZMod.card p
  have hcard : (((univ : Finset (ZMod p)).erase (activeResidue b e)).card : ℝ) =
      (p : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, haunt, Nat.cast_sub]
    · norm_num
    · exact NeZero.one_le
  have hdef : (∑ a ∈ (univ : Finset (ZMod p)).erase (activeResidue b e),
      (1 - betaZ ^ departureCount b a)) =
        (p : ℝ) - 1 -
          ∑ a ∈ (univ : Finset (ZMod p)).erase (activeResidue b e),
            betaZ ^ departureCount b a := by
    rw [sum_sub_distrib]
    simp only [sum_const, nsmul_eq_mul, mul_one, hcard]
  rw [hdef]
  simp only [primeMean, centerPrimeFactor_singleton b d e he, sub_mul, sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true, h₂]
  change (p : ℝ)⁻¹ * (theta - ∑ a : ZMod p, (theta / p) * betaZ ^ departureCount b a) = _
  rw [← mul_sum, hsum]
  field_simp
  ring

lemma one_sub_normalization_nonneg (n : ℕ) : 0 ≤ 1 - betaZ ^ n := by
  exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))

lemma one_sub_normalization_le_count (n : ℕ) : 1 - betaZ ^ n ≤ (n : ℝ) := by
  rcases n with _ | n
  · simp
  · have hpow : 0 ≤ betaZ ^ (n + 1) := pow_nonneg (by norm_num) _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [Nat.cast_add, Nat.cast_one]
    linarith

theorem source_good_singleton_integral (b : Fin ℓ → ℤ) (d : Fin ℓ → ℕ)
    (e : Fin ℓ) (he : ∀ i, p ∣ d i ↔ i = e)
    (h₂ : departureCount b (activeResidue b e : ZMod p) = 2)
    (hlarge : 2 * (ℓ + 1) ≤ p) :
    0 ≤ primeMean (p := p) (centerPrimeFactor b d) ∧
      |primeMean (p := p) (centerPrimeFactor b d)| ≤ theta / (2 * p) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have htheta : 0 ≤ theta := by norm_num
  have hcoef : 0 ≤ theta / (p : ℝ)^2 := div_nonneg htheta (sq_nonneg _)
  have hsum0 : 0 ≤
      ∑ a ∈ (univ : Finset (ZMod p)).erase (activeResidue b e),
        (1 - betaZ ^ departureCount b a) :=
    sum_nonneg (fun a _ => one_sub_normalization_nonneg _)
  have hsumle : (∑ a ∈ (univ : Finset (ZMod p)).erase (activeResidue b e),
      (1 - betaZ ^ departureCount b a)) ≤ (ℓ : ℝ) := by
    calc
      _ ≤ ∑ a ∈ (univ : Finset (ZMod p)).erase (activeResidue b e),
          (departureCount b a : ℝ) :=
        sum_le_sum (fun a _ => one_sub_normalization_le_count _)
      _ ≤ ∑ a : ZMod p, (departureCount b a : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun a _ _ => Nat.cast_nonneg _)
      _ = (ℓ : ℝ) := by exact_mod_cast departureCount_sum b
  rw [singleton_mean_exact b d e he h₂]
  have hnonneg : 0 ≤ theta / (p : ℝ)^2 *
      (1 - theta + ∑ a ∈ (univ : Finset (ZMod p)).erase (activeResidue b e),
        (1 - betaZ ^ departureCount b a)) :=
    mul_nonneg hcoef (by rw [theta_value]; linarith)
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ theta / (p : ℝ)^2 * ((ℓ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hcoef
    _ ≤ theta / (2 * p) := by
      have hlarge' : 2 * ((ℓ : ℝ) + 1) ≤ p := by exact_mod_cast hlarge
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff₀ (sq_pos_of_pos hp) (mul_pos (by norm_num) hp)).mpr
      calc
        theta * ((ℓ : ℝ) + 1) * (2 * p) =
            (theta * p) * (2 * ((ℓ : ℝ) + 1)) := by ring
        _ ≤ (theta * p) * p :=
          mul_le_mul_of_nonneg_left hlarge' (mul_nonneg htheta hp.le)
        _ = theta * (p : ℝ)^2 := by ring

end OrdinaryCorrelations.SignedTrace

end

end OAI
