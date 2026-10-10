import Mathlib
import OAI.Probability.BinarySweep.Model

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

abbrev Coins (d : ℕ) := Slot d → Bool

def physical (d : ℕ) (c : Coins d) : Equiv.Perm (Slot (d + 1)) where
  toFun x := Fin.snoc (Fin.tail x) (x 0 ^^ c (Fin.tail x))
  invFun y := Fin.cons (y (Fin.last d) ^^ c (Fin.init y)) (Fin.init y)
  left_inv x := by
    simp
  right_inv y := by
    simp

def physicalHistory (d t : ℕ) (c : Fin t → Coins d) : Equiv.Perm (Slot (d + 1)) :=
  (List.ofFn (fun i => physical d (c i))).reverse.prod

def physicalLaw (d t : ℕ) : Equiv.Perm (Slot (d + 1)) → ℝ :=
  finiteLaw (physicalHistory d t)

def c0 : ℝ := (1 / 100 : ℝ) / 100
def e0 : ℝ := (1 / 100 : ℝ) / 100
def cExponent (s : ℕ) : ℝ := c0 + 1 / Real.sqrt (Real.log s)
def eExponent (s : ℕ) : ℝ := e0 - 1 / Real.sqrt (Real.log s)

def traceMoment {D : ℕ} (q : ℕ) (K : RepSpace D →L[ℂ] RepSpace D) : ℝ :=
  (LinearMap.trace ℂ (RepSpace D)
    (((ContinuousLinearMap.adjoint K) * K) ^ q).toLinearMap).re

def logMoment (T : ℝ) : EReal := (ENNReal.ofReal T).log

section FiniteProbability
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

lemma finiteLaw_nonneg (f : Ω → G) (g : G) : 0 ≤ finiteLaw f g := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma finiteLaw_sum [Nonempty Ω] (f : Ω → G) : ∑ g, finiteLaw f g = 1 := by
  classical
  simp only [finiteLaw]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

lemma uniformLaw_sum [Nonempty G] : ∑ g, uniformLaw G g = 1 := by
  simp [uniformLaw, Fintype.card_ne_zero]

lemma finiteLaw_eq_zero_outside (f : Ω → G) (s : Finset G)
    (hs : ∀ ω, f ω ∈ s) {g : G} (hg : g ∉ s) : finiteLaw f g = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro ω _
  rw [ite_eq_right]
  intro he
  exact hg (he ▸ hs ω)

lemma event_le_totalVariation (p q : G → ℝ) (heq : ∑ g, p g = ∑ g, q g)
    (s : Finset G) : ∑ g ∈ s, (p g - q g) ≤ totalVariation p q := by
  classical
  have hzero : ∑ g, (p g - q g) = 0 := by
    rw [Finset.sum_sub_distrib, heq, sub_self]
  have hsplit := Finset.sum_add_sum_compl s (fun g => p g - q g)
  rw [hzero] at hsplit
  have hspabs := Finset.sum_add_sum_compl s (fun g => |p g - q g|)
  have h₁ : ∑ g ∈ s, (p g - q g) ≤ ∑ g ∈ s, |p g - q g| :=
    Finset.sum_le_sum (fun _ _ => le_abs_self _)
  have h₂ : -(∑ g ∈ sᶜ, (p g - q g)) ≤ ∑ g ∈ sᶜ, |p g - q g| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun _ _ => neg_le_abs _)
  unfold totalVariation
  linarith

theorem uniform_image_support_obstruction [Nonempty Ω] [Nonempty G] (f : Ω → G) :
    1 - (Fintype.card Ω : ℝ) / Fintype.card G ≤
      totalVariation (finiteLaw f) (uniformLaw G) := by
  classical
  let s : Finset G := Finset.univ.image f
  have hs (ω : Ω) : f ω ∈ s := Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩
  have hsum : ∑ g ∈ s, finiteLaw f g = 1 := by
    have hout : ∑ g ∈ sᶜ, finiteLaw f g = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      exact finiteLaw_eq_zero_outside f s hs (Finset.mem_compl.mp hg)
    have h := Finset.sum_add_sum_compl s (finiteLaw f)
    rw [hout, add_zero, finiteLaw_sum] at h
    exact h
  have he : ∑ g ∈ s, (finiteLaw f g - uniformLaw G g) =
      1 - (s.card : ℝ) / Fintype.card G := by
    rw [Finset.sum_sub_distrib, hsum]
    simp [uniformLaw, div_eq_mul_inv]
  have ht := event_le_totalVariation (finiteLaw f) (uniformLaw G)
    (by rw [finiteLaw_sum, uniformLaw_sum]) s
  rw [he] at ht
  have hcard : (s.card : ℝ) ≤ Fintype.card Ω := by
    exact_mod_cast (Finset.card_image_le : s.card ≤ Finset.univ.card)
  have hden : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  calc
    1 - (Fintype.card Ω : ℝ) / Fintype.card G ≤
        1 - (s.card : ℝ) / Fintype.card G :=
      sub_le_sub_left (div_le_div_of_nonneg_right hcard hden.le) 1
    _ ≤ _ := ht

end FiniteProbability

theorem physical_support_obstruction (d t : ℕ) :
    1 - (2 : ℝ) ^ (t * 2 ^ d) / (Nat.factorial (2 ^ (d + 1)) : ℝ) ≤
      totalVariation (physicalLaw d t) (uniformLaw (Equiv.Perm (Slot (d + 1)))) := by
  have h := uniform_image_support_obstruction (physicalHistory d t)
  simpa [physicalLaw, Coins, Slot, Fintype.card_fun, Fintype.card_perm,
    Nat.cast_pow, ← pow_mul, mul_comm] using h

def supportTimeBound (d : ℕ) : ℝ :=
  (2 / (2 : ℝ) ^ (d + 1)) *
    Real.logb 2 (3 * (Nat.factorial (2 ^ (d + 1)) : ℝ) / 4)

theorem physical_threshold_time (d t : ℕ)
    (ht : totalVariation (physicalLaw d t)
      (uniformLaw (Equiv.Perm (Slot (d + 1)))) ≤ 1 / 4) :
    ⌈supportTimeBound d⌉ ≤ (t : ℤ) := by
  apply Int.ceil_le.mpr
  have h := (physical_support_obstruction d t).trans ht
  have hfact : (0 : ℝ) < Nat.factorial (2 ^ (d + 1)) := by positivity
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 3 * (Nat.factorial (2 ^ (d + 1)) : ℝ) / 4 ≤
      (2 : ℝ) ^ (t * 2 ^ d) := by
    have : (3 / 4 : ℝ) ≤
        (2 : ℝ) ^ (t * 2 ^ d) / (Nat.factorial (2 ^ (d + 1)) : ℝ) := by linarith
    have := (le_div_iff₀ hfact).mp this
    linarith
  have hl := Real.log_le_log (by positivity) hb
  rw [Real.log_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hl
  have hdiv : Real.log (3 * (Nat.factorial (2 ^ (d + 1)) : ℝ) / 4) /
      Real.log 2 ≤ (t : ℝ) * (2 : ℝ) ^ d := (div_le_iff₀ hlog).mpr hl
  rw [Int.cast_natCast]
  change (2 / (2 : ℝ) ^ (d + 1)) *
    (Real.log (3 * (Nat.factorial (2 ^ (d + 1)) : ℝ) / 4) / Real.log 2) ≤ (t : ℝ)
  rw [pow_succ]
  have hmul := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ 2 / ((2 : ℝ)^d * 2) by positivity)
  calc
    _ ≤ (2 / ((2 : ℝ)^d * 2)) * ((t : ℝ) * (2 : ℝ)^d) := hmul
    _ = (t : ℝ) := by field_simp

end BinaryCoordinateSweeps
end

end OAI
