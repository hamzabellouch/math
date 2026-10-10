import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularLazyWalk
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallEscape

namespace OAI

/-! # Polynomial lower bounds for regular random-walk energy

The probability mass is supported on one word ball. An adjacent larger ball
contains a point where the vector vanishes. The cocycle word estimate then
gives a quantitative lower bound for its generator energy.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

theorem regularHilbert_point_difference_bound
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) (v : RegularHilbert G)
    {n m : ℕ} {x y : G} (hx : x ∈ wordBall S n) (hy : y ∈ wordBall S m) :
    |v x - v y| ≤ (n + m : ℕ) *
      Real.sqrt (unitaryCocycleEnergy S (unitaryCoboundary regularHilbertRepresentation v)) := by
  let g := x * y⁻¹
  have hg : g ∈ wordBall S (n + m) := mul_mem_wordBall hx (inv_mem_wordBall hS hy)
  obtain ⟨l, hl, hs, he⟩ := (mem_wordBall_iff S (n + m) g).mp hg
  have happ : (unitaryCoboundary regularHilbertRepresentation v g) x = v y - v x := by
    change v (g⁻¹ * x) - v x = v y - v x
    simp only [g, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  calc
    _ = |v y - v x| := abs_sub_comm _ _
    _ ≤ ‖unitaryCoboundary regularHilbertRepresentation v g‖ := by
      simpa only [happ] using regularHilbert_apply_le_norm
        (unitaryCoboundary regularHilbertRepresentation v g) x
    _ = ‖unitaryCoboundary regularHilbertRepresentation v l.prod‖ := by rw [he]
    _ ≤ l.length * Real.sqrt (unitaryCocycleEnergy S
        (unitaryCoboundary regularHilbertRepresentation v)) :=
      (unitaryCoboundary_isCocycle _ v).norm_word_energy_le S l hs
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hl) (Real.sqrt_nonneg _)

theorem regularProbability_energy_lower [Infinite G]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (n : ℕ) (v : RegularHilbert G)
    (hsupport : ∀ x, x ∉ wordBall S n → v x = 0)
    (hmass : (∑ x ∈ wordBall S n, v x) = 1)
    {C : ℝ} (_hC : 0 ≤ C) (b : ℕ)
    (hvol : ((wordBall S n).card : ℝ) ≤ C * (1 + (n : ℝ)) ^ b) :
    1 ≤ (1 + (n : ℝ)) ^ (2 * (b + 1)) *
      (4 * C ^ 2 * unitaryCocycleEnergy S (unitaryCoboundary regularHilbertRepresentation v)) := by
  let E := unitaryCocycleEnergy S (unitaryCoboundary regularHilbertRepresentation v)
  have hE : 0 ≤ E := unitaryCocycleEnergy_nonneg _ _
  obtain ⟨y, hy, hy'⟩ := exists_wordBall_escape S hS hgen n
  have hvy : v y = 0 := hsupport y hy'
  have hpoint (x : G) (hx : x ∈ wordBall S n) :
      v x ≤ 2 * (1 + (n : ℝ)) * Real.sqrt E := by
    have hh := regularHilbert_point_difference_bound S hS v hx hy
    rw [hvy, sub_zero] at hh
    have hc : ((n + (n + 1) : ℕ) : ℝ) ≤ 2 * (1 + (n : ℝ)) := by push_cast; linarith
    exact (le_abs_self _).trans (hh.trans
      (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg E)))
  have hfirst : 1 ≤ (2 * C * (1 + (n : ℝ)) ^ (b + 1)) * Real.sqrt E := by
    calc
      1 = ∑ x ∈ wordBall S n, v x := hmass.symm
      _ ≤ ∑ _x ∈ wordBall S n, 2 * (1 + (n : ℝ)) * Real.sqrt E :=
        sum_le_sum hpoint
      _ = ((wordBall S n).card : ℝ) * (2 * (1 + (n : ℝ)) * Real.sqrt E) := by simp
      _ ≤ (C * (1 + (n : ℝ)) ^ b) * (2 * (1 + (n : ℝ)) * Real.sqrt E) :=
        mul_le_mul_of_nonneg_right hvol (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hsq : 1 ≤ ((2 * C * (1 + (n : ℝ)) ^ (b + 1)) * Real.sqrt E) ^ 2 := by
    nlinarith
  calc
    _ ≤ _ := hsq
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt hE]
      dsimp only [E]
      rw [show 2 * (b + 1) = (b + 1) * 2 by omega, pow_mul]
      ring

theorem regularLazyWalk_polynomial_energy_lower [Infinite G]
    (S : Finset G) (hne : S.Nonempty) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    {C : ℝ} (hC : 0 ≤ C) (b : ℕ)
    (hvol : ∀ n, ((wordBall S n).card : ℝ) ≤ C * (1 + (n : ℝ)) ^ b) (n : ℕ) :
    1 ≤ (1 + (n : ℝ)) ^ (2 * (b + 1)) *
      (4 * C ^ 2 * unitaryCocycleEnergy S
        (unitaryCoboundary regularHilbertRepresentation (regularLazyWalk S n))) :=
  regularProbability_energy_lower S hS hgen n _ (regularLazyWalk_support S hne n)
    (regularLazyWalk_mass S hne n) hC b (hvol n)

end PolycyclicRecognition

end

end OAI
