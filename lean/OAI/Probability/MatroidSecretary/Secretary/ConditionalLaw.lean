import OAI.Probability.MatroidSecretary.Secretary.KernelModel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace OAI

/-!
Exact normalization, support, and joint-law identities for finite conditional
seed reconstruction. This is supporting work for `cor:secretary`; it does not
assume a prefix law or supply the online secretary construction by itself.
-/

namespace MatroidProphet.Secretary

open scoped BigOperators

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
theorem fiberMass_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (b : β) : 0 ≤ fiberMass p f b := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · exact le_rfl

omit [DecidableEq α] in
theorem le_fiberMass (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (a : α) : p a ≤ fiberMass p f (f a) := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun x => if f x = f a then p x else 0)
    (fun x _ => by split_ifs; exact hp x; exact le_rfl)
    (Finset.mem_univ a)
  simpa [fiberMass] using h

omit [DecidableEq α] in
theorem source_zero_of_fiberMass_zero (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) {a : α} {b : β} (hab : f a = b)
    (hb : fiberMass p f b = 0) : p a = 0 := by
  have h := le_fiberMass p hp f a
  rw [hab, hb] at h
  exact le_antisymm h (hp a)

theorem fiberKernel_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (fallback : α) (b : β) (a : α) :
    0 ≤ fiberKernel p f fallback b a := by
  unfold fiberKernel
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (hp a) (fiberMass_nonneg p hp f b)
  · exact le_rfl

theorem fiberKernel_sum (p : α → ℝ) (f : α → β)
    (fallback : α) (b : β) : ∑ a, fiberKernel p f fallback b a = 1 := by
  by_cases hb : fiberMass p f b = 0
  · simp [fiberKernel, hb]
  · simp only [fiberKernel, hb, ite_false]
    calc
      (∑ a, if f a = b then p a / fiberMass p f b else 0) =
          (∑ a, if f a = b then p a else 0) / fiberMass p f b := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> simp
      _ = 1 := div_self hb

theorem fiberKernel_support (p : α → ℝ) (f : α → β)
    (fallback : α) {b : β} (hb : fiberMass p f b ≠ 0)
    {a : α} (ha : fiberKernel p f fallback b a ≠ 0) : f a = b := by
  by_contra h
  exact ha (by simp [fiberKernel, hb, h])

/-- The exact joint law, including observations of zero source probability. -/
theorem fiberMass_mul_fiberKernel (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (fallback : α) (b : β) (a : α) :
    fiberMass p f b * fiberKernel p f fallback b a =
      if f a = b then p a else 0 := by
  by_cases hb : fiberMass p f b = 0
  · rw [hb, zero_mul]
    by_cases hab : f a = b
    · simp [hab, source_zero_of_fiberMass_zero p hp f hab hb]
    · simp [hab]
  · by_cases hab : f a = b
    · simp [fiberKernel, hb, hab, mul_div_cancel₀]
    · simp [fiberKernel, hb, hab]

variable [Fintype β]

omit [DecidableEq α] in
theorem fiberMass_sum (p : α → ℝ) (f : α → β) :
    ∑ b, fiberMass p f b = ∑ a, p a := by
  unfold fiberMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- Reconstruction preserves the full joint distribution of observation and seed.
The test function may depend on unused source coordinates and on the observation. -/
theorem fiberKernel_joint_expectation (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (fallback : α) (g : β → α → ℝ) :
    (∑ b, fiberMass p f b * (∑ a, fiberKernel p f fallback b a * g b a)) =
      ∑ a, p a * g (f a) a := by
  simp_rw [Finset.mul_sum, ← mul_assoc, fiberMass_mul_fiberKernel p hp f fallback]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem fiberKernel_marginal (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (fallback : α) (a : α) :
    (∑ b, fiberMass p f b * fiberKernel p f fallback b a) = p a := by
  simp_rw [fiberMass_mul_fiberKernel p hp f fallback]
  simp

/-- A bona fide conditional probability mass function on the complete seed. -/
noncomputable def fiberPMF (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (fallback : α) (b : β) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (fiberKernel p f fallback b a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun a _ => fiberKernel_nonneg p hp f fallback b a), fiberKernel_sum,
      ENNReal.ofReal_one])

omit [Fintype β] in
@[simp] theorem fiberPMF_apply (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : α → β) (fallback : α) (b : β) (a : α) :
    fiberPMF p hp f fallback b a = ENNReal.ofReal (fiberKernel p f fallback b a) :=
  PMF.ofFintype_apply _ _

/-- The observation marginal as an actual PMF, with its normalization proved. -/
noncomputable def fiberMarginalPMF (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (f : α → β) : PMF β :=
  PMF.ofFintype (fun b => ENNReal.ofReal (fiberMass p f b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => fiberMass_nonneg p hp f b),
      fiberMass_sum, hpsum, ENNReal.ofReal_one])

omit [DecidableEq α] in
@[simp] theorem fiberMarginalPMF_apply (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (f : α → β) (b : β) :
    fiberMarginalPMF p hp hpsum f b = ENNReal.ofReal (fiberMass p f b) :=
  PMF.ofFintype_apply _ _

theorem fiberPMF_joint_atom (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) (f : α → β) (fallback : α) (b : β) (a : α) :
    fiberMarginalPMF p hp hpsum f b * fiberPMF p hp f fallback b a =
      if f a = b then ENNReal.ofReal (p a) else 0 := by
  rw [fiberMarginalPMF_apply, fiberPMF_apply,
    ← ENNReal.ofReal_mul (fiberMass_nonneg p hp f b),
    fiberMass_mul_fiberKernel p hp f fallback]
  split_ifs <;> simp

end MatroidProphet.Secretary

end OAI
