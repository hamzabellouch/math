import OAI.Combinatorics.ContingencyTables.Sampling.ResidualMixture
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs

namespace OAI

/-!
# First-success law and finite-law error bounds

The bounded outer sampler repeats independent trials and uses a fixed
feasible fallback. Its geometric output law has a stationary uniform-mixture
specialization. Total-variation bounds are preserved by deterministic output
maps.
-/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators
open ResidualMixture

variable {α β : Type*} [Fintype α] [Fintype β]

def variation (p q : RationalLaw α) : ℚ :=
  (∑ x, |p.mass x - q.mass x|) / 2

lemma variation_nonnegative (p q : RationalLaw α) : 0 ≤ variation p q :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

lemma geometric_balance (f : ℚ) (J : ℕ) :
    (1 - f) * (∑ j ∈ Finset.range J, f ^ j) + f ^ J = 1 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [ih]

/-- The exact first-success-or-fallback mass from the manuscript. -/
def outputMass [DecidableEq α] (g : α → ℚ) (f : ℚ) (J : ℕ) (fallback z : α) : ℚ :=
  g z * (∑ j ∈ Finset.range J, f ^ j) + if z = fallback then f ^ J else 0

omit [Fintype α] in
lemma outputMass_nonnegative [DecidableEq α] (g : α → ℚ) (f : ℚ) (J : ℕ)
    (fallback z : α) (hg : ∀ z, 0 ≤ g z) (hf : 0 ≤ f) :
    0 ≤ outputMass g f J fallback z := by
  apply add_nonneg
  · exact mul_nonneg (hg z) (Finset.sum_nonneg fun _ _ => pow_nonneg hf _)
  · split_ifs <;> positivity

lemma outputMass_total [DecidableEq α] (g : α → ℚ) (f : ℚ) (J : ℕ)
    (fallback : α) (htotal : (∑ z, g z) + f = 1) :
    ∑ z, outputMass g f J fallback z = 1 := by
  simp only [outputMass, Finset.sum_add_distrib, ← Finset.sum_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hsum : (∑ z, g z) = 1 - f := by linarith
  rw [hsum]
  exact geometric_balance f J

def outputLaw [DecidableEq α] (g : α → ℚ) (f : ℚ) (J : ℕ)
    (fallback : α) (hg : ∀ z, 0 ≤ g z) (hf : 0 ≤ f)
    (htotal : (∑ z, g z) + f = 1) : RationalLaw α where
  mass := outputMass g f J fallback
  nonnegative := fun z => outputMass_nonnegative g f J fallback z hg hf
  total := outputMass_total g f J fallback htotal

variable [Nonempty α]

def uniformLaw : RationalLaw α where
  mass := fun _ => uniformMass (α := α)
  nonnegative := fun _ => uniformMass_pos.le
  total := uniformMass_total

omit [Nonempty α] in
/-- Successful stationary pairs have equal mass; the repeated-trial law
is exactly a uniform law mixed with the fallback, without conditioning on
the implemented approximate trial's success. -/
theorem stationary_output_mass [DecidableEq α] (s : ℚ) (J : ℕ) (fallback z : α) :
    outputMass (fun _ => s * uniformMass (α := α)) (1 - s) J fallback z =
      (1 - (1 - s) ^ J) * uniformMass (α := α) +
        if z = fallback then (1 - s) ^ J else 0 := by
  have hgeom := geometric_balance (1 - s) J
  have hgeom' : s * (∑ j ∈ Finset.range J, (1 - s) ^ j) = 1 - (1 - s) ^ J := by
    nlinarith [hgeom]
  dsimp [outputMass]
  rw [mul_assoc, mul_comm (uniformMass (α := α)), ← mul_assoc, hgeom']

omit [Nonempty α] in
lemma point_mass_variation [DecidableEq α] (p : RationalLaw α) (fallback : α) :
    (∑ z, |(if z = fallback then (1 : ℚ) else 0) - p.mass z|) / 2 ≤ 1 := by
  have hsum : (∑ z, |(if z = fallback then (1 : ℚ) else 0) - p.mass z|) ≤ 2 := by
    calc
      _ ≤ ∑ z, ((if z = fallback then (1 : ℚ) else 0) + p.mass z) := by
        apply Finset.sum_le_sum
        intro z _
        have hi : (0 : ℚ) ≤ if z = fallback then 1 else 0 := by split_ifs <;> norm_num
        calc
          _ ≤ |if z = fallback then (1 : ℚ) else 0| + |p.mass z| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg hi, abs_of_nonneg (p.nonnegative z)]
      _ = 2 := by simp [Finset.sum_add_distrib, p.total]; norm_num
  linarith

/-- The stationary repeated-trial error is at most the probability that
all trials fail. No error term is divided by a success probability. -/
theorem stationary_variation [DecidableEq α] (s : ℚ) (_hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (J : ℕ) (fallback : α) :
    (∑ z, |outputMass (fun _ => s * uniformMass (α := α)) (1 - s) J fallback z -
      uniformMass (α := α)|) / 2 ≤ (1 - s) ^ J := by
  have hf : 0 ≤ (1 - s) ^ J := pow_nonneg (sub_nonneg.mpr hs1) _
  have hpoint := point_mass_variation (uniformLaw (α := α)) fallback
  have hterm (z : α) :
      |outputMass (fun _ => s * uniformMass (α := α)) (1 - s) J fallback z -
        uniformMass (α := α)| =
      (1 - s) ^ J * |(if z = fallback then (1 : ℚ) else 0) - uniformMass (α := α)| := by
    rw [stationary_output_mass]
    have heq : (1 - (1 - s) ^ J) * uniformMass (α := α) +
        (if z = fallback then (1 - s) ^ J else 0) - uniformMass (α := α) =
        (1 - s) ^ J * ((if z = fallback then 1 else 0) - uniformMass (α := α)) := by
      split_ifs <;> ring
    rw [heq, abs_mul, abs_of_nonneg hf]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  change (1 - s) ^ J * (∑ z, |(if z = fallback then 1 else 0) - uniformMass (α := α)|) / 2 ≤ _
  change (∑ z, |(if z = fallback then 1 else 0) - uniformMass (α := α)|) / 2 ≤ 1 at hpoint
  nlinarith [mul_le_mul_of_nonneg_left hpoint hf]

omit [Nonempty α] in
def mapLaw [DecidableEq β] (p : RationalLaw α) (f : α → β) : RationalLaw β where
  mass := fun y => ∑ x, if f x = y then p.mass x else 0
  nonnegative := fun y => Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact p.nonnegative x
    · rfl
  total := by
    rw [Finset.sum_comm]
    simpa using p.total

omit [Nonempty α] in
/-- Deterministic postprocessing contracts total variation, as used for
the map selecting the first successful trial and unpadding its table. -/
theorem variation_map [DecidableEq β] (p q : RationalLaw α) (f : α → β) :
    variation (mapLaw p f) (mapLaw q f) ≤ variation p q := by
  unfold variation
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ = ∑ y, |∑ x, if f x = y then p.mass x - q.mass x else 0| := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      simp only [mapLaw, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ ≤ ∑ y, ∑ x, |if f x = y then p.mass x - q.mass x else 0| := by
      apply Finset.sum_le_sum
      intro y _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |p.mass x - q.mass x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp only [abs_ite, abs_zero]
      simp

omit [Nonempty α] in
def productLaw (p : RationalLaw α) (q : RationalLaw β) : RationalLaw (α × β) where
  mass := fun z => p.mass z.1 * q.mass z.2
  nonnegative := fun z => mul_nonneg (p.nonnegative z.1) (q.nonnegative z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, q.total, mul_one, p.total]

omit [Nonempty α] in
/-- Independent trials accumulate their errors additively, before the
deterministic first-success map is applied. -/
theorem variation_product (p q : RationalLaw α) (r s : RationalLaw β) :
    variation (productLaw p r) (productLaw q s) ≤ variation p q + variation r s := by
  have hpoint (a : α) (b : β) : |p.mass a * r.mass b - q.mass a * s.mass b| ≤
      p.mass a * |r.mass b - s.mass b| + |p.mass a - q.mass a| * s.mass b := by
    calc
      _ = |p.mass a * (r.mass b - s.mass b) + (p.mass a - q.mass a) * s.mass b| := by
        congr 1
        ring
      _ ≤ |p.mass a * (r.mass b - s.mass b)| + |(p.mass a - q.mass a) * s.mass b| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (p.nonnegative a), abs_of_nonneg (s.nonnegative b)]
  have hsum : (∑ a, ∑ b, |p.mass a * r.mass b - q.mass a * s.mass b|) ≤
      (∑ a, |p.mass a - q.mass a|) + (∑ b, |r.mass b - s.mass b|) := by
    calc
      _ ≤ ∑ a, ∑ b, (p.mass a * |r.mass b - s.mass b| +
          |p.mass a - q.mass a| * s.mass b) := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.sum_le_sum fun b _ => hpoint a b
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          p.total, s.total, one_mul, mul_one]
        ring
  unfold variation
  simp only [productLaw, Fintype.sum_prod_type]
  linarith

end ContingencyTables.FirstSuccess

end OAI
