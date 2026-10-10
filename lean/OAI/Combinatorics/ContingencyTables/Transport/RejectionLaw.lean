import OAI.Combinatorics.ContingencyTables.Transport.FirstSuccess

namespace OAI

/-! # Exact finite repeated-trial laws and their approximation error -/

namespace ContingencyTables.FirstSuccess

open scoped BigOperators Classical
open ResidualMixture

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

theorem variation_self (p : RationalLaw α) : variation p p = 0 := by
  simp [variation]

theorem variation_triangle (p q r : RationalLaw α) :
    variation p r ≤ variation p q + variation q r := by
  have hsum : (∑ x, |p.mass x - r.mass x|) ≤
      (∑ x, |p.mass x - q.mass x|) + ∑ x, |q.mass x - r.mass x| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => abs_sub_le (p.mass x) (q.mass x) (r.mass x)
  unfold variation
  linarith

def pointLaw (z : β) : RationalLaw β where
  mass := fun y => if y = z then 1 else 0
  nonnegative := fun y => by split_ifs <;> norm_num
  total := by simp

def retryStep (p : RationalLaw α) (f : α → Option β) (tail : RationalLaw β) : RationalLaw β :=
  mapLaw (productLaw p tail) (fun z => (f z.1).getD z.2)

def retryLaw (p : RationalLaw α) (f : α → Option β) (fallback : β) : ℕ → RationalLaw β
  | 0 => pointLaw fallback
  | n + 1 => retryStep p f (retryLaw p f fallback n)

def successMass (p : RationalLaw α) (f : α → Option β) (z : β) : ℚ :=
  ∑ x, if f x = some z then p.mass x else 0

def failureMass (p : RationalLaw α) (f : α → Option β) : ℚ :=
  ∑ x, if f x = none then p.mass x else 0

theorem success_failure_total (p : RationalLaw α) (f : α → Option β) :
    (∑ z, successMass p f z) + failureMass p f = 1 := by
  unfold successMass failureMass
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  calc
    _ = ∑ x, p.mass x := by
      apply Finset.sum_congr rfl
      intro x _
      cases f x <;> simp
    _ = 1 := p.total

theorem retryStep_mass (p : RationalLaw α) (f : α → Option β)
    (tail : RationalLaw β) (z : β) :
    (retryStep p f tail).mass z = successMass p f z + failureMass p f * tail.mass z := by
  change (∑ x : α × β, if (f x.1).getD x.2 = z then p.mass x.1 * tail.mass x.2 else 0) = _
  rw [Fintype.sum_prod_type]
  unfold successMass failureMass
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases hfx : f x with
  | none => simp [hfx]
  | some y =>
    by_cases hy : y = z
    · subst y
      simp only [hfx, Option.getD_some, ite_true, ite_false,
        reduceCtorEq, zero_mul, add_zero]
      rw [← Finset.mul_sum, tail.total, mul_one]
    · simp [hfx, hy]

omit [Fintype β] in
theorem outputMass_succ (g : β → ℚ) (f : ℚ) (n : ℕ) (fallback z : β) :
    outputMass g f (n + 1) fallback z = g z + f * outputMass g f n fallback z := by
  have h := geometric_balance f n
  have hg := congrArg (fun x : ℚ => g z * x) h
  unfold outputMass
  rw [Finset.sum_range_succ, pow_succ]
  split_ifs <;> nlinarith [hg]

/-- The law of finitely many independent trials, each of which can either
return a value or fail, is the geometric first-success law. -/
theorem retryLaw_mass (p : RationalLaw α) (f : α → Option β)
    (fallback z : β) (n : ℕ) :
    (retryLaw p f fallback n).mass z =
      outputMass (successMass p f) (failureMass p f) n fallback z := by
  induction n with
  | zero => simp [retryLaw, pointLaw, outputMass]
  | succ n ih =>
    rw [retryLaw, retryStep_mass, ih, outputMass_succ]

/-- Approximate independent trials incur their error before the success
test. Rejection never divides that error by a success probability. -/
theorem retryLaw_variation (p q : RationalLaw α) (f : α → Option β)
    (fallback : β) (n : ℕ) :
    variation (retryLaw p f fallback n) (retryLaw q f fallback n) ≤
      (n : ℚ) * variation p q := by
  induction n with
  | zero => simp [retryLaw, variation_self]
  | succ n ih =>
    calc
      _ ≤ variation p q + variation (retryLaw p f fallback n) (retryLaw q f fallback n) :=
        (variation_map (productLaw p (retryLaw p f fallback n))
          (productLaw q (retryLaw q f fallback n)) _).trans (variation_product _ _ _ _)
      _ ≤ variation p q + (n : ℚ) * variation p q := add_le_add le_rfl ih
      _ = _ := by push_cast; ring

end

end ContingencyTables.FirstSuccess

end OAI
