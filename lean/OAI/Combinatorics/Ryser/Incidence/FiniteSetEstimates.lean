module
public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import all Mathlib.Combinatorics.Additive.PluenneckeRuzsa

namespace OAI

public section

namespace RyserCoveringCounterexample.Incidence.FiniteSetEstimates

open Finset Nat
open scoped Pointwise

variable {G : Type*} [DecidableEq G]

section Group
variable [Group G] {A B C : Finset G}

@[to_additive                                                             ]
theorem ruzsa_triangle_inequality_div_div_div (A B C : Finset G) :
    #(A / C) * #B ≤ #(A / B) * #(C / B) := by
  exact Finset.ruzsa_triangle_inequality_div_div_div A B C

@[to_additive                                                             ]
theorem ruzsa_triangle_inequality_div_mul_mul (A B C : Finset G) :
    #(A / C) * #B ≤ #(A * B) * #(C * B) := by
  exact Finset.ruzsa_triangle_inequality_div_mul_mul A B C

@[to_additive]
theorem pluennecke_petridis_inequality_mul (C : Finset G)
    (hA : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A) :
    #(C * A * B) * #A ≤ #(A * B) * #(C * A) := by
  exact Finset.pluennecke_petridis_inequality_mul C hA

end Group

variable [CommGroup G] {A B C : Finset G}

@[to_additive]
private theorem mul_aux (hA : A.Nonempty) (hAB : A ⊆ B)
    (h : ∀ A' ∈ B.powerset.erase ∅, (#(A * C) : ℚ≥0) / #A ≤ #(A' * C) / #A') :
    ∀ A' ⊆ A, #(A * C) * #A' ≤ #(A' * C) * #A := by
  exact Finset.mul_aux hA hAB h

@[to_additive]
private lemma card_mul_pow_le (hAB : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A) (n : ℕ) :
    #(A * B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ n * #A := by
  exact Finset.card_mul_pow_le hAB n

@[to_additive
                                                                                        ]
theorem pluennecke_ruzsa_inequality_pow_div_pow_mul (hA : A.Nonempty) (B : Finset G) (m n : ℕ) :
    #(B ^ m / B ^ n) ≤ (#(A * B) / #A : ℚ≥0) ^ (m + n) * #A := by
  exact Finset.pluennecke_ruzsa_inequality_pow_div_pow_mul hA B m n

@[to_additive                                                                ]
theorem pluennecke_ruzsa_inequality_pow_div_pow_div (hA : A.Nonempty) (B : Finset G) (m n : ℕ) :
    #(B ^ m / B ^ n) ≤ (#(A / B) / #A : ℚ≥0) ^ (m + n) * #A := by
  exact Finset.pluennecke_ruzsa_inequality_pow_div_pow_div hA B m n

end RyserCoveringCounterexample.Incidence.FiniteSetEstimates

end

end OAI
