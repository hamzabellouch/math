import OAI.NumberTheory.DukePrimeDegree.Arithmetic.CyclicInduction

namespace OAI

/-!
# Cyclic averages of the zero character

The same cyclic-subgroup coefficients used in the Artin permutation
identity recover a sum of character values from their cyclic averages.
For a linear character each such average detects the principal factor.
-/

open scoped BigOperators Classical

namespace DukePrimeDegree

/-- The sum of a finite linear character detects the principal character. -/
theorem sum_linearCharacter {C : Type*} [Group C] [Fintype C]
    (χ : C →* ℂˣ) :
    (∑ g, (χ g : ℂ)) = if χ = 1 then (Fintype.card C : ℂ) else 0 := by
  classical
  by_cases hχ : χ = 1
  · simp [hχ]
  · simp only [hχ, ite_false]
    obtain ⟨a, ha⟩ : ∃ a, χ a ≠ 1 := by
      by_contra! h
      apply hχ
      apply MonoidHom.ext
      intro a
      simpa using h a
    have hval : (χ a : ℂ) ≠ 1 := by
      intro h
      exact ha (Units.ext h)
    have hs : (χ a : ℂ) * (∑ g, (χ g : ℂ)) = ∑ g, (χ g : ℂ) := by
      simp only [Finset.mul_sum, ← Units.val_mul, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)
    by_contra hs0
    exact hval ((mul_eq_right₀ hs0).mp hs)

/-- Cyclic indicator coefficients recover the full sum from cyclic
subgroup sums. This is the scalar counterpart of the permutation identity. -/
theorem sum_eq_cyclic_sums
    {G : Type*} [Group G] [Fintype G]
    (a : CyclicSubgroups G → ℤ)
    (ha : ∀ g : G, (∑ C, if g ∈ C.val then a C else 0) = 1)
    (f : G → ℂ) :
    (∑ g, f g) = ∑ C : CyclicSubgroups G, (a C : ℂ) * ∑ g : C.val, f g := by
  classical
  have hcast (g : G) : (∑ C : CyclicSubgroups G,
      if g ∈ C.val then (a C : ℂ) else 0) = 1 := by
    exact_mod_cast ha g
  calc
    (∑ g, f g) = ∑ g, f g *
        (∑ C : CyclicSubgroups G, if g ∈ C.val then (a C : ℂ) else 0) := by
      simp only [hcast, mul_one]
    _ = ∑ C : CyclicSubgroups G, (a C : ℂ) *
        ∑ g : G, if g ∈ C.val then f g else 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp [mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C _
      congr 1
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) f

end DukePrimeDegree

end OAI
