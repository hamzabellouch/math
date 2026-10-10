import OAI.Combinatorics.HoneycombChords.YangBaxterDefinitions
import Lean.Elab.Tactic.Omega

namespace OAI

/-! Spin conservation for the honeycomb Yang–Baxter numerator and its triple products. -/

namespace CriticalHoneycomb.Transfer.YangBaxter
open scoped BigOperators

lemma numerator_eq_zero_of_sum_ne (C A S x y ii : ℂ) (p q : Fin 3 × Fin 3)
    (h : p.1.val + p.2.val ≠ q.1.val + q.2.val) :
    numerator C A S x y ii p q = 0 := by
  unfold numerator
  split <;> simp_all

lemma leftComponent_eq_zero_of_sum_ne (C A S x y z w ii : ℂ)
    (a b c d e f : Fin 3) (h : a.val + b.val + c.val ≠ d.val + e.val + f.val) :
    leftComponent C A S x y z w ii a b c d e f = 0 := by
  classical
  unfold leftComponent
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  by_cases h₁ : a.val + b.val = j.val + k.val
  · by_cases h₂ : j.val + c.val = d.val + l.val
    · have h₃ : k.val + l.val ≠ e.val + f.val := by omega
      rw [numerator_eq_zero_of_sum_ne C A S z w ii (k, l) (e, f) h₃, mul_zero]
    · rw [numerator_eq_zero_of_sum_ne C A S x y ii (j, c) (d, l) h₂, mul_zero, zero_mul]
  · rw [numerator_eq_zero_of_sum_ne C A S (x*w-y*z) (y*w+x*z) ii (a, b) (j, k) h₁, zero_mul, zero_mul]

lemma rightComponent_eq_zero_of_sum_ne (C A S x y z w ii : ℂ)
    (a b c d e f : Fin 3) (h : a.val + b.val + c.val ≠ d.val + e.val + f.val) :
    rightComponent C A S x y z w ii a b c d e f = 0 := by
  classical
  unfold rightComponent
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  by_cases h₁ : b.val + c.val = k.val + l.val
  · by_cases h₂ : a.val + l.val = j.val + f.val
    · have h₃ : j.val + k.val ≠ d.val + e.val := by omega
      rw [numerator_eq_zero_of_sum_ne C A S (x*w-y*z) (y*w+x*z) ii (j, k) (d, e) h₃, mul_zero]
    · rw [numerator_eq_zero_of_sum_ne C A S x y ii (a, l) (j, f) h₂, mul_zero, zero_mul]
  · rw [numerator_eq_zero_of_sum_ne C A S z w ii (b, c) (k, l) h₁, zero_mul, zero_mul]

end CriticalHoneycomb.Transfer.YangBaxter

end OAI
