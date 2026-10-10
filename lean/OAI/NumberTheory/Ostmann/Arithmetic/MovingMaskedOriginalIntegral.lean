import OAI.NumberTheory.Ostmann.Arithmetic.MovingMaskedEnergyIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateExternalMultiplier
import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedDiagonalEnergy

namespace OAI

/-! # The mixed integral of the actual masked coefficient square -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingMaskedTemplateKernel_original_integral {I : Type}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (outside : List ℕ) (μ : ℕ → P → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n (4 + r) m → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (H : ℝ) (u v a b center : ℝ) :
    mixedExternalAverage ν (V n) u v a b center
      (fun s x z y => (φ (z - H) : ℂ) * (φ (y - H) : ℂ) *
        (movingMaskedTemplateKernel P hP outside μ childBound pivotBound V
          (movingOriginalLeaf Subtype.val q (fun _ => f) g Dq S ψ X lo hi) φ G n r m greg
          x ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s : ℝ)) =
    movingWeightedDiagonalEnergy q Subtype.val outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n (movingTemplateSmall n (4 + r) m)
      (bulkSlotLeaves n m (movingTemplateBulk n (4 + r) m))
      (fun s => movingTemplateExternalMultiplier P hP n (4 + r) m
        (movingRestoredActive n r m) outside greg s φ H H false) u v a b center := by
  unfold mixedExternalAverage movingWeightedDiagonalEnergy
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro Xg hXg
  split_ifs
  · congr 1
    unfold complexIntegerInterval
    apply Finset.sum_congr rfl
    intro piv hpiv
    congr 1
    have hp : (0 : ℝ) < piv := by
      exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hpiv).1
    have hq : (0 : ℝ) < Xg := by
      exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hXg).1
    simp only [Real.exp_log hp, Real.exp_log hq, Nat.floor_natCast,
      movingMaskedTemplateKernel, movingTemplateExternalMultiplier,
      movingTemplateCoefficient, giantOuterWeight, positiveLogCutoff,
      ite_eq_left hp, ite_eq_left hq, Bool.false_eq_true, ite_false, mul_one, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  · rfl

end Ostmann

end OAI
