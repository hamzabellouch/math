import OAI.NumberTheory.Ostmann.Arithmetic.MovingSymmetrizedMaskedIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateExternalMultiplier

namespace OAI

/-! # Exact normalization of the original bulk-averaged masked energy -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingTemplateMaskedSymmetrizedEnergy
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (active : MovingRegularSlot n r m → Bool)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v a b center : ℝ) : ℂ :=
  mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
    (‖movingBulkAveragedTemplateCoefficient Subtype.val outside μ childBound pivotBound V F φ G
      n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
      movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal y x z)

theorem movingSymmetrizedMaskedTemplateKernel_original_integral
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (n r m : ℕ) (ν : MovingRegularSlot n (4 + r) m → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (H : ℝ) (u v a b center : ℝ) :
    mixedExternalAverage ν (V n) u v a b center
      (fun s x z y => (φ (z - H) : ℂ) * (φ (y - H) : ℂ) *
        (movingSymmetrizedMaskedTemplateKernel P hP outside μ childBound pivotBound V F φ G
          n r m greg x ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ s : ℝ)) =
    movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
      n (4 + r) m ν (movingRestoredActive n r m) greg H H false u v a b center := by
  unfold movingTemplateMaskedSymmetrizedEnergy mixedExternalAverage
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
      movingSymmetrizedMaskedTemplateKernel, movingTemplateExternalMultiplier,
      giantOuterWeight, positiveLogCutoff, ite_eq_left hp, ite_eq_left hq,
      Bool.false_eq_true, ite_false, mul_one, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  · rfl

theorem movingSymmetrizedMaskedTemplateEnergy_original_interval
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (G : ℕ → ℝ)
    (n r m : ℕ) (Q : MovingRegularSlot n r m → Finset ℕ)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (center : ℝ) :
    let H := G (n + 1)
    let Pg := smoothGiantPrimeRange H
    let I := Finset.Ioc ⌊Real.exp (H - 1)⌋₊ ⌊Real.exp (H + 1)⌋₊
    let ν := movingTemplateRestoredPrior n r m (μ n) (fun i => primeSubsetPrior P (Q i))
    (movingSymmetrizedMaskedTemplateEnergy P Pg I hP outside μ childBound pivotBound V F φ G
      n r m Q greg (fun _ => 1) : ℂ) =
    (Real.exp (smoothGiantLogNormalizer Pg φ H + center) : ℂ) *
      movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
        n (4 + r) m ν (movingRestoredActive n r m) greg H H false
        (H - 1) (H + 1) (H - 1) (H + 1) center := by
  dsimp only
  rw [movingSymmetrizedMaskedTemplateEnergy_interval P hP outside μ childBound pivotBound V
    F φ hout G n r m Q greg center]
  rw [movingSymmetrizedMaskedTemplateKernel_original_integral]

end Ostmann

end OAI
