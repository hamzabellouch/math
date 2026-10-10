import OAI.NumberTheory.Ostmann.Tree.SamePairFiber

namespace OAI

/-! # Conditional second moment of an untouched actual quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance untouchedFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem sum_samePairMajorant_eq {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (y : ZMod p) :
    (∑ ρ : MulChar (ZMod p) ℂ,
      samePairMajorant (fieldPairCoefficientMoment g) (fieldPairMoment h) ρ y) =
      differenceMajorant (fieldPairMoment g) (fieldPairMoment h) y := by
  unfold samePairMajorant differenceMajorant differenceMoment
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_mul, sum_squareCharacterMass, sum_fieldPairCoefficientMoment]

theorem rationalQuartet_fiber_secondMoment_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (Q : RationalQuartetData (ZMod p)ˣ)
    (XL XR P : (ZMod p)ˣ) :
    (Fintype.card (TreeLeafFiber (ZMod p)ˣ 2 P) : ℝ)⁻¹ *
      (∑ m : TreeLeafFiber (ZMod p)ˣ 2 P,
        ‖rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true)) m.1‖ ^ 2) ≤
      8 * differenceMajorant (fieldPairMoment g) (fieldPairMoment g)
        (rationalTreeArgument Q.s (Q.CL * Q.CR) D XL XR P) := by
  rw [mean_samePairLeftFiber P (fun m =>
    ‖rationalTreeAmplitude g D Q.tree XL XR ((false, true), (false, true)) m‖ ^ 2)]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (MulChar (ZMod p) ℂ)))
    (fun ρ _ => rationalQuartet_samePair_left_held_bound g D Q XL XR P ρ)
  rw [← Finset.mul_sum] at h
  conv_rhs at h => rw [← Finset.mul_sum, sum_samePairMajorant_eq]
  apply le_of_eq_of_le _ h
  symm
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact mellin_parseval (fun r => rationalTreeAmplitude g D Q.tree XL XR
    ((false, true), (false, true)) (samePairLeftLeaves P a b r))

theorem untouchedQuartetMajorant_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ y : (ZMod p)ˣ,
      differenceMajorant (fieldPairMoment g) (fieldPairMoment g) y) /
        (Fintype.card (ZMod p)ˣ : ℝ) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 := by
  apply (mean_differenceMajorant_le _ _
    (fieldPairMoment_nonneg g) (fieldPairMoment_nonneg g)).trans
  have h := fieldPairMoment_mean_le g hg henergy
  have h0 : 0 ≤ (∑ d : ZMod p, fieldPairMoment g d) / (Fintype.card (ZMod p)ˣ : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun d _ => fieldPairMoment_nonneg g d) (Nat.cast_nonneg _)
  convert mul_le_mul h h h0 (sq_nonneg _) using 1
  ring

end Ostmann

end OAI
