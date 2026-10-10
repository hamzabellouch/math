import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TokenSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BoundedMultiplicity

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ} {w : ClosedLine h ℓ}

noncomputable local instance fiberTokenTypeDec (w : ClosedLine h ℓ) : DecidableEq (TokenType w) := Classical.decEq _
noncomputable local instance fiberPrimeIndexDec (S : PrimeSystem) : DecidableEq S.Index := Classical.decEq _
noncomputable local instance fiberTokenSlotDec (j : TokenType w → ℕ) : DecidableEq (TokenSlot j) := Classical.decEq _

noncomputable def normalizedFiberWeight (K : ℝ) (u : TokenType w → ℝ)
    (C : Fin ℓ → ℝ) (H τ : ℝ) (f : S.Index → Option (TokenType w)) : ℝ :=
  if unorderedBins (TypeFibers.multiplicity f) C H τ (TypeFibers.unordered f) then
    (K^(pivotEdges (slotShape (TypeFibers.multiplicity f)) (slotCore (TypeFibers.multiplicity f))).card)⁻¹ *
      ∏ p : S.Index, TypeFibers.factor f (fun t p => u t * slotWeight S (t.1=true) p) p
  else 0

lemma unorderedWeight_nonneg (j : TokenType w → ℕ) (u : TokenType w → ℝ) (hu : ∀ t, 0 ≤ u t)
    (U : FactorialAssignments.Unordered (P := S.Index) j) :
    0 ≤ FactorialAssignments.unorderedWeight j (fun t p => u t * slotWeight S (t.1=true) p) U := by
  apply prod_nonneg
  intro t ht
  exact prod_nonneg (fun p _ => mul_nonneg (hu t) (slotWeight_nonneg _ _ _))

theorem normalized_fiber_sum (K τ : ℝ) (hK : 0 < K) (hB : UnorderedTokenBound S K τ)
    (u : TokenType w → ℝ) (hu : ∀ t, 0 ≤ u t)
    (C : Fin ℓ → ℝ) (hC : ∀ e, 0 < C e) (H : ℝ) :
    (∑ f : S.Index → Option (TokenType w), normalizedFiberWeight K u C H τ f) ≤
      ∑ j : TypeFibers.BoundedMultiplicity S.Index (TokenType w),
        tokenFactorialProduct (fun t => (j t).val) S.harmonicCore S.harmonicCenter u := by
  classical
  let W : TypeFibers.FiberCode S.Index (TokenType w) → ℝ := fun z =>
    if unorderedBins (fun t => (z.1 t).val) C H τ z.2 then
      (K^(pivotEdges (slotShape (fun t => (z.1 t).val)) (slotCore (fun t => (z.1 t).val))).card)⁻¹ *
        FactorialAssignments.unorderedWeight (fun t => (z.1 t).val)
          (fun t p => u t * slotWeight S (t.1=true) p) z.2 else 0
  have hW (z : TypeFibers.FiberCode S.Index (TokenType w)) : 0 ≤ W z := by
    unfold W
    split_ifs
    · exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hK.le _)) (unorderedWeight_nonneg _ u hu _)
    · exact le_rfl
  have he (f : S.Index → Option (TokenType w)) : W (TypeFibers.encode f)=normalizedFiberWeight K u C H τ f := by
    unfold W normalizedFiberWeight
    dsimp only [TypeFibers.encode,TypeFibers.boundedMultiplicity]
    rw [TypeFibers.unorderedWeight_eq]
    rfl
  simp_rw [← he]
  apply (TypeFibers.encoded_sum_le W hW).trans
  apply sum_le_sum
  intro j hj
  let J : TokenType w → ℕ := fun t => (j t).val
  let k := (pivotEdges (slotShape J) (slotCore J)).card
  have hbound := hB h ℓ w J C hC H (fun _ => True) u hu
  have hsum : (∑ U : FactorialAssignments.Unordered (P := S.Index) J, W ⟨j,U⟩) =
      (K^k)⁻¹ * unorderedTokenSum S J u C H τ (fun _ => True) := by
    unfold unorderedTokenSum
    rw [mul_sum]
    apply sum_congr rfl
    intro U hU
    simp only [W,true_and,J,k]
    split_ifs <;> simp
  rw [hsum]
  have hm := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (pow_nonneg hK.le k))
  calc
    _ ≤ (K^k)⁻¹ * (K^k * tokenFactorialProduct J S.harmonicCore S.harmonicCenter u) := hm
    _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hK.ne'),one_mul]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
