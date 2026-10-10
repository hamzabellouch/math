import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RecordPacket
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExceptionalCodeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.NormalizedFiberWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ChargePivotAbsorption

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.TaggedPrimeGroups
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

noncomputable local instance globalFiberTokenDec (w : ClosedLine h ℓ) : DecidableEq (TokenType w) := Classical.decEq _
noncomputable local instance globalFiberIndexDec (S : PrimeSystem) : DecidableEq S.Index := Classical.decEq _

namespace RecordPacket
variable {w₀ : ClosedLine h ℓ} {hh : 0 < h} {r : ℕ}
variable {hr₀ : (returnSteps w₀).card=r} {n N : ℕ}

noncomputable def factorialTotal (S : PrimeSystem) (w : ClosedLine h ℓ) (pC pZ : S.Index) : ℝ :=
  ∑ j : TypeFibers.BoundedMultiplicity S.Index (TokenType w),
    tokenFactorialProduct (fun t => (j t).val) S.harmonicCore S.harmonicCenter (tokenWeight w pC pZ)

lemma factorialTotal_nonneg (S : PrimeSystem) (w : ClosedLine h ℓ) (pC pZ : S.Index) :
    0 ≤ factorialTotal S w pC pZ := by
  apply sum_nonneg
  intro j hj
  apply prod_nonneg
  intro t ht
  apply div_nonneg
  · apply pow_nonneg
    apply mul_nonneg
    · unfold tokenMass harmonicCore harmonicCenter
      split_ifs <;> exact sum_nonneg (fun p _ => by positivity)
    · exact tokenWeight_nonneg w pC pZ t
  · exact Nat.cast_nonneg _

noncomputable def exceptionalCost (S : PrimeSystem) (ℓ L n N : ℕ) (C₀ B : ℝ) : ℝ :=
  (∏ i ∈ range (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)),
    ((i:ℝ)+1+∑ p : S.Index, (p:ℝ)⁻¹)) * (3*(ℓ:ℝ)+1)^N

lemma exceptionalCost_nonneg (S : PrimeSystem) (ℓ L n N : ℕ) (C₀ B : ℝ) :
    0 ≤ exceptionalCost S ℓ L n N C₀ B := by
  unfold exceptionalCost
  apply mul_nonneg
  · exact prod_nonneg (fun i _ => by positivity)
  · positivity

lemma chargedCodeWeight_tail (K : ℝ) (pC pZ : S.Index) (m : ListMetadata ℓ L n)
    (x : Fin (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) → Option S.Index)
    (y : Fin N → Option (TaggedShape w₀)) (f : S.Index → Option (TokenType w₀)) :
    chargedCodeWeight (D := D) K pC pZ (m,x,y,f) =
      exceptionalWeight (m,x,y,fun _ => none) * normalizedFiberWeight K (tokenWeight w₀ pC pZ)
        (flatEdge (m,x,y,fun _ => none)) D.H τ f := by
  let z : FlatCode S w₀ C₀ B L n N := (m,x,y,fun _ => none)
  have hE : flatEdge (m,x,y,f)=flatEdge z := rfl
  have hW : exceptionalWeight (m,x,y,f)=exceptionalWeight z := rfl
  unfold chargedCodeWeight flatGate flatWeight flatPivots normalizedFiberWeight
  rw [hE,hW]
  split_ifs <;> simp only [mul_zero]
  · ring

lemma chargedCode_sum_tail (K : ℝ) (hK : 0 < K) (hB : UnorderedTokenBound S K τ)
    (pC pZ : S.Index) (m : ListMetadata ℓ L n)
    (x : Fin (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) → Option S.Index)
    (y : Fin N → Option (TaggedShape w₀)) :
    (∑ f : S.Index → Option (TokenType w₀), chargedCodeWeight (D := D) K pC pZ (m,x,y,f)) ≤
      exceptionalWeight (m,x,y,fun _ => none) * factorialTotal S w₀ pC pZ := by
  let z : FlatCode S w₀ C₀ B L n N := (m,x,y,fun _ => none)
  have he := chargedCodeWeight_tail (D := D) K pC pZ m x y
  simp_rw [he]
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left
    (normalized_fiber_sum K τ hK hB (tokenWeight w₀ pC pZ) (tokenWeight_nonneg w₀ pC pZ)
      (flatEdge z) (flatEdge_pos z) D.H) (exceptionalWeight_nonneg z)

lemma exceptionalCode_sum (m : ListMetadata ℓ L n) :
    (∑ x : Fin (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) → Option S.Index,
      ∑ y : Fin N → Option (TaggedShape w₀), exceptionalWeight (m,x,y,fun _ => none)) ≤
      exceptionalCost S ℓ L n N C₀ B := by
  let : DecidableEq S.Index := fun a b => Subtype.instDecidableEq a b
  exact weighted_tagged_slot_sum (fun p : S.Index => (p:ℝ)⁻¹) (fun p => by positivity)
    (fun p s => localTokenWeight w₀ p (taggedShapeCode w₀ s))
    (fun p s => localTokenWeight_nonneg w₀ p _) (3*(ℓ:ℝ)+1) (by have hℓ : 0 ≤ (ℓ:ℝ) := Nat.cast_nonneg _; linarith)
    (tagged_shape_sum w₀) _ N (exceptionalPick L ⌈C₀*Real.log B⌉₊ n N)

theorem charged_code_sum (K : ℝ) (hK : 0 < K) (hB : UnorderedTokenBound S K τ)
    (pC pZ : S.Index) :
    (∑ c : FlatCode S w₀ C₀ B L n N, chargedCodeWeight (D := D) K pC pZ c) ≤
      (Fintype.card (ListMetadata ℓ L n):ℝ) * exceptionalCost S ℓ L n N C₀ B *
        factorialTotal S w₀ pC pZ := by
  classical
  have hsplit : (∑ c : FlatCode S w₀ C₀ B L n N, chargedCodeWeight (D := D) K pC pZ c) =
      ∑ m : ListMetadata ℓ L n,
        ∑ x : Fin (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) → Option S.Index,
          ∑ y : Fin N → Option (TaggedShape w₀),
            ∑ f : S.Index → Option (TokenType w₀), chargedCodeWeight (D := D) K pC pZ (m,x,y,f) := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro m hm
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro x hx
    rw [Fintype.sum_prod_type]
  rw [hsplit]
  calc
    _ ≤ ∑ m : ListMetadata ℓ L n,
        ∑ x : Fin (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) → Option S.Index,
          ∑ y : Fin N → Option (TaggedShape w₀),
            exceptionalWeight (m,x,y,fun _ => none) * factorialTotal S w₀ pC pZ :=
      sum_le_sum (fun m _ => sum_le_sum (fun x _ => sum_le_sum (fun y _ =>
        chargedCode_sum_tail K hK hB pC pZ m x y)))
    _ = ∑ m : ListMetadata ℓ L n,
        (∑ x : Fin (Fintype.card (ExceptionalCodeSlot L ⌈C₀*Real.log B⌉₊ n N)) → Option S.Index,
          ∑ y : Fin N → Option (TaggedShape w₀), exceptionalWeight (m,x,y,fun _ => none)) *
            factorialTotal S w₀ pC pZ := by simp only [sum_mul]
    _ ≤ ∑ _m : ListMetadata ℓ L n,
        exceptionalCost S ℓ L n N C₀ B * factorialTotal S w₀ pC pZ :=
      sum_le_sum (fun m _ => mul_le_mul_of_nonneg_right (exceptionalCode_sum m)
        (factorialTotal_nonneg S w₀ pC pZ))
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring

end RecordPacket
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
