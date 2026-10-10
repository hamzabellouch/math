import OAI.NumberTheory.DirichletL.Reflection.RowTail
import OAI.NumberTheory.DirichletL.Reflection.ShapeWeights

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem original_family_whole_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,CubicSieve.Admissible P) →
    ∀ (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖literalWholeRow F K hK S jF Pset D s hc W θ X r aw-
        (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
          ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
            literalDyadicRow F K hK S jF Pset D s hc u i W θ X
              (fun K => r K*shapeArgument (primaryGenerator K))
              (fun P => aw P*shapeArgument (primaryGenerator P))‖≤
        (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*Pset.card*
          (C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
            T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_row_tail
    (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod hPad θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let E := C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
    T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹
  have hb (v : Eisˣ) :
      ‖(∑' i,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa)-
        ∑ i∈J,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa‖≤Pset.card*E :=
    hbound F K hK S jF Pset D s hc hN hbase hchar hj hprod v θ X T QK QP rr aa hX hT hQK hQP hKr hPr
      (by simpa only [rr,row_shape_weight_norm r K hK] using hr)
      (fun P hp => by simpa only [aa,slot_shape_weight_norm aw P (hPad P hp)] using haw P hp)
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  rw [literalWholeRow_eq_dyadic F K hK S jF Pset D s hc hN hbase hchar hj hprod W lo hi hlo hWs hW θ X hX r aw]
  rw [←mul_sub,norm_mul, norm_mul,stratumShapeFactor_frozen_norm]
  simp only [tsum_fintype]
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*
        ∑ v : Eisˣ,‖(∑' i,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa)-
          ∑ i∈J,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*∑ _v : Eisˣ,Pset.card*E := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hb v)) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; dsimp only [E]; ring
end
end SevenEighths.InverseReflectedPhase

end OAI
