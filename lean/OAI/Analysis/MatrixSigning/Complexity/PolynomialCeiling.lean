import Mathlib
import OAI.Analysis.MatrixSigning.Realization.RatFieldsRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFamilies

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

lemma ratNumToNat_cost : ∃ p : NaturalPolynomial,∀q,
    ratNumToNat.cost q≤p.eval (ratCode q).length+6*q.num.toNat := by
  have : PolyTime ratLE := by
    refine ⟨⟨5*X+2048*(X+1)^2+8,?_⟩⟩
    intro input
    have hinput : (ratCode input.1).length+(ratCode input.2).length ≤
        (prodCode ratCode ratCode input).length := by rw [prodCode_length];omega
    have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hinput 1) 2
    have hleft := le_prodCode_left (ea:=ratCode) (eb:=ratCode) input
    change CompareRoutine.ticks input.1 input.2≤5*(prodCode ratCode ratCode input).length+
      2048*((prodCode ratCode ratCode input).length+1)^2+8
    simp only [CompareRoutine.ticks,CompareRoutine.encode,KS.W29.polynomialFuel,List.length_append]
    simp only [ratCode] at *
    omega
  let cmp := ((constant ratCode ratCode 0).le (identity ratCode)).both (identity ratCode)
  have : PolyTime cmp := by dsimp [cmp,Realizes.le];infer_instance
  have : PolyTime wordTail := ⟨⟨1,fun _ => le_rfl⟩⟩
  have : PolyTime ratNumBinary := by unfold ratNumBinary ratFields;infer_instance
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=cmp)
  obtain ⟨r,hr⟩ := PolyTime.bound (r:=ratNumBinary)
  refine ⟨p+5*r+5*X+20,?_⟩
  intro q
  have hcost := hp q
  have hn := hr q
  have ho := ratNumBinary.output_length q
  have hz : (natCode 0).length=0 := rfl
  have hc : (conditional (ratNumBinary.then binaryToNat) (constant ratCode natCode 0)).cost
      (decide (0≤q),q) ≤ 5*r.eval (ratCode q).length+5*(ratCode q).length+20+6*q.num.toNat := by
    change 5+(if decide (0≤q) then ratNumBinary.cost q+(6*KS.W01.intPayload q.num+4*(binaryNatCode (KS.W01.intPayload q.num)).length+4)
      else (ratCode q).length+1+((natCode 0).length+1))+1≤_
    by_cases hq : 0≤q
    · have he : KS.W01.intPayload q.num=q.num.toNat := by
        have hnum := Rat.num_nonneg.mpr hq
        cases hh : q.num with
        | ofNat n => rfl
        | negSucc n => rw [hh] at hnum;omega
      simp only [hq,decide_true,↓reduceIte,he]
      change (binaryNatCode (KS.W01.intPayload q.num)).length≤_ at ho
      rw [he] at ho
      omega
    · simp only [hq,decide_false,Bool.false_eq_true,↓reduceIte,hz]
      omega
  unfold ratNumToNat
  rw [Realizes.congr_cost]
  change cmp.cost q+(conditional (ratNumBinary.then binaryToNat) (constant ratCode natCode 0)).cost (decide (0≤q),q)≤p.eval (ratCode q).length+5*r.eval (ratCode q).length+5*(ratCode q).length+20+6*q.num.toNat
  omega

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_ratNumToNat (a : ι → ℚ) (ha : IsPoly L (fun i => (ratCode (a i)).length))
    (hn : IsPoly L (fun i => (a i).num.toNat)) : RunsPoly L ratNumToNat a := by
  obtain ⟨p,hp⟩ := ratNumToNat_cost
  exact ⟨ha,((ha.eval p).add ((isPoly_const L 6).mul hn)).mono (fun i => hp (a i))⟩
lemma runsPoly_ratCeil (a : ι → ℚ) (ha : IsPoly L (fun i => (ratCode (a i)).length))
    (hn : IsPoly L (fun i => ⌈a i⌉₊)) : RunsPoly L ratCeil a := by
  unfold ratCeil
  apply RunsPoly.congr
  have : PolyTime (ratOp .sub) := by
    refine ⟨⟨5*X+6000000*(X+1)^3+6,?_⟩⟩
    intro input
    have hlength := RoutineLength.output_length
      (KS.W13.ExpressionMachine.binaryArithmetic_spec .sub input.1 input.2 [] []) 10
    have houtput : (ratCode (KS.W13.ExpressionMachine.BinaryOp.sub.eval input.1 input.2)).length≤
        KS.W13.ExpressionMachine.binaryBudget input.1 input.2 := by
      simpa [KS.W13.ExpressionMachine.registers] using hlength
    have hinput : (ratCode input.1).length+(ratCode input.2).length ≤
        (prodCode ratCode ratCode input).length := by rw [prodCode_length];omega
    have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hinput 1) 3
    have hleft := le_prodCode_left (ea:=ratCode) (eb:=ratCode) input
    change ArithmeticRoutine.ticks .sub input.1 input.2≤5*(prodCode ratCode ratCode input).length+
      6000000*((prodCode ratCode ratCode input).length+1)^3+6
    simp only [ArithmeticRoutine.ticks,ArithmeticRoutine.encode,
      KS.W13.ExpressionMachine.binaryBudget,KS.W01.ratLength] at houtput ⊢
    simp only [ratCode] at *
    omega
  have : PolyTime ratFloor := by
    refine ⟨⟨192*(X+1)^2+2,?_⟩⟩
    intro input
    have hlength := RoutineLength.output_length (KS.W20.FloorRationalMachine.polynomial_spec input) 5
    have houtput : (ratCode (⌊input⌋ : ℚ)).length≤64*((ratCode input).length+1)^2 := by
      simpa [KS.W20.FloorRationalMachine.state,KS.W19.SignedFloorMachine.«stacks»,
        KS.W29.polynomialFuel] using hlength
    change FloorCleanRoutine.ticks input≤192*((ratCode input).length+1)^2+2
    simp only [FloorCleanRoutine.ticks,KS.W29.polynomialFuel,FloorCleanRoutine.encode]
    simp only [ratCode] at *
    omega
  let pre := ((identity ratCode).neg.then ratFloor).neg
  have : PolyTime pre := by
    dsimp only [pre, Realizes.neg, Realizes.sub]
    refine @poly_congr _ _ _ _ _ _ _ _ ?_
    refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · infer_instance
      · refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
        · refine @poly_congr _ _ _ _ _ _ _ _ ?_
          refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
          · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_ <;> infer_instance
          · assumption
        · assumption
    · assumption
  have hp := RunsPoly.of_poly pre a ha
  apply hp.then
  apply runsPoly_ratNumToNat _ hp.output
  simpa only [id_eq,Int.floor_neg,Int.cast_neg,neg_neg,Rat.num_intCast,Int.ceil_toNat] using hn
end CurrentKS.Realization

end OAI
