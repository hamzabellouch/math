import Mathlib
import OAI.Computability.QuantumFactoring.TrialExpressionResources

namespace OAI



section

namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : ℕ → Type*} {d Q B j : ∀ n, NatExpr (v n)} {η : ∀ n, RatExpr (v n)}
lemma rampPoly_poly (q a : ℤ) :
    PolySchemaPoly (fun _ => rampPoly q a : ∀ n, PolyExpr (v n)) := by
  unfold rampPoly
  split <;> schema_poly
lemma rampLin_poly (q a : ℤ) :
    PolySchemaPoly (fun _ => rampLin q a : ∀ n, PolyExpr (v n)) := by
  unfold rampLin
  split <;> schema_poly
lemma splineRePoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => splineRePoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampPoly_poly (v:=v) q 0
  have h2 := rampPoly_poly (v:=v) q 2
  have h4 := rampPoly_poly (v:=v) q 4
  unfold splineRePoly
  schema_poly
lemma splineImPoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => splineImPoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampPoly_poly (v:=v) q (-1)
  have h2 := rampPoly_poly (v:=v) q 1
  have h4 := rampPoly_poly (v:=v) q 3
  have h5 := rampPoly_poly (v:=v) q 5
  unfold splineImPoly
  schema_poly
lemma phaseRePoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => phaseRePoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampLin_poly (v:=v) q 0
  have h2 := rampLin_poly (v:=v) q 2
  have h4 := rampLin_poly (v:=v) q 4
  unfold phaseRePoly
  schema_poly
lemma phaseImPoly_poly (q : ℤ) :
    PolySchemaPoly (fun _ => phaseImPoly q : ∀ n, PolyExpr (v n)) := by
  have h0 := rampLin_poly (v:=v) q (-1)
  have h2 := rampLin_poly (v:=v) q 1
  have h4 := rampLin_poly (v:=v) q 3
  have h5 := rampLin_poly (v:=v) q 5
  unfold phaseImPoly
  schema_poly
lemma massZero_poly (hd : NatExprPoly d) (q : ℤ) :
    PolySchemaPoly (fun n => massZero (d n) q) :=
  ((integralZero_poly hd (phaseRePoly_poly q)).pow 2).add
    ((integralZero_poly hd (phaseImPoly_poly q)).pow 2)
lemma massSlope_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q₀ q₁ : ℤ) :
    PolySchemaPoly (fun n => massSlope (d n) (η n) q₀ q₁) :=
  ((integralSlope_poly hd hη (splineRePoly_poly q₀) (splineRePoly_poly q₁)).pow 2).add
    ((integralSlope_poly hd hη (splineImPoly_poly q₀) (splineImPoly_poly q₁)).pow 2)
lemma massCoeff_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q₀ q₁ : ℤ) (k : ℕ) :
    RatExprPoly (fun n => massCoeff (d n) (η n) q₀ q₁ k) :=
  hη.ifEq (RatExprPoly.constant 0) ((massZero_poly hd q₀).coeffs k)
    ((massSlope_poly hd hη q₀ q₁).coeffs k)
lemma low_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q : ℤ×ℤ) :
    NatExprPoly (fun n => low (d n) (η n) q) := by
  unfold low
  apply NatExprPoly.max <;> expr_poly
lemma high_poly (hd : NatExprPoly d) (hη : RatExprPoly η) (q : ℤ×ℤ) :
    NatExprPoly (fun n => high (d n) (η n) q) := by
  unfold high
  apply NatExprPoly.min hd
  apply NatExprPoly.min <;> expr_poly
lemma pieceSum_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) (q : ℤ×ℤ) :
    RatExprPoly (fun n => pieceSum (Q n) (B n) (d n) (j n) q) := by
  have he := error_poly hQ hd hj
  have hl := low_poly hd he q
  have hh := high_poly hd he q
  have hs := fiveTerm_poly
    (fun k => rounded_poly (roundingDen_poly hQ hB) (massCoeff_poly hd he q.1 q.2 k)) hl hh
  unfold pieceSum
  exact hs.add ((RatExprPoly.ofNat (hh.sub hl)).mul
    ((RatExprPoly.constant 64).div (RatExprPoly.ofNat hQ)))
lemma majorantSumE_poly (hQ : NatExprPoly Q) (hB : NatExprPoly B) (hd : NatExprPoly d)
    (hj : NatExprPoly j) :
    RatExprPoly (fun n => majorantSumE (Q n) (B n) (d n) (j n)) :=
  (RatExprPoly.sumList (fun q => pieceSum_poly hQ hB hd hj q) quarterList).div
    (RatExprPoly.constant 2)
end ExactQuantumFactoring.OrderTrial.Expressions

end



end OAI
