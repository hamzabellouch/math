import Mathlib
import OAI.Computability.QuantumFactoring.RetentionCircuit
import OAI.Computability.QuantumFactoring.StaticMajorantResources

namespace OAI



section

namespace ExactQuantumFactoring.OrderTrial.Expressions
variable {v : ℕ→Type*} {d Q B j t : ∀ n,NatExpr (v n)} {f : ℕ→ℕ}
lemma lambdaE_poly (hf : PolyBound f) (hd : NatExprPoly d) :
    RatExprPoly (fun n=>lambdaE (f n) (d n)) := by
  have hh := coveringPow_poly hd hf
  unfold lambdaE
  expr_poly
lemma coefficientE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>coefficientE (f n) (Q n) (B n) (d n) (j n)) := by
  have hh := lambdaE_poly hf hd
  have hs := majorantSumE_poly hQ hB hd hj
  have hc : NatExprPoly (fun n=>NatExpr.const (2^(10*f n)) : ∀ n,NatExpr (v n)) :=
    NatExprPoly.const ((PolyBound.const 10).mul hf).twoPowSize
  unfold coefficientE
  expr_poly
lemma remainderE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>remainderE (f n) (Q n) (B n) (d n) (j n)) :=
  (lambdaE_poly hf hd).sub ((coefficientE_poly hf hQ hB hd hj).mul (majorantSumE_poly hQ hB hd hj))
lemma discrepancyE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) (ht : NatExprPoly t) :
    RatExprPoly (fun n=>discrepancyE (f n) (Q n) (B n) (d n) (j n) (t n)) := by
  have hm := majorantE_poly hQ hB hd hj ((hj.mul ht).mod hd)
  have hp := probability_poly hQ hd hj ht
  have hc := coefficientE_poly hf hQ hB hd hj
  unfold discrepancyE
  expr_poly
lemma thirdRetentionE_poly (hf : PolyBound f) (hQ : NatExprPoly Q) (hB : NatExprPoly B)
    (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>thirdRetentionE (f n) (Q n) (B n) (d n) (j n)) := by
  have hr := remainderE_poly hf hQ hB hd hj
  unfold thirdRetentionE
  expr_poly
lemma firstE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>firstE (f n) (d n) (j n)) := by
  apply coefficientE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
lemma secondE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j)
    (ht : NatExprPoly t) : RatExprPoly (fun n=>secondE (f n) (d n) (j n) (t n)) := by
  apply discrepancyE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj ht
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
lemma lastE_poly (hf : PolyBound f) (hd : NatExprPoly d) (hj : NatExprPoly j) :
    RatExprPoly (fun n=>lastE (f n) (d n) (j n)) := by
  apply thirdRetentionE_poly hf _ (NatExprPoly.const hf.twoPowSize) hd hj
  apply NatExprPoly.const
  simpa only [←pow_mul] using (hf.mul (PolyBound.const 16)).twoPowSize
end ExactQuantumFactoring.OrderTrial.Expressions

namespace ExactQuantumFactoring
lemma thresholdExpr_poly {v : ℕ→Type*} {T : ℕ→ℕ} {p : ∀ n,RatExpr (v n)}
    {c : ∀ n,NatExpr (v n)} (hT : PolyBound T) (hp : RatExprPoly p) (hc : NatExprPoly c) :
    NatExprPoly (fun n=>thresholdExpr (T n) (p n) (c n)) := by
  have hh : NatExprPoly (fun n=>NatExpr.const (2^(T n)) : ∀ n,NatExpr (v n)) :=
    NatExprPoly.const hT.twoPowSize
  unfold thresholdExpr
  expr_poly
end ExactQuantumFactoring

end



end OAI
