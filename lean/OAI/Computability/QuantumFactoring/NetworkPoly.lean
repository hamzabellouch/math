import Mathlib
import OAI.Computability.QuantumFactoring.RetentionExpressionResources
import OAI.Computability.QuantumFactoring.NetworkPolyResources

namespace OAI

section
namespace ExactQuantumFactoring
open BooleanNetwork

namespace NetworkPoly
variable {a b c : ℕ→ℕ}
lemma select (h : ∀ n,Fin (b n)→Fin (a n)) : NetworkPoly (fun n=>BooleanNetwork.select (h n)) := by
  simpa only [NetworkPoly,count_select] using PolyBound.const 0
lemma comp {f : ∀ n,BooleanNetwork (a n) (b n)} {g : ∀ n,BooleanNetwork (b n) (c n)}
    (hf : NetworkPoly f) (hg : NetworkPoly g) : NetworkPoly (fun n=>(f n).comp (g n)) := by
  simpa only [NetworkPoly,count_comp] using PolyBound.add hf hg
lemma pair {f : ∀ n,BooleanNetwork (a n) (b n)} {g : ∀ n,BooleanNetwork (a n) (c n)}
    (hf : NetworkPoly f) (hg : NetworkPoly g) : NetworkPoly (fun n=>(f n).pair (g n)) := by
  simpa only [NetworkPoly,count_pair] using PolyBound.add hf hg
lemma rewire {f : ∀ n,BooleanNetwork (a n) (b n)} (hf : NetworkPoly f)
    (h : ∀ n,Fin (c n)→Fin (b n)) : NetworkPoly (fun n=>(f n).rewire (h n)) := by
  simpa only [NetworkPoly,count_rewire] using hf
lemma constant (h : ℕ→Bool) : NetworkPoly (fun n=>BooleanNetwork.constant (n:=a n) (h n)) := by
  simpa only [NetworkPoly,count_constant] using PolyBound.const 1
lemma bnot {f : ∀ n,BooleanNetwork (a n) 1} (hf : NetworkPoly f) :
    NetworkPoly (fun n=>(f n).bnot) := by
  simpa only [NetworkPoly,count_bnot] using (PolyBound.add hf (PolyBound.const 1))
lemma band {f g : ∀ n,BooleanNetwork (a n) 1} (hf : NetworkPoly f) (hg : NetworkPoly g) :
    NetworkPoly (fun n=>(f n).band (g n)) := by
  simpa only [NetworkPoly,count_band] using ((PolyBound.add hf hg).add (PolyBound.const 1))
lemma bor {f g : ∀ n,BooleanNetwork (a n) 1} (hf : NetworkPoly f) (hg : NetworkPoly g) :
    NetworkPoly (fun n=>(f n).bor (g n)) := by
  simpa only [NetworkPoly,count_bor] using ((PolyBound.add hf hg).add (PolyBound.const 4))
lemma of_le {f : ∀ n,BooleanNetwork (a n) (b n)} {c : ℕ→ℕ} (hc : PolyBound c)
    (h : ∀ n,(f n).net.count≤c n) : NetworkPoly f := hc.of_le h
end NetworkPoly

namespace NatExprPoly
variable {v : ℕ→Type*} {e : ∀ n,NatExpr (v n)} {a b : ℕ→ℕ}
  {vars : ∀ n,v n→BooleanNetwork (a n) (b n)}
lemma sharedCost (he : NatExprPoly e) : PolyBound (fun n=>(e n).sharedCost) :=
  PolyBound.of_le he (fun n=>(e n).sharedCost_le_weight)
lemma operationBound {f : ℕ→ℕ} (hf : PolyBound f) :
    PolyBound (fun n=>NatExpr.operationBound (f n)) := by
  unfold NatExpr.operationBound
  poly_bound
lemma template (he : NatExprPoly e) (hb : PolyBound b) (hv : NetworkVarsPoly vars) :
    NetworkPoly (fun n=>(e n).template (vars n)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyBound (fun n=>p.eval n):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkPoly.of_le (he.sharedCost.mul (((operationBound hw).add hc).add hw))
  exact fun n=>(e n).template_shared_count (vars n) (hp n)
lemma isOne (he : NatExprPoly e) (hb : PolyBound b) (hv : NetworkVarsPoly vars) :
    NetworkPoly (fun n=>(e n).isOne (vars n)) := by
  obtain ⟨p,hp⟩:=hv
  have hc : PolyBound (fun n=>p.eval n):=⟨p,fun _=>le_rfl⟩
  have hw:=he.templateWidth hb
  apply NetworkPoly.of_le
    (((he.sharedCost.mul (((operationBound hw).add hc).add hw)).add
      ((PolyBound.const 100).mul hw)).add (PolyBound.const 21))
  exact fun n=>(e n).isOne_shared_count (vars n) (hp n)
end NatExprPoly

lemma retentionNet_poly {v : ℕ→Type*} {a b T : ℕ→ℕ} {p : ∀ n,RatExpr (v n)}
    {c : ∀ n,NatExpr (v n)} {vars : ∀ n,v n→BooleanNetwork (a n) (b n)}
    (hT : PolyBound T) (hp : RatExprPoly p) (hc : NatExprPoly c) (hb : PolyBound b)
    (hv : NetworkVarsPoly vars) :
    NetworkPoly (fun n=>retentionNet (T n) (p n) (c n) (vars n)) :=
  (thresholdExpr_poly hT hp hc).isOne hb hv
end ExactQuantumFactoring

end



end OAI
