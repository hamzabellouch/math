import Mathlib
import OAI.Computability.QuantumFactoring.NodeStateBounds
import OAI.Computability.QuantumFactoring.PolyAt
import OAI.Computability.QuantumFactoring.PreparationPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BitArithmetic
namespace PreparationPolynomial
variable {α : Sort*} {len s w a b c : α→ℕ}
lemma cyclicMulBound_poly (hs : PolyAt len s) (hw : PolyAt len w)
    (ha : PolyAt len a) (hb : PolyAt len b) (hc : PolyAt len c) :
    PolyAt len (fun x=>cyclicMulBound (s x) (w x) (a x) (b x) (c x)) := by
  unfold cyclicMulBound
  have hwp:=hw.add (PolyAt.const len 1)
  exact (hs.mul hw).mul (hw.add (hs.mul ((((((ha.add hb).add ((PolyAt.const len 2).mul hc)).add
    (((((PolyAt.const len 1224).mul hw).mul hw).add ((PolyAt.const len 143).mul hw)).add (PolyAt.const len 12))).add
    ((PolyAt.const len 216).mul (hwp.pow 2))).add ((PolyAt.const len 142).mul hwp)).add (PolyAt.const len 15))))
lemma cyclicAddBound_poly (hs : PolyAt len s) (hw : PolyAt len w)
    (ha : PolyAt len a) (hb : PolyAt len b) (hc : PolyAt len c) :
    PolyAt len (fun x=>cyclicAddBound (s x) (w x) (a x) (b x) (c x)) := by
  unfold cyclicAddBound
  have hwp:=hw.add (PolyAt.const len 1)
  exact (hs.mul hw).mul ((((((ha.add hb).add hc).add ((PolyAt.const len 216).mul (hwp.pow 2))).add
    ((PolyAt.const len 142).mul hwp)).add (PolyAt.const len 15)))
lemma cyclicStepBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>cyclicStepBound (s x) (w x)) := by
  have h0:=PolyAt.const len 0
  have hm:=cyclicMulBound_poly hs hw h0 h0 h0
  exact ((cyclicMulBound_poly hs hw hm h0 h0).add hm).add ((PolyAt.const len 7).mul (hs.mul hw))
lemma cyclicTestBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>cyclicTestBound (s x) (w x)) := by
  have h0:=PolyAt.const len 0
  have hsw:=(hs.mul hw).mul hw
  have hstep:=hw.mul (cyclicStepBound_poly hs hw)
  exact (((((cyclicAddBound_poly hs hw hsw hsw h0).add hsw).add hstep).add
    (cyclicAddBound_poly hs hw (((PolyAt.const len 2).mul hsw).add hstep) hsw h0)).add
      ((PolyAt.const len 96).mul (hs.mul hw))).add (PolyAt.const len 21)
lemma rootWidth_poly : PolyBound rootWidth := by unfold rootWidth;poly_fast
lemma perfectCheckBound_poly : PolyBound perfectCheckBound := by
  have hn:=PolyBound.id
  have hr:=rootWidth_poly
  have hb:=((((PolyBound.const 90).mul hr).mul hr).add ((PolyBound.const 14).mul hr)).add (PolyBound.const 6)
  exact ((((PolyBound.const 147).mul hr).add (PolyBound.const 31)).add
    (hn.mul ((((PolyBound.const 230).mul hr).add (PolyBound.const 21)).add (hn.mul hb)))).add (hn.mul hb)
lemma aksBranchBound_poly : PolyBound (fun n=>aksBranchBound n (n^8) (rootWidth n)) := by
  have hn:=PolyBound.id
  have hr:=rootWidth_poly
  have hc : PolyBound (fun n=>cyclicTestBound (n^8) (rootWidth n)) :=
    cyclicTestBound_poly ((PolyAt.self (id : ℕ→ℕ)).pow 8) hr
  have hbase:=(((((PolyBound.const 216).mul hr).mul hr).add ((PolyBound.const 154).mul hr)).add
    (PolyBound.const 27)).add (PolyBound.const 1)
  have hstep:=(((((PolyBound.const 3672).mul hr).mul hr).add ((PolyBound.const 436).mul hr)).add (PolyBound.const 36))
  have hord:=((hn.pow 2).mul ((((PolyBound.const 100).mul hr).add (PolyBound.const 23)).add (hr.mul hstep))).add (PolyBound.const 1)
  have hdiv:=(((PolyBound.const 8).mul (hn.pow 8)).mul
    (((((PolyBound.const 216).mul hr).mul hr).add ((PolyBound.const 203).mul hr)).add (PolyBound.const 38))).add (PolyBound.const 1)
  have hcon:=(((PolyBound.const 8).mul (hn.pow 8)).mul (hc.add (PolyBound.const 1))).add (PolyBound.const 1)
  exact (((hbase.add hord).add hdiv).add hcon).add (PolyBound.const 3)
lemma primalityBound_poly : PolyBound primalityBound := by
  have hn:=PolyBound.id
  exact (((hn.add (PolyBound.const 1)).mul (perfectCheckBound_poly.add (PolyBound.const 4))).add
    (PolyBound.const 1)).add (PolyBound.const 1) |>.add
      ((((hn.pow 8).add (PolyBound.const 1)).mul (aksBranchBound_poly.add (PolyBound.const 4))).add (PolyBound.const 1)) |>.add (PolyBound.const 1)
lemma primeBound_poly : PolyBound NodeCircuit.primeBound :=
  ((((PolyBound.const 49).mul PolyBound.id).add (PolyBound.const 10)).add rootWidth_poly).add primalityBound_poly
lemma guardBound_poly : PolyBound NodeCircuit.guardBound :=
  (((((PolyBound.const 216).mul PolyBound.id).mul PolyBound.id).add
    ((PolyBound.const 250).mul PolyBound.id)).add (PolyBound.const 45))
lemma quotientBound_poly : PolyBound NodeCircuit.quotientBound :=
  (((((PolyBound.const 216).mul PolyBound.id).mul PolyBound.id).add
    ((PolyBound.const 56).mul PolyBound.id)).add (PolyBound.const 6))
lemma nodeStepBound_poly (hs : PolyAt len s) (hw : PolyAt len w) :
    PolyAt len (fun x=>NodeStateCircuit.stepBound (s x) (w x)) := by
  have hp:=PolyAt.comp primeBound_poly hw
  have hg:=PolyAt.comp guardBound_poly hw
  have hq:=PolyAt.comp quotientBound_poly hw
  have hn : PolyAt len (fun x=>NodeCircuit.nextBound (s x) (w x)) := by
    unfold NodeCircuit.nextBound NodeCircuit.splitBound
    poly_at
  have ho : PolyAt len (fun x=>NodeStateCircuit.outputBound (s x) (w x)) := by
    unfold NodeStateCircuit.outputBound
    poly_at
  unfold NodeStateCircuit.stepBound
  poly_at
end PreparationPolynomial
end ExactQuantumFactoring

end



end OAI
