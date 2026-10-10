import Mathlib
import OAI.Computability.QuantumFactoring.RawTrialDecoder
import OAI.Computability.QuantumFactoring.RecoveryPolynomial
import OAI.Computability.QuantumFactoring.TrialNetworkPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace OrderTrial
lemma rawMode_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawMode r).net.count=r.net.count := by
  simp only [rawMode,leftNet,count_comp,count_select,Nat.add_zero]
lemma rawSample_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawSample r).net.count=r.net.count := by
  simp only [rawSample,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawGuesses_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawGuesses r).net.count=r.net.count := by
  simp only [rawGuesses,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawDen_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawDen r).net.count=r.net.count := by
  simp only [rawDen,rawGuesses_count,leftNet,count_comp,count_select,Nat.add_zero]
lemma rawNum_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawNum r).net.count=r.net.count := by
  simp only [rawNum,rawGuesses_count,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawResidue_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawResidue r).net.count=r.net.count := by
  simp only [rawResidue,rawGuesses_count,leftNet,rightNet,count_comp,count_select,Nat.add_zero]
lemma rawCoin_count {k u s n : ℕ} (r : BooleanNetwork k (rawWidth u s n)) :
    (rawCoin r).net.count=r.net.count := by
  simp only [rawCoin,rawGuesses_count,rightNet,count_comp,count_select,Nat.add_zero]
lemma decodeSteps_poly : PolyBound (fun n=>decodeSteps (OrderSlots.sampleExponent n)) := by
  unfold decodeSteps
  have:=PreparationPolynomial.sampleExponent
  poly_fast
lemma decodeWidth_poly : PolyBound (fun n=>decodeWidth n (OrderSlots.sampleExponent n) n) := by
  have hs:=PreparationPolynomial.sampleExponent
  have ht:=decodeSteps_poly
  have hcf : PolyBound (fun n=>cfWidth (OrderSlots.sampleExponent n+3) (decodeSteps (OrderSlots.sampleExponent n))) := by
    unfold cfWidth;poly_fast
  have hr:=PreparationPolynomial.retentionBits
  unfold decodeWidth;poly_fast

variable {α : Type*} {len k : α→ℕ}
  {r : ∀x,BooleanNetwork (k x) (rawWidth (len x) (OrderSlots.sampleExponent (len x)) (len x))}
lemma recoveredPairNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>recoveredPairNet (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hs:=PolyAt.ofPoly PreparationPolynomial.sampleExponent len
  have hrs : NetworkAt len (fun x=>rawSample (r x)) := by
    simpa only [NetworkAt,rawSample_count] using hr
  have hy : NetworkAt len (fun x=>(rawSample (r x)).comp (sampleYNet (len x) (OrderSlots.sampleExponent (len x)+2))) :=
    hrs.comp (NetworkAt.select _)
  exact recoveryNet_poly (NetworkAt.wordConstant _ hw) (NetworkAt.wordConstant _ hw)
    (hy.toWidth (hs.add (PolyAt.const len 2)) hw) hw (PolyAt.ofPoly decodeSteps_poly len)
lemma trialPairNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialPairNet (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hn:=PolyAt.self len
  have hm : NetworkAt len (fun x=>rawMode (r x)) := by
    simpa only [NetworkAt,rawMode_count] using hr
  have hd : NetworkAt len (fun x=>rawDen (r x)) := by
    simpa only [NetworkAt,rawDen_count] using hr
  have hj : NetworkAt len (fun x=>rawNum (r x)) := by
    simpa only [NetworkAt,rawNum_count] using hr
  exact ((hm.toWidth (PolyAt.const len 2) hw).wordLt (NetworkAt.wordConstant _ hw) hw).wordMux
    (recoveredPairNet_poly hr) ((hd.toWidth hn hw).pair (hj.toWidth hn hw)) (hw.add hw)
lemma trialDenNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialDenNet (r x)) :=
  (trialPairNet_poly hr).comp (NetworkAt.select _)
lemma trialNumNet_poly (hr : NetworkAt len r) : NetworkAt len (fun x=>trialNumNet (r x)) :=
  (trialPairNet_poly hr).comp (NetworkAt.select _)

lemma samplerSelectedNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    {z : ∀x,BooleanNetwork (k x) (OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2))}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hz : NetworkAt len z) :
    NetworkAt len (fun x=>samplerSelectedNet (a x) (m x) (z x)) := by
  have hs := PolyAt.ofPoly PreparationPolynomial.sampleExponent len
  have hscratch := PolyAt.ofPoly PreparationPolynomial.sampleScratch len
  have hwidth := PolyAt.ofPoly PreparationPolynomial.sampleWidth len
  have hwork : PolyAt len (fun x=>Triangular.work (OrderSlots.sampleExponent (len x)+2)) := by
    unfold Triangular.work;poly_at
  have hrest : PolyAt len (fun x=>3*(OrderSlots.sampleExponent (len x)+2)+
      Triangular.work (OrderSlots.sampleExponent (len x)+2)+
      OrderSample.scratch (len x) (OrderSlots.sampleExponent (len x)+2)+
      98*OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2)+21) := by
    exact (((((PolyAt.const len 3).mul (hs.add (PolyAt.const len 2))).add hwork).add hscratch).add
      ((PolyAt.const len 98).mul hwidth)).add (PolyAt.const len 21)
  apply NetworkAt.of_le (bound:=fun x=>3*(z x).net.count+(a x).net.count+(m x).net.count+
      (3*(OrderSlots.sampleExponent (len x)+2)+Triangular.work (OrderSlots.sampleExponent (len x)+2)+
      OrderSample.scratch (len x) (OrderSlots.sampleExponent (len x)+2)+
      98*OrderSample.width (len x) (OrderSlots.sampleExponent (len x)+2)+21))
  · exact (((PolyAt.const len 3).mul hz).add ha |>.add hm).add hrest
  · intro x
    have h:=samplerSelectedNet_count (a x) (m x) (z x)
    omega
lemma rawAcceptNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>rawAcceptNet (a x) (m x) (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  have hn:=PolyAt.self len
  have hmode : NetworkAt len (fun x=>rawMode (r x)) := by
    simpa only [NetworkAt,rawMode_count] using hr
  have ht : NetworkAt len (fun x=>rawResidue (r x)) := by
    simpa only [NetworkAt,rawResidue_count] using hr
  have hc : NetworkAt len (fun x=>rawCoin (r x)) := by
    simpa only [NetworkAt,rawCoin_count] using hr
  have hs : NetworkAt len (fun x=>rawSample (r x)) := by
    simpa only [NetworkAt,rawSample_count] using hr
  exact trialAcceptOn_poly (ha.toWidth hn hw) (hm.toWidth hn hw)
    (hmode.toWidth (PolyAt.const len 2) hw) (trialDenNet_poly hr) (trialNumNet_poly hr)
    (ht.toWidth hn hw) (hc.toWidth (PolyAt.ofPoly PreparationPolynomial.retentionBits len) hw)
    (samplerSelectedNet_poly ha hm hs) hw
lemma trialValueNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>trialValueNet (a x) (m x) (r x)) := by
  have hw:=PolyAt.ofPoly decodeWidth_poly len
  exact (rawAcceptNet_poly ha hm hr).wordMux (trialDenNet_poly hr) (NetworkAt.wordConstant _ hw) hw
lemma trialSmallValueNet_poly {a m : ∀x,BooleanNetwork (k x) (len x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hr : NetworkAt len r) :
    NetworkAt len (fun x=>trialSmallValueNet (a x) (m x) (r x)) :=
  (trialValueNet_poly ha hm hr).comp
    (NetworkAt.resizeWord (PolyAt.ofPoly decodeWidth_poly len) (PolyAt.self len))
end OrderTrial
end ExactQuantumFactoring

end


end OAI
