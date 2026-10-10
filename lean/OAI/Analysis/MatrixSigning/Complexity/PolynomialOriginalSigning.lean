import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceRun
import OAI.Analysis.MatrixSigning.Realization.OriginalSignRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOriginalFields

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

lemma originalFace_good (x : Input) (hx : Admissible x) (hn : originalCount x≠0) :
    (originalFace x).GoodAtoms := by
  have h := RationalInput.normalized_input_properties x hx hn
  exact ⟨RationalInput.dimension_ne x hx hn,hn,h.1,h.2.1,h.2.2.1,h.2.2.2⟩

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_originalNormalizedSigns (a : ι → Input)
    (ha : IsPoly L (fun i => (originalCode (a i)).length))
    (hx : ∀i,Admissible (a i)) (hn : ∀i,originalCount (a i)≠0) :
    RunsPoly L originalNormalizedSigns a := by
  unfold originalNormalizedSigns
  apply RunsPoly.then_with (RunsPoly.of_poly originalFaceRealizes a ha)
  intro hi
  exact runsPoly_normalizedRun _ hi (fun i => originalFace_good (a i) (hx i) (hn i))

lemma runsPoly_originalExtendedSigns (a : ι → Input)
    (ha : IsPoly L (fun i => (originalCode (a i)).length))
    (hx : ∀i,Admissible (a i)) (hn : ∀i,originalCount (a i)≠0) :
    RunsPoly L originalExtendedSigns a := by
  unfold originalExtendedSigns
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both
  · exact RunsPoly.of_poly _ a ha
  · exact (RunsPoly.of_poly _ a ha).both (runsPoly_originalNormalizedSigns a ha hx hn)

lemma runsPoly_originalOutputBit (a : ι → (Σ x : Input,Fin x.N))
    (ha : IsPoly L (fun i => (finFamilyCode originalCode Input.N (a i)).length))
    (hx : ∀i,Admissible (a i).1) (hn : ∀i,originalCount (a i).1≠0) :
    RunsPoly L originalOutputBit a := by
  have hp := RunsPoly.of_poly (familyFirst (ea:=originalCode) (n:=Input.N)) a ha
  have hs := hp.then (runsPoly_originalExtendedSigns _ hp.output hx hn)
  have hi := RunsPoly.of_poly (familyIndex (ea:=originalCode) (n:=Input.N)) a ha
  have hv := (hi.both hs).then_poly (getD ratCode 0)
  have hm := (RunsPoly.of_poly originalOrientation a ha).mul hv
  have hc := RunsPoly.of_poly (constant (finFamilyCode originalCode Input.N) ratCode 1) a ha
  unfold originalOutputBit Realizes.eq
  apply RunsPoly.congr
  apply RunsPoly.congr
  apply RunsPoly.ite
  · exact (hm.both hc).then_poly _
  · exact (hc.both hm).then_poly _
  · exact RunsPoly.of_poly _ a ha

lemma runsPoly_originalSigningFramed (a : ι → Input)
    (ha : IsPoly L (fun i => (originalCode (a i)).length))
    (hx : ∀i,Admissible (a i)) : RunsPoly L originalSigningFramed a := by
  have hb := RunsPoly.of_poly (originalCountRealizes.then natIsZero) a ha
  have ht := RunsPoly.of_poly (((constant originalCode boolCode true).both originalN).then (replicateList boolCode)) a ha
  have hs : RunsPoly (fun i : {i // originalCount (a i)≠0} => L i.val)
      (originalOutputBit.tabulateFin originalN) (fun i => a i.val) := by
    have hw := ha.reindex (fun i : {i // originalCount (a i)≠0} => i.val)
    apply runsPoly_tabulateFin_family _ _ _ hw
    exact runsPoly_originalOutputBit _ (isPoly_finFamily originalN _ hw)
      (fun i => hx i.1.val) (fun i => i.1.property)
  have hc : IsPoly L (fun i => if originalCount (a i)=0 then
      (((constant originalCode boolCode true).both originalN).then (replicateList boolCode)).cost (a i)
      else (originalOutputBit.tabulateFin originalN).cost (a i)) := by
    exact isPoly_dite (ht.cost.reindex (fun i : {i // originalCount (a i)=0} => i.val)) hs.cost
  unfold originalSigningFramed
  apply RunsPoly.congr
  apply hb.ite_on
  simpa only [decide_eq_true_eq] using hc
end CurrentKS.Realization

end

end OAI
