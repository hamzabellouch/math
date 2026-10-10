import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedUpdate
import OAI.Combinatorics.MatchingCount.Probability.OnlineSampleLaw

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive Variation

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

variable {n : ℕ} [Nontrivial (Fin n)]
variable (w : Fin n→Fin n→ℚ) (K D m : ℕ)
abbrev vertexCount := Fintype.card (SourceVertex (Fin n) K)
abbrev labelCount := Fintype.card (RationalSource.Label w K)
abbrev edgeCount := Fintype.card (BagEdge (RationalSource.bags w K))
abbrev tierCount := Transport.endpoint (vertexCount (n:=n) K) D K Fintype.card_pos
abbrev copies := ladderQ (vertexCount (n:=n) K) D
abbrev scansCount := discreteLadderSteps (vertexCount (n:=n) K) D K (tierCount (n:=n) K D) m
abbrev choiceWidth (η : ℚ) := bitPrecision (scansCount (n:=n) K D m *
  scanErrorNumerator (SourceVertex (Fin n) K) (RationalSource.Label w K) (RationalSource.bags w K)
    (tierCount (n:=n) K D) (copies (n:=n) K D)) η
abbrev markWidth (η : ℚ) := bitPrecision (6*edgeCount w K) η
abbrev Raw (η : ℚ) := OnlineSample.Random (vertexCount (n:=n) K) (choiceWidth w K D m η)
  (scansCount (n:=n) K D m) (edgeCount w K) (markWidth w K η)

def rawEquiv (η : ℚ) :
    ((Fin (scansCount (n:=n) K D m*scanBitCount (vertexCount (n:=n) K) (choiceWidth w K D m η))→Bool) ×
      (BagEdge (RationalSource.bags w K)→Fin (markWidth w K η)→Bool)) ≃ Raw w K D m η :=
  Equiv.prodCongr (runBitsEquiv (SourceVertex (Fin n) K) (choiceWidth w K D m η) (scansCount (n:=n) K D m))
    (Equiv.arrowCongr (orderedEnum (BagEdge (RationalSource.bags w K))).symm (Equiv.refl _))
lemma raw_scan (η : ℚ) (bs : Raw w K D m η) :
    runBitsEquiv (SourceVertex (Fin n) K) (choiceWidth w K D m η) (scansCount (n:=n) K D m)
      ((rawEquiv w K D m η).symm bs).1=bs.1 :=
  congrArg Prod.fst ((rawEquiv w K D m η).apply_symm_apply bs)
lemma raw_marks (η : ℚ) (bs : Raw w K D m η) (e : BagEdge (RationalSource.bags w K)) :
    ((rawEquiv w K D m η).symm bs).2 e=bs.2 ((orderedEnum _).symm e) := rfl
noncomputable def rawDraw (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0<copies (n:=n) K D) (he : Even n) (η : ℚ) : Raw w K D m η→RationalSource.Marked w K :=
  RationalSource.markedSampler w hw K D m hD Fintype.card_pos hu hq
    (RationalSource.startMatching w K he) η ∘ (rawEquiv w K D m η).symm

noncomputable def core (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K) (he : Even n)
    (T q : ℕ) (hq : 0<q) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) : RationalSource.Marked w K :=
  TableMarking.reveal (BagEdge.Incident (bags:=RationalSource.bags w K))
    (ladderRun (RationalSource.bags_adjacent w K hu) (RationalSource.tree_acyclic w K)
      (fun l : RationalSource.Label w K=>l.1.val) (RationalSource.parent w K)
      (RationalSource.bags_ranked w K hu) (RationalSource.bags_nonempty w K)
      (RationalSource.parent_rank w K) hq (RationalSource.bagWeight w K D)
      (RationalSource.startMatching w K he) k r (fun _=>RationalSource.startMatching w K he) bits
      (topSlot T q hq))
    (fun e=>(RationalSource.markingTable w hw K D hD e).draw km (mb e))
lemma generated_eq_core (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K) (he : Even n)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    generatedSourceSample he w hw K D hD hu ft fq hq bits mb=
      core w K D hw hD hu he ft.length fq.length hq bits mb := rfl

lemma generated_eq_raw (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0<copies (n:=n) K D) (he : Even n) (η : ℚ) (bs : Raw w K D m η) :
    generatedSourceSample he w hw K D hD hu
      (List.replicate (tierCount (n:=n) K D) false) (List.replicate (copies (n:=n) K D) false)
      (by simpa only [List.length_replicate] using hq) bs.1
      (fun e=>bs.2 ((orderedEnum (BagEdge (RationalSource.bags w K))).symm e)) =
    rawDraw w K D m hw hD hu hq he η bs := by
  rw [generated_eq_core]
  simp only [List.length_replicate]
  unfold core rawDraw RationalSource.markedSampler TableMarking.draw RationalSource.topSampler
    RationalSource.sampler finiteLadder ladderBitRun
  simp only [Function.comp_apply,raw_scan,raw_marks]

noncomputable local instance : Fintype (BagPM (RationalSource.bags w K)) := Fintype.ofFinite _
noncomputable local instance : Fintype (RationalSource.Marked w K) := Fintype.ofFinite _
lemma rawDraw_law (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0<copies (n:=n) K D) (he : Even n) (η : ℚ) :
    imageLaw (rawDraw w K D m hw hD hu hq he η)=
      RationalSource.markedSamplerLaw w hw K D m hD Fintype.card_pos hu hq
        (RationalSource.startMatching w K he) η := by
  unfold rawDraw RationalSource.markedSamplerLaw
  apply Eq.trans (imageLaw_comp_equiv (rawEquiv w K D m η).symm _)
  exact imageLaw_instances _ _ _
end MatchingFPRAS.OnlineStage

end OAI
