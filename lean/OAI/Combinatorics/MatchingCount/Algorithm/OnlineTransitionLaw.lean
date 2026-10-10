import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.FiniteTrialLaw
import OAI.Combinatorics.MatchingCount.Algorithm.OutputLengthBound
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineStage
import OAI.Combinatorics.MatchingCount.Probability.OnlineLawBridge
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineLaw

namespace OAI

namespace MatchingFPRAS.OnlineStage
open PhysicalStream TreeTyped ExecutableSource NumericLadder TreeFraction ExecutableScaling
open UnitRefresh Transport Enlargement TreeTyped.Numbered ExecutableAdaptive Variation

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {n : ℕ} [Nontrivial (Fin n)]
variable (w : Fin n→Fin n→ℚ) (K D m : ℕ)
noncomputable local instance : Fintype (BagPM (RationalSource.bags w K)) := Fintype.ofFinite _
noncomputable local instance : Fintype (RationalSource.Marked w K) := Fintype.ofFinite _
noncomputable local instance : Fintype (SourceMarked (fun a b=>(w a b:ℝ)) K) := Fintype.ofFinite _
noncomputable def realRawDraw (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0<copies (n:=n) K D) (he : Even n) (η : ℚ) :
    Raw w K D m η→SourceMarked (fun a b=>(w a b:ℝ)) K :=
  (RationalSource.sourceMarkedEquiv w K).symm ∘ rawDraw w K D m hw hD hu hq he η
lemma realRawDraw_law (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0<copies (n:=n) K D) (he : Even n) (η : ℚ) :
    imageLaw (realRawDraw w K D m hw hD hu hq he η)=
      RationalSource.finiteSourceLaw w hw K D m hD Fintype.card_pos hu hq
        (RationalSource.startMatching w K he) η := by
  unfold realRawDraw
  rw [imageLaw_output_equiv,rawDraw_law]
  rfl
lemma realRawDraw_inverse (hw : ∀ a b,0<w a b) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0<copies (n:=n) K D) (he : Even n) (η : ℚ) (b : Raw w K D m η) :
    RationalSource.sourceMarkedEquiv w K (realRawDraw w K D m hw hD hu hq he η b)=
      rawDraw w K D m hw hD hu hq he η b :=
  (RationalSource.sourceMarkedEquiv w K).apply_symm_apply _

lemma finiteLaw_parameters (hw : ∀ a b,0<w a b) (D' : ℕ) (hDD : D=D')
    (hD : 0<D) (hD' : 0<D')
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (hq : 0<copies (n:=n) K D) (hq' : 0<copies (n:=n) K D')
    (M : BagPM (RationalSource.bags w K)) (η η' : ℚ) (hη : η=η') :
    RationalSource.finiteSourceLaw w hw K D m hD Fintype.card_pos hu hq M η=
      RationalSource.finiteSourceLaw w hw K D' m hD' Fintype.card_pos hu hq' M η' := by
  subst D'; subst η'; rfl

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable abbrev denominator (p : Trial.Parameters G) := 1000*p.K*p.S
noncomputable def fixedRequest {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j) : OnlineSample.Request :=
  (((choiceWidth s.activity p.K (FiniteTrial.sourceD (G:=G) p.K) (denominator p) (1/denominator p),p.N),
      scansCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K) (denominator p)),
    (markWidth s.activity p.K (1/denominator p),
      List.ofFn (fun i=>index (orderedEnum (BagEdge (RationalSource.bags s.activity p.K)) i))))
noncomputable def fixedData {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j) : SparseStageData :=
  data s p.K (FiniteTrial.sourceD (G:=G) p.K)
    (List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
    (List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
noncomputable def transition {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j) :
    Experiment (Fraction×Vector) := execute (fixedData p s,(p.S,fixedRequest p s))

lemma transition_mean {j : ℕ} (p : Trial.Parameters G) (hj : j≤p.K)
    (s : FiniteTrial.ScaleState G j) (h : Fraction×Vector→ℚ) :
    (transition p s).mean h=
      qaverage (fun bits : Fin (FiniteTrial.stageBits p)→Bool=>
        let x := RationalSource.sourceMarkedEquiv s.activity p.K ∘ s.drawStage p hj bits
        h (repr (s.ratioEstimate x),vectorRep (s.update p.hn x).scale)) := by
  have hD : 0<FiniteTrial.sourceD (G:=G) p.K := by
    rw [FiniteTrial.sourceD_eq]
    exact Enlargement.sourceD_one p.K
  have hq : 0<copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K) := by
    simpa only [copies,vertexCount,FiniteTrial.sourceD_eq,Trial.Parameters.q,Trial.Parameters.N,Trial.Parameters.D] using p.q_pos
  unfold transition fixedData fixedRequest
  simp only [Trial.Parameters.N]
  rw [source_mean p.hn p.even s p.K hD (s.cap hj) _ _ (by simpa using hq)]
  let raw := realRawDraw s.activity p.K (FiniteTrial.sourceD (G:=G) p.K) (denominator p)
    s.activity_pos hD (s.cap hj) hq p.even (1/denominator p)
  have hr : imageLaw raw=(s.runLaw p hj).mass := by
    rw [realRawDraw_law]
    dsimp only [FiniteTrial.ScaleState.runLaw]
    apply finiteLaw_parameters
    · exact FiniteTrial.sourceD_eq p.K
    · simp only [denominator,Nat.cast_mul,Nat.cast_ofNat]
  have hp : imageLaw (fun bs : Fin p.S→Raw s.activity p.K (FiniteTrial.sourceD (G:=G) p.K)
      (denominator p) (1/denominator p)=>fun i=>raw (bs i)) = imageLaw (s.drawStage p hj) := by
    rw [imageLaw_componentwise,hr,FiniteTrial.ScaleState.drawStage_law]
    rfl
  have hmean := qaverage_eq_of_imageLaw_eq _ _ hp (fun y=>
    let x:=RationalSource.sourceMarkedEquiv s.activity p.K ∘ y
    h (repr (s.ratioEstimate x),vectorRep (s.update p.hn x).scale))
  apply Eq.trans _ hmean
  apply qaverage_congr
  intro bs
  have hx : (fun i=>generatedSourceSample p.even s.activity s.activity_pos p.K
      (FiniteTrial.sourceD (G:=G) p.K) hD (s.cap hj)
      (List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
      (List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
      (by simpa using hq) (bs i).1 (fun e=>(bs i).2 ((orderedEnum _).symm e))) =
      RationalSource.sourceMarkedEquiv s.activity p.K ∘ (fun i=>raw (bs i)) := by
    funext i
    rw [generated_eq_raw]
    exact (realRawDraw_inverse ..).symm
  rw [hx]
end MatchingFPRAS.OnlineStage

end OAI
