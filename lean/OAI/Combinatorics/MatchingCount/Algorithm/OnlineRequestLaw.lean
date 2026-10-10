import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineRequest
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineTransitionLaw

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling Transport
open UnitRefresh Enlargement TreeTyped.Numbered OnlineStage ExecutableRefresh

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma bitPrecision_inverseNat (R m : ℕ) : bitPrecision R (1/(m:ℚ))=Nat.clog 2 (R*m) := by
  simp [bitPrecision]

variable {G : GraphInput} [Nontrivial (Fin G.n)]
lemma sourceRequest_source {j : ℕ} (p : Trial.Parameters G) (s : FiniteTrial.ScaleState G j) :
    sourceRequest (fixedData p s,p.S)=fixedRequest p s := by
  unfold sourceRequest
  rw [show sourcePrecision (fixedData p s,p.S)=
    (((((Fintype.card (SourceVertex (Fin G.n) p.K)),FiniteTrial.sourceD (G:=G) p.K),
      (p.K,tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K))),denominator p),
      (edgeCount s.activity p.K,labelCount s.activity p.K)) from by
    simpa only [fixedData,denominator,edgeCount,labelCount,List.length_replicate] using
      sourcePrecision_source p.hn s p.K (FiniteTrial.sourceD (G:=G) p.K) p.S
        (List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)
        (List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false)]
  have hc : (sourceTables (sparseBagInput (fixedData p s))).1.length=edgeCount s.activity p.K := by
    unfold fixedData
    rw [sparseBagInput_source,sourceTables_catalog p.hn s.activity
      (fun i j=>(s.activity_pos i j).le) p.K]
    simp only [sourceCatalog,List.length_ofFn]
  simp only [hc,precisionPlan,fixedRequest,choiceWidth,markWidth,bitPrecision_inverseNat]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simp only [index_orderedEnum]
      apply List.ext_getElem
      · simp
      · intro _ _ _
        simp
end MatchingFPRAS.OnlineSchedule

end OAI
