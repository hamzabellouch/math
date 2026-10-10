import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.GuardProbability
import OAI.Combinatorics.MatchingCount.Algorithm.TreeGeneratedUpdate

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma generatedSourceSample_support {n : ℕ} [Nontrivial (Fin n)]
    (he : Even n) (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0<w a b) (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge w a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin n) K) k)
    (mb : BagEdge (RationalSource.bags w K)→Fin km→Bool) :
    0<sourceLaw (fun a b=>(w a b:ℝ)) K D ((RationalSource.sourceMarkedEquiv w K).symm
      (generatedSourceSample he w hw K D hD hu ft fq hq bits mb)) := by
  let x:=generatedSourceSample he w hw K D hD hu ft fq hq bits mb
  have hs:=RationalSource.source_draw_support w hw K D km hD
    (fun _ : Unit=>x.1) ((),mb)
  exact hs

lemma generated_certificate_zero {G : GraphInput} [Nontrivial (Fin G.n)]
    (he : Even G.n) {j : ℕ} (s : FiniteTrial.ScaleState G j) (hZ : Z G=0)
    (K D : ℕ) (hD : 0<D)
    (hu : ∀ a b,a≠b→BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K)
    (ft fq : List Bool) (hq : 0<fq.length) {k r km : ℕ}
    (bits : Fin r→ScanBits (SourceVertex (Fin G.n) K) k)
    (mb : BagEdge (RationalSource.bags s.activity K)→Fin km→Bool) :
    RationalSource.observableD s.activity s.certificateActivity K
      (generatedSourceSample he s.activity s.activity_pos K D hD hu ft fq hq bits mb)=0 := by
  let x:=generatedSourceSample he s.activity s.activity_pos K D hD hu ft fq hq bits mb
  let a:=(RationalSource.sourceMarkedEquiv s.activity K).symm x
  have hs:=generatedSourceSample_support he s.activity s.activity_pos K D hD hu ft fq hq bits mb
  have hc:=s.toReal.certificate_zero (K:=K) he hZ D
  rw [←s.activity_cast,←s.certificateActivity_cast] at hc
  have hh:=hc a hs
  have hv:=RationalSource.observableD_cast s.activity s.certificateActivity K a
  simp only [a,Equiv.apply_symm_apply] at hv
  rw [←hv] at hh
  exact_mod_cast hh
end MatchingFPRAS.ExecutableSource

end OAI
