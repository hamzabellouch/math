import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.FiniteStage
import OAI.Combinatorics.MatchingCount.Algorithm.RationalScale
import OAI.Combinatorics.MatchingCount.Algorithm.RationalStart

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance finiteTrialLawSourceLabelDecidableEq (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance finiteTrialLawSourceBagEdgeFintype (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _

omit [Nontrivial (Fin G.n)] in
lemma ScaleState.cap {j K : ℕ} (s : ScaleState G j) (hj : j≤K) (a b : Fin G.n) (hab : a≠b) :
    BottleneckAlgorithm.edge s.activity a b≤(4:ℚ)^K := by
  have h:=s.toReal.cap hj a b hab
  rw [←s.activity_cast] at h
  have he : ((BottleneckAlgorithm.edge s.activity a b:ℚ):ℝ)=edgeActivity (fun a b=>(s.activity a b:ℝ)) a b := by
    unfold BottleneckAlgorithm.edge edgeActivity
    split_ifs <;> rfl
  rw [←he] at h
  exact_mod_cast h

noncomputable def ScaleState.runLaw (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    Law (SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K) where
  mass := RationalSource.finiteSourceLaw s.activity s.activity_pos p.K
    (Enlargement.sourceD (V:=Fin G.n) p.K) (1000*p.K*p.S)
    (sourceD_one p.K) Fintype.card_pos (s.cap hj) p.q_pos
    (RationalSource.startMatching s.activity p.K p.even) (1/(1000*p.K*p.S))
  nonneg := RationalSource.finiteSourceLaw_nonneg _ _ _ _ _ _ _ _ _ _ _
  total := RationalSource.finiteSourceLaw_sum _ _ _ _ _ _ _ _ _ _ _

noncomputable def ScaleState.sampleLaw (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    Law (Fin p.S → SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K) := (s.runLaw p hj).iid p.S

theorem ScaleState.sampleLaw_budget (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    (s.sampleLaw p hj).event
      (fun x=>¬StageGood (fun a b=>(s.activity a b:ℝ)) (fun a b=>(s.nextActivity a b:ℝ)) p.K p.sigma x)
      <13/(1000*p.K) := by
  have h:=RationalSource.finite_source_stage_budget s.activity s.activity_pos
    (fun a b=>(s.nextActivity a b:ℝ))
    (fun a b=>by exact_mod_cast (s.nextActivity_pos a b).le)
    (fun a b _=>by have h:=(s.toReal.cooling a b).2; rw [←s.activity_cast,←s.nextActivity_cast] at h; exact h)
    (by rw [s.activity_cast]; exact s.toReal.partition_pos p.even)
    p.K p.K p.S p.K_pos p.S_pos p.sigma p.sigma_pos.le (by simpa using p.S_bound)
    (s.cap hj) p.q_pos (RationalSource.startMatching s.activity p.K p.even)
  convert h using 1
  unfold ScaleState.sampleLaw ScaleState.runLaw Law.event Law.iid Variation.event
  rfl
end MatchingFPRAS.FiniteTrial

end OAI
