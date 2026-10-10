import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.RationalEstimator

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport Switching

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
def ScaleState.Balanced (hn : 2≤G.n) (s : ScaleState G j) : Prop := s.toReal.Balanced hn
omit [Nontrivial (Fin G.n)] in
lemma initial_balanced (hn : 2≤G.n) (he : Even G.n) : (initialScaleState G hn).Balanced hn :=
  Trial.initial_balanced G hn he
noncomputable def stageData (p : Trial.Parameters G) (hj : j≤p.K) (s : ScaleState G j)
    (hs : s.Balanced p.hn) : StageData G.n p.K p.K where
  hn:=p.hn
  w a b:=(s.activity a b:ℝ)
  next a b:=(s.nextActivity a b:ℝ)
  positive a b:=by exact_mod_cast s.activity_pos a b
  next_positive a b:=by exact_mod_cast s.nextActivity_pos a b
  partition_positive:=by rw [s.activity_cast]; exact s.toReal.partition_pos p.even
  lower:=by rw [s.activity_cast]; exact hs.1
  upper:=by rw [s.activity_cast]; exact hs.2
  cool_lower a b _:=by
    have h:=(s.toReal.cooling a b).1
    rw [←s.activity_cast,←s.nextActivity_cast] at h
    exact h
  cool_upper a b _:=by
    have h:=(s.toReal.cooling a b).2
    rw [←s.activity_cast,←s.nextActivity_cast] at h
    exact h
  cap:=by rw [s.activity_cast]; exact s.toReal.cap hj
  stages:=p.K_pos
  epsilon:=p.epsilon
  epsilon_positive:=p.epsilon_real_pos
  epsilon_lt_one:=p.epsilon_real_lt_one

theorem successful_update (p : Trial.Parameters G) (hj : j≤p.K) (s : ScaleState G j)
    (hs : s.Balanced p.hn) (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K)
    (hx : StageGood (fun a b=>(s.activity a b:ℝ)) (fun a b=>(s.nextActivity a b:ℝ)) p.K p.sigma x) :
    (s.update p.hn (RationalSource.sourceMarkedEquiv s.activity p.K ∘ x)).Balanced p.hn ∧
      |(s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity p.K ∘ x):ℝ)/
        (partition (Trial.raw G (j+1)) ∅/partition (Trial.raw G j) ∅)-1|≤(p.epsilon:ℝ)/(100*p.K) := by
  let c:=stageData p hj s hs
  let obs : EmpiricalData c:=empiricalData c x hx
  have hh:=actual_successful_stage c obs
  dsimp only at hh
  let y:=RationalSource.sourceMarkedEquiv s.activity p.K ∘ x
  have hm : (fun a b=>(s.matrix y a b:ℝ))=Enlargement.estimateMatrix (Enlargement.sourceD (V:=Fin G.n) p.K) obs.dbar obs.zbar := by
    rw [s.matrix_cast,sourceD_eq]
    rfl
  have hv : (fun i=>(s.updateVector p.hn y i:ℝ))=
      RealStage.scalingTrace c.hn (Enlargement.estimateMatrix (Enlargement.sourceD (V:=Fin G.n) p.K) obs.dbar obs.zbar) G.n := by
    funext i
    rw [ScaleState.updateVector,Counting.scalingTrace_cast,hm]
  constructor
  · unfold ScaleState.Balanced Trial.ScaleState.Balanced
    rw [←ScaleState.activity_cast,ScaleState.update_activity]
    have ha : (fun a b=>((s.nextActivity a b*s.updateVector p.hn y a*s.updateVector p.hn y b:ℚ):ℝ))=
        (fun a b=>c.next a b*(RealStage.scalingTrace c.hn (Enlargement.estimateMatrix
          (Enlargement.sourceD (V:=Fin G.n) p.K) obs.dbar obs.zbar) G.n a)*
          (RealStage.scalingTrace c.hn (Enlargement.estimateMatrix
          (Enlargement.sourceD (V:=Fin G.n) p.K) obs.dbar obs.zbar) G.n b)) := by
      funext a z
      simp only [Rat.cast_mul,congrFun hv]
      rfl
    rw [ha]
    exact ⟨fun i=>(hh.2.1 i).1,fun i=>(hh.2.1 i).2⟩
  · rw [s.ratioEstimate_cast]
    have hr : partition c.next ∅/partition c.w ∅=
        partition (Trial.raw G (j+1)) ∅/partition (Trial.raw G j) ∅ := by
      change partition (fun a b=>(s.nextActivity a b:ℝ)) ∅/partition (fun a b=>(s.activity a b:ℝ)) ∅=_
      rw [s.nextActivity_cast,s.activity_cast,s.toReal.ratio]
    rw [←hr]
    exact hh.2.2

lemma ScaleState.ratioEstimate_nonneg (s : ScaleState G j)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    0 ≤ s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x) := by
  have h : (0:ℝ)≤(s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x):ℝ) := by
    rw [s.ratioEstimate_cast]
    unfold RealStage.ratioEstimate
    split_ifs with h
    · apply div_nonneg _ h.le
      unfold Enlargement.sampleAverage
      apply div_nonneg _ (Nat.cast_nonneg S)
      apply sum_nonneg
      intro i _
      exact (observableD_range_off (fun a b=>(s.activity a b:ℝ)) (fun a b=>(s.nextActivity a b:ℝ))
        (fun a b=>by exact_mod_cast s.activity_pos a b)
        (fun a b=>by exact_mod_cast (s.nextActivity_pos a b).le)
        (fun a b _=>by have h:=(s.toReal.cooling a b).2; rw [←s.activity_cast,←s.nextActivity_cast] at h; exact h) K (x i)).1
    · norm_num
  exact_mod_cast h
end MatchingFPRAS.FiniteTrial

end OAI
