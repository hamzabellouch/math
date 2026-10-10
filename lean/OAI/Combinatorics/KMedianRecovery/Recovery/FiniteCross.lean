import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FiniteContinuation

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing PhaseCountCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

def run (loc : Fin d → X) (distance : X → Fin d → ℚ) (F Q : Finset X)
    (v lam : ℚ) (q n k : ℕ) (copy spare : X → X) (H G : List X)
    (T U : List (List X)) : Result X :=
  let complete := FiniteLabelContinuation.complete loc distance F v ((1+v^2)^q) lam
  let S := CanonicalMergeRefinement.regularChain F (F.sort (·≤·)) complete Q copy spare H G
  scan F Q k (FiniteLabelContinuation.continuation loc distance F v lam (q+1) n) U H T S

variable [PseudoMetricSpace X]
 theorem run_spec (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hmetric : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset X)
    (v lam : ℚ) (eta : ℝ) (q n k : ℕ) (copy spare : X → X)
    (hv : (0:ℝ)<(v:ℝ)) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i ≤ (lam:ℝ))
    (hc : ∀ i∈F,copy i∉F∪B) (hd : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy i))
    (hs : ∀ i∈F,spare i∉F∪PhaseMergePath.pool F B copy)
    (he : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (spare i))
    (H G : List X) (T U : List (List X))
    (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H)
    (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G)
    (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hT : Runs loc F B (Q∪H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q∪G.toFinset) v lam (q+1) n U)
    (hbr : Sandwich k (finalCount F Q H T) (finalCount F Q G U)) :
    (run loc distance F Q v lam q n k copy spare H G T U).Correct loc F
      (PhaseMergePath.pool F (PhaseMergePath.pool F B copy) spare) Q v lam eta q n k := by
  let B' := PhaseMergePath.pool F (PhaseMergePath.pool F B copy) spare
  have hB : B⊆B' := (PhaseMergePath.subset_pool F B copy).trans (PhaseMergePath.subset_pool ..)
  let complete := FiniteLabelContinuation.complete loc distance F v ((1+v^2)^q) lam
  have hz : (((1+v^2)^q:ℚ):ℝ)=(1+(v:ℝ)^2)^q := by push_cast; rfl
  have hcomp : CanonicalMergePath.CorrectCompletion loc F v ((1+(v:ℝ)^2)^q) lam complete := by
    have hh := FiniteLabelContinuation.correct_completion loc distance hmetric F v ((1+v^2)^q) lam
      hv hvsmall (by rw [hz]; positivity)
    simpa only [hz] using hh
  obtain ⟨_,hp⟩ := CanonicalMergeRefinement.regularChain_spec loc F B Q (F.sort (·≤·)) copy spare
    v ((1+(v:ℝ)^2)^q) lam eta complete hcomp hv hvsmall (by positivity) hlam heta
    (fun i hi=>by simpa only [Finset.mem_sort] using hi) hQ hdis hrow hc hd hs he H G hH hG hHr hGr
  apply scan_spec loc F B' Q v lam eta q n k _ _
    (hQ.trans (Finset.union_subset_union_right hB))
    (CanonicalMergeCrossing.disjoint_pool F _ spare (CanonicalMergeCrossing.disjoint_pool F B copy hdis hc) hs)
    (by linarith) hlam hp T U hbr (hT.mono_free hB) (hU.mono_free hB)
  intro R hR
  exact FiniteLabelContinuation.continuation_spec loc distance hmetric F B' R v lam hv hvsmall (q+1) n hR

end MetricKMedianRecovery.FiniteLabelCrossing

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

inductive Plan (X : Type*) where
  | free (i f : X)
  | paid (C T : List X) (i : X)

def Plan.root : Plan X → X
  | .free i _ => i
  | .paid _ _ i => i

def Plan.common (H : List X) : Plan X → List X
  | .free _ _ => H
  | .paid C T _ => C++T

def Plan.small (T U : List (List X)) : Plan X → List (List X)
  | .free _ _ => U
  | .paid _ _ _ => T

def Plan.large (T U : List (List X)) : Plan X → List (List X)
  | .free _ _ => T
  | .paid _ _ _ => U

def accepts (distance : X → Fin d → ℚ) (F : Finset X) (H G : List X) : Plan X → Prop
  | .free i f => i∈F ∧ f∉F ∧ G=H++[f] ∧ ∀ j,distance i j=distance f j
  | .paid C T i => i∈F ∧ H=C++i::T ∧ G=C++T

instance (distance : X → Fin d → ℚ) (F : Finset X) (H G : List X) (J : Plan X) :
    Decidable (accepts distance F H G J) := by cases J <;> dsimp only [accepts] <;> infer_instance

def candidates (R H G : List X) : List (Plan X) :=
  (R.flatMap (fun i=>G.map (Plan.free i))) ++ ((cuts H).map (fun p=>Plan.paid p.1 p.2.2 p.2.1))

def view (distance : X → Fin d → ℚ) (F : Finset X) (R H G : List X) : Option (Plan X) :=
  (candidates R H G).find? (fun J=>decide (accepts distance F H G J))

omit [DecidableEq X] in
lemma candidates_length (R H G : List X) : (candidates R H G).length=R.length*G.length+H.length := by
  simp only [candidates,List.length_append,List.length_map,cuts_length]
  induction R with
  | nil => simp
  | cons i R ih => simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_cons, Nat.succ_mul]; omega

lemma view_sound (distance : X → Fin d → ℚ) (F : Finset X) (R H G : List X) (J : Plan X)
    (h : view distance F R H G=some J) : accepts distance F H G J :=
  of_decide_eq_true (List.find?_some (p := fun J=>decide (accepts distance F H G J)) h)

variable [PseudoMetricSpace X]
lemma view_exists (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hd : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F B : Finset X) (R H G : List X)
    (hR : ∀ i∈F,i∈R) (hdis : Disjoint F B) (h : LengthEdit loc F B H G) :
    ∃ J,view distance F R H G=some J := by
  have hex : ∃ J∈candidates R H G,accepts distance F H G J := by
    cases h with
    | freeAppend H i f hi hf hco =>
      refine ⟨.free i f,?_,hi,fun he=>Finset.disjoint_left.mp hdis he hf,rfl,?_⟩
      · apply List.mem_append_left
        apply List.mem_flatMap.mpr
        refine ⟨i,hR i hi,List.mem_map.mpr ⟨f,?_,rfl⟩⟩
        exact List.mem_append_right _ (List.mem_cons_self ..)
      · intro j
        apply Rat.cast_injective (α:=ℝ)
        rw [hd,hd,dist_comm i,dist_comm f]
        exact hco j
    | paidDelete C T i hi =>
      refine ⟨.paid C T i,?_,hi,rfl,rfl⟩
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨(C,i,T),mem_cuts.mpr rfl,rfl⟩
  have hn : view distance F R H G≠none := by
    intro hn
    obtain ⟨J,hJ,hacc⟩ := hex
    exact List.find?_eq_none.mp hn J hJ (decide_eq_true hacc)
  exact Option.ne_none_iff_exists'.mp hn

end MetricKMedianRecovery.CanonicalLengthView

end OAI
