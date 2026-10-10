import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.Clipped

namespace OAI

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Entry (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (i : X) : Prop :=
  i ∉ Q ∧ (i ∈ B ∨ (i ∈ F ∧ ∃ W : Finset X, Q ⊆ W ∧ W ⊆ F ∪ B ∧
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i))

inductive Prefix (loc : D → X) (F B : Finset X) (v z lam eta : ℝ) :
    Finset X → List X → Prop
  | nil (Q) : Prefix loc F B v z lam eta Q []
  | cons {Q : Finset X} {i : X} {H : List X}
      (hi : Entry loc F B Q v z lam eta i)
      (htail : Prefix loc F B v z lam eta (insert i Q) H) :
      Prefix loc F B v z lam eta Q (i::H)

def Maximal (loc : D → X) (F Q : Finset X) (v z lam : ℝ) : Prop :=
  ∀ i ∈ F, i ∉ Q → ¬etaOpenable loc F Q (1-3*v) (1+v^2) v z lam 0 i

def Valid (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X) : Prop :=
  Prefix loc F B v z lam eta Q H ∧ Maximal loc F (Q ∪ H.toFinset) v z lam

end PhaseSequence
end MetricKMedianRecovery
namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive History (loc : D → X) (F B : Finset X) (v lam eta : ℝ) :
    ℕ → Finset X → List (List X) → Prop
  | nil (q Q) : History loc F B v lam eta q Q []
  | cons {q Q H T} (head : PhaseSequence.Valid loc F B Q v ((1+v^2)^q) lam eta H)
      (tail : History loc F B v lam eta (q+1) (Q ∪ H.toFinset) T) :
      History loc F B v lam eta q Q (H::T)

def after (Q : Finset X) : List (List X) → Finset X
  | [] => Q
  | H::T => after (Q ∪ H.toFinset) T

end MetricKMedianRecovery.PhaseHistoryTransfer
namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Regular (F : Finset X) (T : List (List X)) : Prop := ∀ H ∈ T, ∀ i ∈ H, i ∈ F

def Attains (loc : D → X) (F B Q : Finset X) (v lam : ℝ) (q n c : ℕ) : Prop :=
  ∃ T : List (List X), T.length = n ∧ History loc F B v lam 0 q Q T ∧
    Regular F T ∧ ((after Q T) ∩ F).card = c

end MetricKMedianRecovery.PhaseMergeCompletion
namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion OrdinaryProducer

def historyRun {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (List (Fin m))
  | 0,s => (s,[])
  | n+1,s =>
    let r := finish distance F v lam F.card s
    let u := advance distance v r.1
    let t := historyRun distance F v lam n u
    (t.1,(r.2.map Event.facility)::t.2)

lemma historyRun_fst {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (n : ℕ) (s : State m d) :
    (historyRun distance F v lam n s).1=(run distance F v lam n s).1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _

lemma finish_prefix {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F B : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
    (fuel : ℕ) (s : State m d) (hz : (0:ℝ)≤(s.phase:ℝ)) (hQ : s.opened⊆F∪B) :
    let r := finish distance F v lam fuel s
    Prefix loc F B (v:ℝ) (s.phase:ℝ) (lam:ℝ) 0 s.opened (r.2.map Event.facility) ∧
    (∀ i∈r.2.map Event.facility,i∈F) ∧
    r.1.opened=s.opened∪(r.2.map Event.facility).toFinset := by
  induction fuel generalizing s with
  | zero =>
    simp only [finish,List.map_nil,List.toFinset_nil,Finset.union_empty,List.not_mem_nil,
      false_implies,implies_true,and_true]
    exact .nil _
  | succ fuel ih =>
    cases he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i)) with
    | none =>
      simp only [finish,he,List.map_nil,List.toFinset_nil,Finset.union_empty,List.not_mem_nil,
        false_implies,implies_true,and_true]
      exact .nil _
    | some e =>
      obtain ⟨hi,hin,x,hx,_⟩ := first_some distance F s.opened v s.phase lam _ e he
      have hu : (update distance v s e).opened⊆F∪B := Finset.insert_subset (Finset.mem_union_left B hi) hQ
      obtain ⟨hp,hr,hs⟩ := ih (update distance v s e) hz hu
      have hop := storedOpening_sound loc distance hd F s.opened v s.phase lam 0 e.facility hv hv1 hz x hx
      have hentry : Entry loc F B s.opened (v:ℝ) (s.phase:ℝ) (lam:ℝ) 0 e.facility :=
        ⟨hin,Or.inr ⟨hi,s.opened,Finset.Subset.refl _,hQ,by simpa only [Rat.cast_zero] using hop⟩⟩
      simp only [finish,he,List.map_cons]
      refine ⟨.cons hentry hp,?_,?_⟩
      · intro i hi'
        rcases List.mem_cons.mp hi' with rfl|hi'
        · exact hi
        · exact hr i hi'
      · rw [hs,List.toFinset_cons]
        change insert e.facility s.opened ∪ _=s.opened∪insert e.facility _
        simp only [Finset.insert_union,Finset.union_insert]

theorem historyRun_spec {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F B : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
    (n q : ℕ) (s : State m d) (hz : s.phase=(1+v^2)^q) (hQ : s.opened⊆F∪B) :
    let r := historyRun distance F v lam n s
    r.2.length=n ∧ History loc F B (v:ℝ) (lam:ℝ) 0 q s.opened r.2 ∧
    Regular F r.2 ∧ after s.opened r.2=r.1.opened := by
  induction n generalizing q s with
  | zero =>
    dsimp only [historyRun,after]
    exact ⟨rfl,.nil _ _,by simp only [Regular,List.not_mem_nil,false_implies,implies_true],rfl⟩
  | succ n ih =>
    let r := finish distance F v lam F.card s
    have hphase : (s.phase:ℝ)=(1+(v:ℝ)^2)^q := by rw [hz]; push_cast; rfl
    have hnonneg : (0:ℝ)≤(s.phase:ℝ) := by rw [hphase]; positivity
    obtain ⟨_,_,_,_,hhi,hp,hm⟩ := complete_spec loc distance hd F v lam hv hv1 s hnonneg
    change r.1.opened⊆s.opened∪F at hhi
    change r.1.phase=s.phase at hp
    obtain ⟨hprefix,hregular,hopened⟩ := finish_prefix loc distance hd F B v lam hv hv1 F.card s hnonneg hQ
    change Prefix loc F B (v:ℝ) (s.phase:ℝ) (lam:ℝ) 0 s.opened (r.2.map Event.facility) at hprefix
    change (∀ i∈r.2.map Event.facility,i∈F) at hregular
    change r.1.opened=s.opened∪(r.2.map Event.facility).toFinset at hopened
    have hvalid : Valid loc F B s.opened (v:ℝ) ((1+(v:ℝ)^2)^q) (lam:ℝ) 0 (r.2.map Event.facility) := by
      refine ⟨by simpa only [hphase] using hprefix,?_⟩
      rw [←hopened]
      change PhaseMaximal loc F (v:ℝ) (lam:ℝ) r.1.real at hm
      simpa only [PhaseMaximal,PhaseSequence.Maximal,State.real,hp,hphase] using hm
    have hnextphase : (advance distance v r.1).phase=(1+v^2)^(q+1) := by
      change (1+v^2)*r.1.phase=_
      rw [hp,hz,pow_succ]
      ring
    have hnextQ : (advance distance v r.1).opened⊆F∪B :=
      hhi.trans (Finset.union_subset hQ Finset.subset_union_left)
    obtain ⟨htlen,hthist,htreg,htafter⟩ := ih (q+1) (advance distance v r.1) hnextphase hnextQ
    dsimp only [historyRun]
    refine ⟨by simpa only [List.length_cons] using congrArg (·+1) htlen,?_,?_,?_⟩
    · apply History.cons hvalid
      rw [←hopened]
      exact hthist
    · intro H hH
      rcases List.mem_cons.mp hH with rfl|hH
      · exact hregular
      · exact htreg H hH
    · change after (s.opened∪(r.2.map Event.facility).toFinset) _=_
      rw [←hopened]
      exact htafter

def count {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v lam : ℚ) (q n : ℕ) : ℕ :=
  ((run distance F v lam n ⟨Q,(1+v^2)^q,Vector.replicate d 0⟩).1.opened∩F).card

theorem count_attains {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F B Q : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (q n : ℕ) (hQ : Q⊆F∪B) :
    Attains loc F B Q (v:ℝ) (lam:ℝ) q n (count distance F Q v lam q n) := by
  let s : State m d := ⟨Q,(1+v^2)^q,Vector.replicate d 0⟩
  obtain ⟨hlen,hh,hr,ha⟩ := historyRun_spec loc distance hd F B v lam hv hv1 n q s rfl hQ
  refine ⟨(historyRun distance F v lam n s).2,hlen,hh,hr,?_⟩
  rw [ha,historyRun_fst]
  rfl

end MetricKMedianRecovery.RationalPhase

end OAI
