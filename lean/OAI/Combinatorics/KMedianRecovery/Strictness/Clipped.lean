import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FinishSpec

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

def clipped {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (W : Finset (Fin m)) (j : Fin d) : ℚ :=
  if W.Nonempty then min z ((1-3*v)*RationalOpenability.nearest distance W j) else z

lemma clipped_real {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (v z : ℚ) (W : Finset (Fin m)) (j : Fin d) :
    (clipped distance v z W j:ℝ)=clippedAt loc (1-3*(v:ℝ)) (z:ℝ) W j := by
  classical
  simp only [clipped,clippedAt]
  split_ifs with hW
  · simp only [Rat.cast_min,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_ofNat,
      RationalOpenability.nearest_cast loc distance hd]
  · rfl

def advance {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) : State m d :=
  ⟨s.opened,(1+v^2)*s.phase,Vector.ofFn (fun j =>
    if active distance v s.phase s.opened j then
      clipped distance v ((1+v^2)*s.phase) s.opened j else s.budget[j])⟩

lemma advance_get {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (j : Fin d) :
    (advance distance v s).budget[j] = if active distance v s.phase s.opened j then
      clipped distance v ((1+v^2)*s.phase) s.opened j else s.budget[j] := by
  simp only [advance,Fin.getElem_fin,Vector.getElem_ofFn]

lemma advance_real {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (v : ℚ) (s : State m d) :
    (advance distance v s).real=phaseUpdate loc (1-3*(v:ℝ)) (1+(v:ℝ)^2) s.real := by
  classical
  change ExecutionState.mk s.opened (((1+v^2)*s.phase:ℚ):ℝ)
      (fun j => (((advance distance v s).budget[j]:ℚ):ℝ)) =
    ExecutionState.mk s.opened ((1+(v:ℝ)^2)*(s.phase:ℝ))
      (fun j => if activeAt loc (1-3*(v:ℝ)) (s.phase:ℝ) s.opened j then
        clippedAt loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)*(s.phase:ℝ)) s.opened j
        else (s.budget[j]:ℝ))
  congr 1
  · push_cast
    rfl
  · funext j
    rw [advance_get]
    by_cases hj : active distance v s.phase s.opened j
    · simp only [ite_eq_left hj,ite_eq_left ((active_iff loc distance hd v s.phase s.opened j).mp hj),
        clipped_real loc distance hd,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_pow]
    · simp only [ite_eq_right hj,ite_eq_right (fun h => hj ((active_iff loc distance hd v s.phase s.opened j).mpr h))]

inductive Instruction (m d : ℕ) where
  | opening : Event m d → Instruction m d
  | advance : Instruction m d

def run {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (Instruction m d)
  | 0,s => (s,[])
  | q+1,s =>
      let r := finish distance F v lam F.card s
      let u := advance distance v r.1
      let t := run distance F v lam q u
      (t.1,r.2.map Instruction.opening ++ Instruction.advance::t.2)

theorem run_spec {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6)
    (q : ℕ) (s : State m d) (hz : (0:ℝ)≤(s.phase:ℝ)) :
    let r := run distance F v lam q s
    CountedTrace (OrdinaryStep loc F (v:ℝ) (lam:ℝ)) r.2.length s.real r.1.real ∧
    r.2.length≤q*(F.card+1) ∧
    s.opened ⊆ r.1.opened ∧ r.1.opened ⊆ s.opened∪F ∧
    r.1.phase=(1+v^2)^q*s.phase := by
  induction q generalizing s with
  | zero =>
    dsimp only [run]
    exact ⟨.nil _,by simp,Finset.Subset.refl _,Finset.subset_union_left,by simp⟩
  | succ q ih =>
    let r := finish distance F v lam F.card s
    have hr := complete_spec loc distance hd F v lam hv hv1 s hz
    change CountedTrace _ r.2.length s.real r.1.real ∧ _ at hr
    obtain ⟨hrtrace,hrlen,hrcount,hrlo,hrhi,hrphase,hrmax⟩ := hr
    change r.2.length≤F.card at hrlen
    have hphase : (0:ℝ)≤((advance distance v r.1).phase:ℝ) := by
      change (0:ℝ)≤(((1+v^2)*r.1.phase:ℚ):ℝ)
      rw [hrphase]
      push_cast
      exact mul_nonneg (by positivity) hz
    obtain ⟨httrace,htlen,htlo,hthi,htphase⟩ := ih (advance distance v r.1) hphase
    have hs : OrdinaryStep loc F (v:ℝ) (lam:ℝ) r.1.real (advance distance v r.1).real := by
      rw [advance_real loc distance hd]
      exact .advance _ hrmax
    have hall := (hrtrace.map (fun _ _ h => OrdinaryStep.opening h)).append
      (CountedTrace.cons hs httrace)
    simp only [run,List.length_append,List.length_map,List.length_cons]
    refine ⟨hall,?_,hrlo.trans htlo,?_,?_⟩
    · change r.2.length+((run distance F v lam q (advance distance v r.1)).2.length+1)≤_
      calc
        _ ≤ F.card+(q*(F.card+1)+1) := by omega
        _ = (q+1)*(F.card+1) := by ring
    · apply hthi.trans
      exact Finset.union_subset hrhi Finset.subset_union_right
    · rw [htphase]
      change (1+v^2)^q*((1+v^2)*r.1.phase)=_
      rw [hrphase,pow_succ]
      ring

def initial (m d : ℕ) : State m d := ⟨∅,1,Vector.replicate d 1⟩

lemma initial_real (m d : ℕ) : (initial m d).real=initialState (Fin d) (Fin m) := by
  simp only [initial,State.real,initialState,Rat.cast_one,Fin.getElem_fin,Vector.getElem_replicate]

end MetricKMedianRecovery.RationalPhase

end OAI
