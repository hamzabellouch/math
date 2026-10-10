import Mathlib
import OAI.Combinatorics.UniformKServer.EpochShadow

namespace OAI

noncomputable section
                                   
section

namespace UniformKServer.EpochControl
open EpochShadow

structure State (n k : ℕ) where
  filter : FilterState n k
  virtual : Entry n k
  marked : Finset (Fin k)
  seen : Finset (Fin n)
  fallback : Bool

def asRaw {n k : ℕ} (s : State n k) : Fallback.RawState n k :=
  ⟨⟨s.virtual.position,s.marked⟩,s.seen,0⟩

def initial {n k : ℕ} (u : Configuration n k) : State n k :=
  ⟨UniformKServer.initial u,⟨u,0⟩,∅,∅,false⟩

def label {n k : ℕ} (hk : 0 < k) (T : Selector n k) (s : State n k) (r : Fin n) : Fin k :=
  if s.fallback then Fallback.rawChoice hk (asRaw s) r
  else if ∀z ∈ s.filter.live,Covers z r then
    Fallback.pick hk (Fallback.coverers s.virtual.position r)
  else T s.filter.kept s.virtual.position r

def step {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : State n k) (r : Fin n) : State n k :=
  if s.fallback then
    let raw := Fallback.rawStep hk (asRaw s) r
    ⟨UniformKServer.step M s.filter r,⟨raw.marking.position,s.virtual.moves⟩,
      raw.marking.marked,raw.seen,true⟩
  else if ∀z ∈ s.filter.live,Covers z r then
    {s with seen := bookStep (k:=k) s.seen r}
  else
    let e := nextEntry s.virtual r (T s.filter.kept s.virtual.position r)
    ⟨UniformKServer.step M s.filter r,e,∅,bookStep (k:=k) s.seen r,decide (M<e.moves)⟩

def runTrace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k) :
    State n k → List (Fin n) → History n k
  | _,[] => []
  | s,r::w => (r,label hk T s r)::runTrace hk M T (step hk M T s r) w

theorem rawChoice_congr {n k : ℕ} (hk : 0 < k) (s t : Fallback.RawState n k)
    (hm : s.marking=t.marking) (hs : s.seen=t.seen) (r : Fin n) :
    Fallback.rawChoice hk s r=Fallback.rawChoice hk t r := by
  simp [Fallback.rawChoice,Fallback.isEndpoint,hm,hs]
  rfl

theorem rawStep_congr {n k : ℕ} (hk : 0 < k) (s t : Fallback.RawState n k)
    (hm : s.marking=t.marking) (hs : s.seen=t.seen) (r : Fin n) :
    (Fallback.rawStep hk s r).marking=(Fallback.rawStep hk t r).marking ∧
    (Fallback.rawStep hk s r).seen=(Fallback.rawStep hk t r).seen := by
  have hc := rawChoice_congr hk s t hm hs r
  by_cases he : k < (insert r t.seen).card <;>
    simp [Fallback.rawStep,Fallback.isEndpoint,hm,hs,hc,he]

theorem fallbackTrace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : State n k) (hs : s.fallback=true) (raw : Fallback.RawState n k)
    (hm : (asRaw s).marking=raw.marking) (hseen : s.seen=raw.seen) (w : List (Fin n)) :
    runTrace hk M T s w = Fallback.rawTrace hk raw w := by
  induction w generalizing s raw with
  | nil => rfl
  | cons r w ih =>
    have hchoice := rawChoice_congr hk (asRaw s) raw hm hseen r
    have hstep := rawStep_congr hk (asRaw s) raw hm hseen r
    simp only [runTrace,label,hs,ite_true,Fallback.rawTrace,hchoice]
    congr 1
    apply ih
    · simp [step,hs]
    · simpa [step,hs,asRaw] using hstep.1
    · simpa [step,hs] using hstep.2

theorem normalTrace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (s : State n k) (hs : s.fallback=false) (w : List (Fin n)) :
    runTrace hk M T s w = trace hk M T s.filter s.virtual s.seen w := by
  induction w generalizing s with
  | nil => rfl
  | cons r w ih =>
    by_cases hit : ∀z ∈ s.filter.live,Covers z r
    · simp only [runTrace,label,hs,Bool.false_eq_true,ite_false,ite_eq_left hit,trace]
      congr 1
      simpa only [step,hs,Bool.false_eq_true,ite_false,ite_eq_left hit] using
        ih {s with seen := bookStep (k:=k) s.seen r} hs
    · let e := nextEntry s.virtual r (T s.filter.kept s.virtual.position r)
      by_cases hc : e.moves ≤ M
      · have he : ¬ M < e.moves := by omega
        simp only [runTrace,label,hs,Bool.false_eq_true,ite_false,ite_eq_right hit,trace]
        simp only [show (nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves ≤ M from hc,
          ite_true]
        change _::_ = _::_
        congr 1
        simpa only [step,hs,Bool.false_eq_true,ite_false,ite_eq_right hit,show ¬M<e.moves from he,
          decide_false,e] using ih (step hk M T s r) (by
            simp only [step,hs,Bool.false_eq_true,ite_false,ite_eq_right hit]
            exact decide_eq_false he)
      · have he : M < e.moves := by omega
        simp only [runTrace,label,hs,Bool.false_eq_true,ite_false,ite_eq_right hit,trace]
        simp only [show ¬(nextEntry s.virtual r (T s.filter.kept s.virtual.position r)).moves ≤ M from hc,
          ite_false]
        congr 1
        apply fallbackTrace
        · simp only [step,hs,Bool.false_eq_true,ite_false,ite_eq_right hit]
          exact decide_eq_true he
        · simp [asRaw,step,hs,hit]
        · simp [step,hs,hit]

theorem initial_trace {n k : ℕ} (hk : 0 < k) (M : ℕ) (T : Selector n k)
    (u : Configuration n k) (w : List (Fin n)) :
    runTrace hk M T (initial u) w = trace hk M T (UniformKServer.initial u) ⟨u,0⟩ ∅ w :=
  normalTrace hk M T (initial u) rfl w

end UniformKServer.EpochControl

end


end

end OAI
