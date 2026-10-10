import OAI.Combinatorics.ContingencyTables.Transport.FiniteAdaptiveObservable

namespace OAI

/-! # Complete histories under an encoded transition law -/

namespace ContingencyTables.FiniteObservableTransport

open CommonBasesFPRAS
open scoped Classical

def traceAfter {C U : Type*} (step : C → U → C) (c : C) : List U → List C
  | [] => []
  | u::us => let d := step c u; d::traceAfter step d us

def traceStates {C U : Type*} (step : C → U → C) (c : C) (us : List U) : List C :=
  c::traceAfter step c us

lemma traceAfter_map {C U V : Type*} (F : C → U → C) (f : V → U)
    (vs : List V) (c : C) :
    traceAfter F c (vs.map f)=traceAfter (fun c v => F c (f v)) c vs := by
  induction vs generalizing c with
  | nil => rfl
  | cons v vs ih => simp only [List.map_cons,traceAfter,ih]

lemma traceStates_map {C U V : Type*} (F : C → U → C) (f : V → U)
    (vs : List V) (c : C) :
    traceStates F c (vs.map f)=traceStates (fun c v => F c (f v)) c vs := by
  unfold traceStates
  rw [traceAfter_map]

noncomputable section
variable {C Z U V : Type*} [Fintype U] [Fintype V]

/-- Equality of the encoded row laws transfers the whole finite history,
including observables depending on every visited state. -/
theorem traceStates_sameLaw (F : C → U → C) (G : Z → V → Z) (e : Z → C)
    (h : ∀ z,SameLaw (F (e z)) (fun v => e (G z v))) (z : Z) (N : ℕ) :
    SameLaw (fun us : Fin N → U => traceStates F (e z) (List.ofFn us))
      (fun vs : Fin N → V => (traceStates G z (List.ofFn vs)).map e) := by
  intro phi
  induction N generalizing z phi with
  | zero => simp only [List.ofFn_zero,traceStates,traceAfter,List.map_cons,List.map_nil,
      uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp only [List.ofFn_cons,traceStates,traceAfter,List.map_cons]
    have he := h z (fun c => uniformAverage (fun us : Fin N → U =>
      phi (e z::traceStates F c (List.ofFn us))))
    refine he.trans ?_
    apply congrArg uniformAverage
    funext v
    exact ih (G z v) (fun cs => phi (e z::cs))

/-- The same encoding argument also transports a terminal state without
requiring a decoder or finiteness of the encoded state space. -/
theorem foldl_sameLaw (F : C → U → C) (G : Z → V → Z) (e : Z → C)
    (h : ∀ z,SameLaw (F (e z)) (fun v => e (G z v))) (z : Z) (N : ℕ) :
    SameLaw (fun us : Fin N → U => (List.ofFn us).foldl F (e z))
      (fun vs : Fin N → V => e ((List.ofFn vs).foldl G z)) := by
  intro phi
  induction N generalizing z phi with
  | zero => simp only [List.ofFn_zero,List.foldl_nil,uniformAverage_const]
  | succ N ih =>
    rw [uniformAverage_fin_succ,uniformAverage_fin_succ]
    simp only [List.ofFn_cons,List.foldl_cons]
    have he := h z (fun c => uniformAverage (fun us : Fin N → U =>
      phi ((List.ofFn us).foldl F c)))
    refine he.trans ?_
    apply congrArg uniformAverage
    funext v
    exact ih (G z v) phi

omit [Fintype U] in
/-- The reverse accumulator used by a bounded fold has precisely the
chronological history after reversing its stored list. -/
lemma traceAfter_fold (F : C → U → C) (us : List U) (c : C) (history : List C) :
    (us.foldl (fun s u => let d := F s.1 u; (d,d::s.2)) (c,history)).2.reverse=
      history.reverse++traceAfter F c us := by
  induction us generalizing c history with
  | nil => simp only [List.foldl_nil,traceAfter,List.append_nil]
  | cons u us ih =>
    simp only [List.foldl_cons,traceAfter]
    rw [ih,List.reverse_cons,List.append_assoc]
    rfl

omit [Fintype U] in
lemma traceStates_fold (F : C → U → C) (us : List U) (c : C) :
    (us.foldl (fun s u => let d := F s.1 u; (d,d::s.2)) (c,[c])).2.reverse=
      traceStates F c us := by
  rw [traceAfter_fold]
  rfl

end
end ContingencyTables.FiniteObservableTransport

end OAI
