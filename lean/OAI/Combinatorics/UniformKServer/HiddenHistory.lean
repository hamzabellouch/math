import Mathlib
import OAI.Combinatorics.UniformKServer.RawBlockCharge
import OAI.Combinatorics.UniformKServer.HiddenFlow
import OAI.Combinatorics.UniformKServer.ActualPublicFlow

namespace OAI

noncomputable section

/-! Literal optimal labeled histories yield the public-prefix hidden law used
in the finite-law construction. After a word ends its chosen label stays put;
no future request is supplied to the online process. -/
namespace UniformKServer.HiddenHistory
open Finset
open scoped Classical
variable {n k : ℕ} [NeZero k]

def next (s : Configuration n k) (h : History n k) (t : ℕ) : Fin n×Fin k :=
  if ht : t<h.length then h[t] else (finish s h 0,0)

def location (s : Configuration n k) (h : History n k) (t : ℕ) : Configuration n k :=
  finish s (h.take t)

omit [NeZero k] in
theorem finish_append (s : Configuration n k) (g h : History n k) :
    finish s (g++h)=finish (finish s g) h := by
  induction g generalizing s with
  | nil => rfl
  | cons a g ih => cases a; simp only [List.cons_append,finish,ih]

theorem update (s : Configuration n k) (h : History n k) (t : ℕ) (a : Fin k) :
    location s h (t+1) a=if a=(next s h t).2 then (next s h t).1 else location s h t a := by
  by_cases ht : t<h.length
  · simp only [location,List.take_succ_eq_append_getElem ht,finish_append,finish,next,dite_eq_left ht]
    simp only [serve,Function.update_apply ]
  · have he : h.length≤t := Nat.le_of_not_gt ht
    simp only [location,List.take_of_length_le he,
      List.take_of_length_le (he.trans (Nat.le_succ t)),next,dite_eq_right ht]
    split_ifs with ha
    · subst a; rfl
    · rfl

def trace (s : Configuration n k) (h : History n k) (t : ℕ) : List (Fin n) :=
  List.ofFn (fun i : Fin t=>(next s h i.val).1)

theorem trace_snoc (s : Configuration n k) (h : History n k) (t : ℕ) :
    trace s h (t+1)=trace s h t++[(next s h t).1] := by
  simp only [trace,List.ofFn_succ',List.concat_eq_append,Fin.val_castSucc,Fin.val_last]

theorem trace_length (s : Configuration n k) (h : History n k) (t : ℕ) :
    (trace s h t).length=t := by simp only [trace,List.length_ofFn]

theorem trace_take (s : Configuration n k) (h : History n k) (t : ℕ) (ht : t≤h.length) :
    trace s h t=(h.take t).map Prod.fst := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hl : t<h.length := by omega
    rw [trace_snoc,ih (by omega),List.take_succ_eq_append_getElem hl]
    simp only [List.map_append,List.map_singleton,next,dite_eq_left hl]

theorem trace_full (s : Configuration n k) (h : History n k) :
    trace s h h.length=h.map Prod.fst := by
  rw [trace_take s h _ le_rfl,List.take_length]

theorem trace_prefix (s : Configuration n k) (h : History n k) (a b : ℕ) (hab : a≤b) :
    (trace s h a).IsPrefix (trace s h b) := by
  induction b with
  | zero =>
    have ha : a=0 := by omega
    subst a
    exact List.prefix_refl _
  | succ b ih =>
    by_cases he : a=b+1
    · subst a; exact List.prefix_refl _
    · exact (ih (by omega)).trans (by rw [trace_snoc]; exact List.prefix_append _ _)

variable {Ω : Type} [Fintype Ω]

def data (s : Configuration n k) (h : Ω→History n k) (w : Ω→ℝ)
    (hw : ∀ω,0<w ω) (ht : ∑ω,w ω=1) : HiddenFlow.Data (Fin n) Ω k where
  weight := w
  positive := hw
  total := ht
  filtration t := Setoid.ker (fun ω=>trace s (h ω) t)
  refines := by
    intro t ω v he
    change trace s (h ω) (t+1)=trace s (h v) (t+1) at he
    rw [trace_snoc,trace_snoc] at he
    exact (List.append_inj he (by rw [trace_length,trace_length])) |>.1
  position t ω := location s (h ω) t
  chosen t ω := (next s (h ω) t).2
  request t ω := (next s (h ω) t).1
  update t ω a := update s (h ω) t a
  request_measurable := by
    intro t ω v he
    change trace s (h ω) (t+1)=trace s (h v) (t+1) at he
    rw [trace_snoc,trace_snoc] at he
    have hh := (List.append_inj he (by rw [trace_length,trace_length])) |>.2
    exact List.singleton_inj.mp hh

theorem is_public (s : Configuration n k) (h : Ω→History n k) (w : Ω→ℝ)
    (hw : ∀ω,0<w ω) (ht : ∑ω,w ω=1) : (data s h w hw ht).Public := by
  intro t ω v he
  exact he

theorem paid_step (d : RationalMetric n) (s : Configuration n k) (h : History n k) (t : ℕ) :
    costAlong d s (h.take (t+1))=costAlong d s (h.take t)+
      (d.distance (location s h t (next s h t).2) (next s h t).1 : ℝ) := by
  by_cases ht : t<h.length
  · rw [List.take_succ_eq_append_getElem ht,RawBlockCharge.cost_append]
    simp only [next,dite_eq_left ht,costAlong,add_zero,location]
  · have he : h.length≤t := Nat.le_of_not_gt ht
    simp only [List.take_of_length_le (he.trans (Nat.le_succ t)),
      next,dite_eq_right ht,location]
    rw [List.take_of_length_le he,(d.eq_zero _ _).mpr rfl,Rat.cast_zero,add_zero]

theorem paid_sum (d : RationalMetric n) (s : Configuration n k) (h : History n k) (N : ℕ) :
    (∑t∈range N,(d.distance (location s h t (next s h t).2) (next s h t).1 : ℝ))=
      costAlong d s (h.take N) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [sum_range_succ,ih,paid_step]

end UniformKServer.HiddenHistory

end

end OAI
