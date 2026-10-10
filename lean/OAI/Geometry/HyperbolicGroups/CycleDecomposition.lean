import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeWalks
open SimpleGraph
variable {V A : Type*} {G : SimpleGraph V} [AddCommGroup A]

def chain (c : G.Dart → A) {u v : V} (p : G.Walk u v) : A := (p.darts.map c).sum
@[simp] lemma chain_nil (c : G.Dart → A) (u : V) : chain c (.nil : G.Walk u u) = 0 := rfl
@[simp] lemma chain_cons (c : G.Dart → A) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    chain c (.cons h p) = c ⟨(u,v),h⟩ + chain c p := rfl
@[simp] lemma chain_append (c : G.Dart → A) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    chain c (p.append q) = chain c p + chain c q := by simp [chain]

/-- A simple loop with its actual base vertex and edge traversals. -/
abbrev Circuit (G : SimpleGraph V) := Σ a : V, {p : G.Walk a a // p.IsCycle}
def perimeter (cs : List (Circuit G)) : ℕ := (cs.map (fun c => c.2.val.length)).sum
def total (c : G.Dart → A) (cs : List (Circuit G)) : A := (cs.map (fun q => chain c q.2.val)).sum
@[simp] lemma perimeter_nil : perimeter ([] : List (Circuit G)) = 0 := rfl
@[simp] lemma perimeter_cons (q : Circuit G) (cs : List (Circuit G)) :
    perimeter (q::cs) = q.2.val.length + perimeter cs := rfl
@[simp] lemma total_nil (c : G.Dart → A) : total c [] = 0 := rfl
@[simp] lemma total_cons (c : G.Dart → A) (q : Circuit G) (cs : List (Circuit G)) :
    total c (q::cs) = chain c q.2.val + total c cs := rfl

lemma short_loop_chain (c : G.Dart → A) (hc : ∀ d, c d.symm = -c d)
    {u v : V} (h : G.Adj u v) (p : G.Walk v u) (hp : p.length + 1 < 3) :
    chain c (.cons h p) = 0 := by
  cases p with
  | nil => exact (h.ne rfl).elim
  | @cons v w u h' p =>
    have hp0 : p.length = 0 := by simp only [Walk.length_cons] at hp; omega
    have hn := Walk.length_eq_zero_iff.mp hp0
    cases hn
    have hh := hc ⟨(u,v),h⟩
    simpa only [chain_cons,chain_nil,add_zero,hh,add_neg_cancel] using
      (show c ⟨(u,v),h⟩ + c ⟨(v,u),h'⟩ = 0 by
        rw [show c ⟨(v,u),h'⟩ = -c ⟨(u,v),h⟩ from hh,add_neg_cancel])

/-- Loop erasure WITH the removed simple circuits retained, preserving the
exact signed edge chain. This is stronger than existence of an elementary
cycle and does not discard a nonzero cellular chain. -/
theorem decompose_walk (c : G.Dart → A) (hc : ∀ d, c d.symm = -c d)
    {u v : V} (p : G.Walk u v) :
    ∃ (q : G.Walk u v) (cs : List (Circuit G)), q.IsPath ∧
      chain c p = chain c q + total c cs ∧ q.length + perimeter cs ≤ p.length := by
  classical
  induction p with
  | nil => exact ⟨.nil,[],Walk.IsPath.nil,by simp,by simp⟩
  | @cons u v w h p ih =>
    obtain ⟨q,cs,hq,he,hl⟩ := ih
    by_cases hu : u ∈ q.support
    · let a := q.takeUntil u hu
      let b := q.dropUntil u hu
      have hab : a.append b = q := q.take_spec hu
      have ha : a.IsPath := hq.takeUntil hu
      have hb : b.IsPath := hq.dropUntil hu
      have hlab : a.length + b.length = q.length := by rw [← Walk.length_append,hab]
      have heab : chain c a + chain c b = chain c q := by rw [← chain_append,hab]
      by_cases hlen : 3 ≤ a.length + 1
      · have hcy : (Walk.cons h a).IsCycle := by
          apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
          exact ⟨by simpa using ha,hlen⟩
        refine ⟨b,⟨u,⟨Walk.cons h a,hcy⟩⟩::cs,hb,?_,?_⟩
        · simp only [chain_cons,total_cons]
          rw [he,← heab]
          abel
        · simp only [perimeter_cons,Walk.length_cons]
          omega
      · have hz := short_loop_chain c hc h a (by omega)
        refine ⟨b,cs,hb,?_,?_⟩
        · rw [chain_cons,he,← heab]
          have hz' : c ⟨(u,v),h⟩ + chain c a = 0 := hz
          calc
            _ = (c ⟨(u,v),h⟩ + chain c a) + (chain c b + total c cs) := by abel
            _ = _ := by rw [hz',zero_add]
        · simp only [Walk.length_cons]
          omega
    · refine ⟨.cons h q,cs,hq.cons hu,?_,?_⟩
      · simp only [chain_cons,he,add_assoc]
      · simp only [Walk.length_cons]
        omega

/-- Every closed macro walk splits into simple cycles and cancelling
backtracks, with exact signed cone chain and nonincreasing total perimeter. -/
theorem decompose_closed (c : G.Dart → A) (hc : ∀ d, c d.symm = -c d)
    {u : V} (p : G.Walk u u) :
    ∃ cs : List (Circuit G), chain c p = total c cs ∧ perimeter cs ≤ p.length := by
  obtain ⟨q,cs,hq,he,hl⟩ := decompose_walk c hc p
  have hn := Walk.isPath_iff_nil.mp hq
  cases hn
  exact ⟨cs,by simpa using he,by simpa using hl⟩

end HyperbolicObstruction.ConeWalks
end
end

section

end
end

end OAI
