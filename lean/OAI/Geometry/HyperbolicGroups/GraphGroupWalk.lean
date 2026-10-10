import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.GraphGroupWalk
open SimpleGraph
variable {V H : Type*} {G : SimpleGraph V} [Group H]

def eval (c : G.Dart → H) {u v : V} (p : G.Walk u v) : H := (p.darts.map c).prod
@[simp] lemma eval_nil (c : G.Dart → H) (u : V) : eval c (.nil : G.Walk u u) = 1 := rfl
@[simp] lemma eval_cons (c : G.Dart → H) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    eval c (.cons h p) = c ⟨(u,v),h⟩ * eval c p := rfl
@[simp] lemma eval_append (c : G.Dart → H) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    eval c (p.append q) = eval c p * eval c q := by simp [eval]

lemma short_loop_eval (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    {u v : V} (h : G.Adj u v) (p : G.Walk v u) (hp : p.length + 1 < 3) :
    eval c (.cons h p) = 1 := by
  cases p with
  | nil => exact (h.ne rfl).elim
  | @cons v w u h' p =>
    have hp0 : p.length = 0 := by simp only [Walk.length_cons] at hp; omega
    have hn := Walk.length_eq_zero_iff.mp hp0
    cases hn
    have hh := hc ⟨(u,v),h⟩
    simp only [eval_cons,eval_nil,mul_one]
    rw [show c ⟨(v,u),h'⟩ = (c ⟨(u,v),h⟩)⁻¹ from hh,mul_inv_cancel]

/-- Noncommutative loop erasure. Killing all elementary cycles suffices;
commutativity, a commutator relation, or graph connectedness is not assumed. -/
theorem reduce_to_path (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    (hcycle : ∀ (u : V) (p : G.Walk u u), p.IsCycle → eval c p = 1)
    {u v : V} (p : G.Walk u v) :
    ∃ q : G.Walk u v, q.IsPath ∧ eval c p = eval c q := by
  classical
  induction p with
  | nil => exact ⟨.nil,Walk.IsPath.nil,rfl⟩
  | @cons u v w h p ih =>
    obtain ⟨q,hq,he⟩ := ih
    by_cases hu : u ∈ q.support
    · let a := q.takeUntil u hu
      let b := q.dropUntil u hu
      have hab : a.append b = q := q.take_spec hu
      have ha : a.IsPath := hq.takeUntil hu
      have hb : b.IsPath := hq.dropUntil hu
      have heab : eval c a * eval c b = eval c q := by rw [← eval_append,hab]
      have hz : eval c (Walk.cons h a) = 1 := by
        by_cases hlen : 3 ≤ a.length + 1
        · apply hcycle
          apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
          exact ⟨by simpa using ha,hlen⟩
        · exact short_loop_eval c hc h a (by omega)
      refine ⟨b,hb,?_⟩
      rw [eval_cons,he,← heab,← mul_assoc]
      change eval c (Walk.cons h a) * eval c b = eval c b
      rw [hz,one_mul]
    · exact ⟨.cons h q,hq.cons hu,by simp only [eval_cons,he]⟩

theorem closed_eval_one (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    (hcycle : ∀ (u : V) (p : G.Walk u u), p.IsCycle → eval c p = 1)
    {u : V} (p : G.Walk u u) : eval c p = 1 := by
  obtain ⟨q,hq,he⟩ := reduce_to_path c hc hcycle p
  have hn := Walk.isPath_iff_nil.mp hq
  cases hn
  exact he

lemma eval_reverse (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    {u v : V} (p : G.Walk u v) : eval c p.reverse = (eval c p)⁻¹ := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    rw [Walk.reverse_cons,eval_append,ih]
    simp only [eval_cons,eval_nil,mul_one,mul_inv_rev]
    rw [show c ⟨(v,u),h.symm⟩ = (c ⟨(u,v),h⟩)⁻¹ from hc ⟨(u,v),h⟩]

/-- Route potentials under elementary-cycle relations. Only the chosen
routes, not a spanning-tree axiom, are needed. -/
theorem route_edge (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    (hcycle : ∀ (u : V) (p : G.Walk u u), p.IsCycle → eval c p = 1)
    {r u v : V} (p : G.Walk r u) (q : G.Walk r v) (h : G.Adj u v) :
    eval c p * c ⟨(u,v),h⟩ = eval c q := by
  have hz := closed_eval_one c hc hcycle (p.append ((Walk.cons h Walk.nil).append q.reverse))
  simp only [eval_append,eval_cons,eval_nil,mul_one,eval_reverse c hc] at hz
  exact mul_inv_eq_one.mp (by simpa only [mul_assoc] using hz)

end HyperbolicObstruction.GraphGroupWalk
end
end

section

end
end

end OAI
