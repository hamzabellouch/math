import Mathlib
import OAI.Geometry.HyperbolicGroups.WordDisk
import OAI.Geometry.HyperbolicGroups.GraphGroupWalk

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.GraphWordFilling
open SimpleGraph WordPictures
variable {V A : Type*} {G : SimpleGraph V}

def word (r : G.Dart → A × Bool) {u v : V} (p : G.Walk u v) : Word A := p.darts.map r
@[simp] lemma word_nil (r : G.Dart → A × Bool) (v : V) : word r (.nil : G.Walk v v) = [] := rfl
@[simp] lemma word_cons (r : G.Dart → A × Bool) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    word r (.cons h p) = r ⟨(u,v),h⟩ :: word r p := rfl
@[simp] lemma word_append (r : G.Dart → A × Bool) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : word r (p.append q) = word r p ++ word r q := by
  simp [word]
@[simp] lemma word_length (r : G.Dart → A × Bool) {u v : V} (p : G.Walk u v) :
    (word r p).length = p.length := by simp [word]

lemma short_filling (r : G.Dart → A × Bool)
    (hr : ∀ e, r e.symm = ((r e).1,!(r e).2)) (R : Set (Word A))
    {u v : V} (h : G.Adj u v) (p : G.Walk v u) (hp : p.length + 1 < 3) :
    Homotopy R (word r (.cons h p)) [] 0 := by
  apply Homotopy.free
  have hv : ∀ e : G.Dart, FreeGroup.mk [r e.symm] = (FreeGroup.mk [r e])⁻¹ := by
    intro e
    rw [hr]
    rfl
  have hh := GraphGroupWalk.short_loop_eval (fun e => FreeGroup.mk [r e]) hv h p hp
  have he {a b : V} (q : G.Walk a b) :
      FreeGroup.mk (word r q) = GraphGroupWalk.eval (fun e => FreeGroup.mk [r e]) q := by
    induction q with
    | nil => rfl
    | cons h q ih =>
      change FreeGroup.mk ([r ⟨_,h⟩] ++ word r q) = _
      rw [← FreeGroup.mul_mk,ih]
      rfl
  exact (he _).trans hh

/-- Quantitative noncommutative loop erasure. Each deleted elementary cycle
costs one, and each backtrack costs zero. The residual path pays for its own
length; no relator injection or distinct-letter assumption is needed. -/
theorem path_filling (r : G.Dart → A × Bool)
    (hr : ∀ e, r e.symm = ((r e).1,!(r e).2)) (R : Set (Word A))
    (hR : ∀ (u : V) (p : G.Walk u u), p.IsCycle → word r p ∈ R)
    {u v : V} (p : G.Walk u v) :
    ∃ (q : G.Walk u v) (a : ℕ), q.IsPath ∧
      Homotopy R (word r p) (word r q) a ∧ a + q.length ≤ p.length := by
  classical
  induction p with
  | nil => exact ⟨.nil,0,Walk.IsPath.nil,WordPictures.Homotopy.refl _,by simp⟩
  | @cons u v w h p ih =>
    obtain ⟨q,a,hq,he,ha⟩ := ih
    have he' : Homotopy R (word r (.cons h p)) (word r (.cons h q)) a := by
      simpa only [List.nil_append,List.append_nil,List.singleton_append,word_cons] using
        he.contextual [r ⟨(u,v),h⟩] []
    by_cases hu : u ∈ q.support
    · let s := q.takeUntil u hu
      let t := q.dropUntil u hu
      have hst : s.append t = q := q.take_spec hu
      have hs : s.IsPath := hq.takeUntil hu
      have ht : t.IsPath := hq.dropUntil hu
      have hlen : s.length + t.length = q.length := by rw [← Walk.length_append,hst]
      obtain ⟨k,hk,hklen⟩ : ∃ k, Homotopy R (word r (.cons h s)) [] k ∧ k ≤ s.length + 1 := by
        by_cases hl : 3 ≤ s.length + 1
        · have hc : (Walk.cons h s).IsCycle :=
            Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hs,hl⟩
          refine ⟨1,?_,by omega⟩
          simpa only [List.nil_append,List.append_nil] using
            (Homotopy.move (Move.face [] [] _ (hR _ _ hc)))
        · exact ⟨0,short_filling r hr R h s (by omega),by omega⟩
      have hkt : Homotopy R (word r (.cons h q)) (word r t) k := by
        have hh := hk.contextual [] (word r t)
        simpa only [List.nil_append,← word_append,Walk.cons_append,hst] using hh
      refine ⟨t,a+k,ht,he'.trans hkt,?_⟩
      simp only [Walk.length_cons]
      omega
    · refine ⟨.cons h q,a,hq.cons hu,he',?_⟩
      simp only [Walk.length_cons]
      omega

/-- A closed graph walk of length L
has a disk derivation over its simple cycles using at most L relator disks. -/
theorem closed_filling (r : G.Dart → A × Bool)
    (hr : ∀ e, r e.symm = ((r e).1,!(r e).2)) (R : Set (Word A))
    (hR : ∀ (u : V) (p : G.Walk u u), p.IsCycle → word r p ∈ R)
    {u : V} (p : G.Walk u u) :
    ∃ a ≤ p.length, Homotopy R (word r p) [] a := by
  obtain ⟨q,a,hq,hh,ha⟩ := path_filling r hr R hR p
  have hn := Walk.isPath_iff_nil.mp hq
  cases hn
  exact ⟨a,by simpa using ha,hh⟩

end HyperbolicObstruction.GraphWordFilling
end
end

section

end
end

end OAI
