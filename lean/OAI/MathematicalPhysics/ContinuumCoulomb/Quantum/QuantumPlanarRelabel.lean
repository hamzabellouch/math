import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarRouteRealization

namespace OAI

/-! Transport a planar route family through vertex and edge permutations.
Each edge may independently reverse its orientation. -/

noncomputable section
namespace ContinuumCoulomb.QMAPlanarRouteData
open scoped Classical

def relabelIndex (L : ℕ) (flip : Bool) (i : ℕ) : ℕ :=
  if flip then L-i else i

private theorem relabelIndex_le {L i : ℕ} (flip : Bool) (hi : i ≤ L) :
    relabelIndex L flip i ≤ L := by
  cases flip
  · exact hi
  · exact Nat.sub_le _ _

private theorem relabelIndex_interior {L i : ℕ} (flip : Bool)
    (hi0 : 0 < i) (hi : i < L) :
    0 < relabelIndex L flip i ∧ relabelIndex L flip i < L := by
  cases flip <;> simp only [relabelIndex,Bool.false_eq_true,ite_false,ite_true] <;> omega

private theorem relabelIndex_injective {L i j : ℕ} (flip : Bool)
    (hi : i ≤ L) (hj : j ≤ L)
    (h : relabelIndex L flip i=relabelIndex L flip j) : i=j := by
  cases flip <;> simp only [relabelIndex,Bool.false_eq_true,ite_false,ite_true] at h <;> omega

def relabelStepIndex (L : ℕ) (flip : Bool) (i : ℕ) : ℕ :=
  if flip then L-(i+1) else i

private theorem relabelStepIndex_lt {L i : ℕ} (flip : Bool) (hi : i < L) :
    relabelStepIndex L flip i < L := by
  cases flip <;> simp [relabelStepIndex] <;> omega

private theorem relabelIndex_left {L i : ℕ} (flip : Bool) (hi : i < L) :
    relabelIndex L flip i=
      if flip then relabelStepIndex L flip i+1 else relabelStepIndex L flip i := by
  cases flip
  · rfl
  · change L-i=L-(i+1)+1
    omega

private theorem relabelIndex_right (L i : ℕ) (flip : Bool) :
    relabelIndex L flip (i+1)=
      if flip then relabelStepIndex L flip i else relabelStepIndex L flip i+1 := by
  cases flip <;> simp [relabelIndex,relabelStepIndex]

private theorem flip_pairs_disjoint {α : Type} (a b c d : α) (s t : Bool)
    (h : ¬(a=c ∧ b=d) ∧ ¬(a=d ∧ b=c)) :
    ¬((if s then b else a)=(if t then d else c) ∧
      (if s then a else b)=(if t then c else d)) ∧
    ¬((if s then b else a)=(if t then c else d) ∧
      (if s then a else b)=(if t then d else c)) := by
  cases s <;> cases t <;> simp_all only [Bool.false_eq_true,ite_false,ite_true] <;> tauto

variable {G H : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    (vertex : Fin H.n ≃ Fin G.n) (edge : H.Edge ≃ G.Edge) (flip : H.Edge → Bool)
    (left : ∀ e, vertex (H.left e)=if flip e then G.right (edge e) else G.left (edge e))
    (right : ∀ e, vertex (H.right e)=if flip e then G.left (edge e) else G.right (edge e))

def relabel : QMAPlanarRouteData H where
  length e := P.length (edge e)
  length_pos e := P.length_pos (edge e)
  position v := P.position (vertex v)
  position_injective := P.position_injective.comp vertex.injective
  point e i := P.point (edge e) (relabelIndex (P.length (edge e)) (flip e) i)
  positive e i hi := P.positive (edge e) _ (relabelIndex_le (flip e) hi)
  first e := by
    rw [left e]
    cases hf : flip e
    · simpa [relabelIndex,hf] using P.first (edge e)
    · simpa [relabelIndex,hf] using P.last (edge e)
  last e := by
    rw [right e]
    cases hf : flip e
    · simpa [relabelIndex,hf] using P.last (edge e)
    · simpa [relabelIndex,hf] using P.first (edge e)
  simple e i j hi hj h :=
    relabelIndex_injective (flip e) hi hj
      (P.simple (edge e) _ _ (relabelIndex_le (flip e) hi)
        (relabelIndex_le (flip e) hj) h)
  step e i hi := by
    rw [relabelIndex_left (flip e) hi,relabelIndex_right _ _ (flip e)]
    have h := P.step (edge e) _ (relabelStepIndex_lt (flip e) hi)
    cases hf : flip e
    · simpa [hf] using h
    · simpa [hf] using h.symm
  avoids e i v hi0 hi := by
    obtain ⟨ha,hb⟩ := relabelIndex_interior (flip e) hi0 hi
    exact P.avoids (edge e) _ (vertex v) ha hb
  disjoint e f i j hef hi0 hi hj := by
    obtain ⟨ha,hb⟩ := relabelIndex_interior (flip e) hi0 hi
    exact P.disjoint (edge e) (edge f) _ _
      (fun h => hef (edge.injective h)) ha hb (relabelIndex_le (flip f) hj)
  edges_disjoint e f hef i j hi hj := by
    have h := P.edges_disjoint (edge e) (edge f)
      (fun h => hef (edge.injective h))
      (relabelStepIndex (P.length (edge e)) (flip e) i)
      (relabelStepIndex (P.length (edge f)) (flip f) j)
      (relabelStepIndex_lt (flip e) hi) (relabelStepIndex_lt (flip f) hj)
    rw [relabelIndex_left (flip e) hi,relabelIndex_right _ _ (flip e),
      relabelIndex_left (flip f) hj,relabelIndex_right _ _ (flip f)]
    simpa only [apply_ite] using flip_pairs_disjoint
      (P.point (edge e) (relabelStepIndex (P.length (edge e)) (flip e) i))
      (P.point (edge e) (relabelStepIndex (P.length (edge e)) (flip e) i+1))
      (P.point (edge f) (relabelStepIndex (P.length (edge f)) (flip f) j))
      (P.point (edge f) (relabelStepIndex (P.length (edge f)) (flip f) j+1))
      (flip e) (flip f) h

theorem relabel_position (v : Fin H.n) :
    (P.relabel vertex edge flip left right).position v=P.position (vertex v) := rfl

theorem relabel_point (e : H.Edge) (i : ℕ) :
    (P.relabel vertex edge flip left right).point e i=
      P.point (edge e) (if flip e then P.length (edge e)-i else i) := rfl

theorem relabel_length_le {K : ℕ} (hK : ∀ e, P.length e≤K) (e : H.Edge) :
    (P.relabel vertex edge flip left right).length e≤K := hK (edge e)

theorem relabel_bounded {X Y : ℕ} (h : P.Bounded X Y) :
    (P.relabel vertex edge flip left right).Bounded X Y := by
  refine ⟨fun v => h.1 (vertex v),?_⟩
  intro e i hi
  exact h.2 (edge e) _ (relabelIndex_le (flip e) hi)

end ContinuumCoulomb.QMAPlanarRouteData

end

end OAI
