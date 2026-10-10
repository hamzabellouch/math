import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRetainedRoutes

namespace OAI

/-! Either half of a corridor determines its unordered physical endpoints. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaPortOpposite_involutive (a : Fin 4) : qmaPortOpposite (qmaPortOpposite a) = a := by
  fin_cases a <;> rfl

theorem qmaGridNeighbor_opposite (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4) :
    qmaGridNeighbor (qmaGridNeighbor p a) (qmaPortOpposite a) = p := by
  fin_cases a
  · exact Prod.ext (Nat.add_sub_cancel p.1 1) rfl
  · exact Prod.ext rfl (Nat.add_sub_cancel p.2 1)
  · exact Prod.ext (by change p.1-1+1 = p.1; omega) rfl
  · exact Prod.ext rfl (by change p.2-1+1 = p.2; omega)

def qmaCorridorHalfCell (p : ℕ × ℕ) (a : Fin 4) (t : Fin 2) : ℕ × ℕ :=
  if t = 0 then p else qmaGridNeighbor p a

def qmaCorridorHalfPort (a : Fin 4) (t : Fin 2) : Fin 4 := if t = 0 then a else qmaPortOpposite a
def qmaCorridorHalfMode (b c : Bool) (t : Fin 2) : Bool := if t = 0 then b else c

def qmaCorridorEndPair (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 4) : Sym2 (ℕ × ℕ) :=
  s(qmaMovedPort cross p a,qmaMovedPort cross (qmaGridNeighbor p a) (qmaPortOpposite a))

theorem qmaCorridorEndPair_reverse (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4) :
    qmaCorridorEndPair cross (qmaGridNeighbor p a) (qmaPortOpposite a) = qmaCorridorEndPair cross p a := by
  unfold qmaCorridorEndPair
  rw [qmaGridNeighbor_opposite p hp a,qmaPortOpposite_involutive]
  exact Sym2.eq_swap

theorem qmaCellCorridor_mem_half {p z : ℕ × ℕ} {a : Fin 4} {b c : Bool}
    (hz : z ∈ qmaCellCorridor p a b c) :
    ∃ t : Fin 2, z ∈ qmaHalfPathAt (qmaCorridorHalfCell p a t)
      (qmaCorridorHalfMode b c t) (qmaCorridorHalfPort a t) := by
  rcases List.mem_append.mp hz with h | h
  · exact ⟨0,h⟩
  · exact ⟨1,List.mem_reverse.mp h⟩

theorem qmaCorridorBody_half_pair (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (hp : 0 < p.1 ∧ 0 < p.2) (a : Fin 4) (b c : Bool)
    (hb : b = decide (cross p)) (hc : c = decide (cross (qmaGridNeighbor p a))) (t : Fin 2) :
    s((QMACellRouteBody.corridor p a b c).source,(QMACellRouteBody.corridor p a b c).target) =
      qmaCorridorEndPair cross (qmaCorridorHalfCell p a t) (qmaCorridorHalfPort a t) := by
  have h0 : s((QMACellRouteBody.corridor p a b c).source,
      (QMACellRouteBody.corridor p a b c).target) = qmaCorridorEndPair cross p a := by
    change s(qmaCellTranslate p (qmaLocalPort b a),
      qmaCellTranslate (qmaGridNeighbor p a) (qmaLocalPort c (qmaPortOpposite a))) = _
    rw [hb,hc,← qmaMovedPort_local,← qmaMovedPort_local]
    rfl
  fin_cases t
  · exact h0
  · exact h0.trans (qmaCorridorEndPair_reverse cross p hp a).symm

theorem qmaCorridorHalf_mode (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    (p : ℕ × ℕ) (a : Fin 4) (b c : Bool)
    (hb : b = decide (cross p)) (hc : c = decide (cross (qmaGridNeighbor p a))) (t : Fin 2) :
    qmaCorridorHalfMode b c t = decide (cross (qmaCorridorHalfCell p a t)) := by
  fin_cases t
  · exact hb
  · exact hc

theorem qmaHalfPathAt_collision (cross : (ℕ × ℕ) → Prop) [DecidablePred cross]
    {p q z : ℕ × ℕ} {a d : Fin 4} {b c : Bool}
    (hb : b = decide (cross p)) (hc : c = decide (cross q))
    (hz : z ∈ qmaHalfPathAt p b a) (hw : z ∈ qmaHalfPathAt q c d) : p = q ∧ a = d := by
  obtain ⟨u,hu,heu⟩ := List.mem_map.mp hz
  obtain ⟨v,hv,hev⟩ := List.mem_map.mp hw
  have hh := qmaCellTranslate_unique (qmaHalfCorridor_bounded b a u hu)
    (qmaHalfCorridor_bounded c d v hv) (heu.trans hev.symm)
  rcases hh with ⟨rfl,rfl⟩
  have hbc : b = c := hb.trans hc.symm
  have hv' : u ∈ qmaHalfCorridorPath b d := by rw [hbc]; exact hv
  refine ⟨rfl,?_⟩
  by_contra had
  exact Finset.disjoint_left.mp (qmaHalfCorridor_disjoint b a d had)
    (List.mem_toFinset.mpr hu) (List.mem_toFinset.mpr hv')

end ContinuumCoulomb

end

end OAI
