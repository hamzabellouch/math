import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelection

namespace OAI

/-! The crossing selector is constructed from physical terminal indices. Every
unselected edge avoids every selected pair; no matrix identity is assumed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMARationalExchangeGraph
variable (G : QMARationalExchangeGraph) {r : ℕ} (site : Fin r → Fin 4 → Fin G.n)

def CrossingMatch (e : G.Edge) (p : Fin r × Fin 2) : Prop :=
  (G.left e = site p.1 (if p.2 = 0 then 0 else 1) ∧
    G.right e = site p.1 (if p.2 = 0 then 2 else 3)) ∨
  (G.left e = site p.1 (if p.2 = 0 then 2 else 3) ∧
    G.right e = site p.1 (if p.2 = 0 then 0 else 1))

def crossingTag (e : G.Edge) : Option (Fin r × Fin 2) :=
  if h : ∃ p, G.CrossingMatch site e p then some (Classical.choose h) else none

theorem crossingTag_some {e : G.Edge} {p : Fin r × Fin 2} (he : G.crossingTag site e = some p) :
    G.CrossingMatch site e p := by
  unfold crossingTag at he
  split_ifs at he with h
  have hp : Classical.choose h = p := Option.some.inj he
  exact hp ▸ Classical.choose_spec h

theorem crossingTag_none {e : G.Edge} : G.crossingTag site e = none ↔ ∀ p, ¬G.CrossingMatch site e p := by
  constructor
  · intro h p hp
    unfold crossingTag at h
    split_ifs at h with hx
    exact hx ⟨p,hp⟩
  · intro h
    have hn : ¬∃ p, G.CrossingMatch site e p := by simpa only [not_exists] using h
    simp only [crossingTag,hn,dite_false]

def crossingSelection (hinj : ∀ i, Function.Injective (site i)) : QMARationalCrossingSelection G r where
  site := site
  injective := hinj
  tag := G.crossingTag site
  tagged := fun _ _ _ he => G.crossingTag_some site he

theorem retained_no_crossing (hinj : ∀ i, Function.Injective (site i))
    (e : (G.crossingSelection site hinj).retained.Edge) (p : Fin r × Fin 2) :
    ¬G.CrossingMatch site e.val p :=
  (G.crossingTag_none site).mp e.property p

end QMARationalExchangeGraph
end ContinuumCoulomb

end

end OAI
