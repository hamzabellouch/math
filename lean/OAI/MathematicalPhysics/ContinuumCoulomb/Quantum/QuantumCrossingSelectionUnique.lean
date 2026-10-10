import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSelectFromSites

namespace OAI

/-! Disjoint physical terminal sets make crossing-edge assignment unique.
Consequently the finite endpoint test computes the canonical selection. -/

noncomputable section
namespace ContinuumCoulomb.QMARationalExchangeGraph
open scoped Classical

private theorem crossingMatch_left_parity (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n) (e : G.Edge) (p : Fin r × Fin 2)
    (h : G.CrossingMatch site e p) :
    ∃ k : Fin 4, site p.1 k=G.left e ∧ k.val%2=p.2.val := by
  rcases p with ⟨i,a⟩
  fin_cases a
  · rcases h with ⟨hl,_⟩ | ⟨hl,_⟩
    · exact ⟨0,hl.symm,rfl⟩
    · exact ⟨2,hl.symm,rfl⟩
  · rcases h with ⟨hl,_⟩ | ⟨hl,_⟩
    · exact ⟨1,hl.symm,rfl⟩
    · exact ⟨3,hl.symm,rfl⟩

theorem crossingMatch_unique (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    {e : G.Edge} {p q : Fin r × Fin 2}
    (hp : G.CrossingMatch site e p) (hq : G.CrossingMatch site e q) : p=q := by
  obtain ⟨a,ha,hpa⟩ := crossingMatch_left_parity G site e p hp
  obtain ⟨b,hb,hqb⟩ := crossingMatch_left_parity G site e q hq
  have hi : (p.1,a)=(q.1,b) := hinj (ha.trans hb.symm)
  have hab : a=b := congrArg Prod.snd hi
  have hindex : p.1=q.1 := congrArg (fun z : Fin r × Fin 4 => z.1) hi
  refine Prod.ext hindex (Fin.ext ?_)
  rw [← hpa,← hqb,hab]

theorem crossingTag_some_iff (G : QMARationalExchangeGraph) {r : ℕ}
    (site : Fin r → Fin 4 → Fin G.n)
    (hinj : Function.Injective (fun p : Fin r × Fin 4 => site p.1 p.2))
    (e : G.Edge) (p : Fin r × Fin 2) :
    G.crossingTag site e=some p ↔ G.CrossingMatch site e p := by
  constructor
  · exact G.crossingTag_some site
  · intro hp
    cases ht : G.crossingTag site e with
    | none => exact ((G.crossingTag_none site).mp ht p hp).elim
    | some q =>
      have hq := G.crossingTag_some site ht
      have hqp := G.crossingMatch_unique site hinj hq hp
      exact congrArg some hqp

end ContinuumCoulomb.QMARationalExchangeGraph

end

end OAI
