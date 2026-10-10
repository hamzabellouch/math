import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkBackground

namespace OAI

/-! A repeatable fork stage: only active stars may have large degree. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical

structure QMAForkState (n c : ℕ) (d : Fin c → ℕ) (ν : Type*) [Fintype ν] where
  ports : QMAForkPorts n c d
  left : ν → Fin n
  right : ν → Fin n
  distinct : ∀ e, left e ≠ right e
  degree_le : ∀ v, qmaGraphDegree left right v ≤ 3
  center_degree : ∀ i, qmaGraphDegree left right (ports.center i) = 0
  port_degree : ∀ p, qmaGraphDegree left right (ports.port p) ≤ 1

namespace QMAForkState
variable {n c : ℕ} {d : Fin c → ℕ} {ν : Type*} [Fintype ν]
variable (G : QMAForkState n c d ν)

abbrev NextEdge := (ν ⊕ Fin G.ports.pairCount) ⊕
  (Fin G.ports.pairCount ⊕ (Fin G.ports.pairCount × Fin 2))

theorem site_away_center (i : Fin c) (e : Fin G.ports.pairCount) :
    G.ports.site e 1 ≠ G.ports.center i ∧ G.ports.site e 2 ≠ G.ports.center i := by
  constructor <;> exact fun h => G.ports.center_ne_port _ _ h.symm

theorem site_away_remaining (p : QMAForkRemainder d) (e : Fin G.ports.pairCount) :
    G.ports.site e 1 ≠ G.ports.port (qmaForkRemainingPort d p) ∧
      G.ports.site e 2 ≠ G.ports.port (qmaForkRemainingPort d p) := by
  constructor <;> intro h
  · exact qmaForkPairedPort_ne_remaining d _ p (G.ports.port_injective h)
  · exact qmaForkPairedPort_ne_remaining d _ p (G.ports.port_injective h)

def next : QMAForkState (n + G.ports.pairCount*2) c
    (fun i => d i / 2 + d i % 2) G.NextEdge where
  ports := G.ports.next
  left := qmaForkBackgroundLeft G.left G.ports.site
  right := qmaForkBackgroundRight G.right G.ports.site
  distinct := qmaParallelGraph_distinct _ _
    (qmaForksBase_distinct G.left G.right G.distinct G.ports.site G.ports.site_injective)
    (fun e b => qmaForkOuter G.ports.site (e,b)) (fun _ _ => 1)
  degree_le := qmaForkBackground_degree_le_three G.left G.right G.ports.site
    G.ports.site_injective G.ports.outer_injective G.degree_le (by
      intro e b
      fin_cases b <;> exact G.port_degree _)
  center_degree := by
    intro i
    change qmaGraphDegree _ _ (old n G.ports.pairCount (G.ports.center i)) = 0
    rw [qmaForkBackground_away_degree G.left G.right G.ports.site
      G.ports.site_injective _ (G.site_away_center i)]
    exact G.center_degree i
  port_degree := by
    intro p
    change qmaGraphDegree _ _ (G.ports.nextPortAux (G.ports.nextPortEquiv p)) ≤ 1
    rcases G.ports.nextPortEquiv p with p | p
    · change qmaGraphDegree _ _ (fresh n G.ports.pairCount (G.ports.pairEquiv p) 0) ≤ 1
      rw [qmaForkBackground_new_degree]
      norm_num
    · change qmaGraphDegree _ _ (old n G.ports.pairCount
        (G.ports.port (qmaForkRemainingPort d p))) ≤ 1
      rw [qmaForkBackground_away_degree G.left G.right G.ports.site
        G.ports.site_injective _ (G.site_away_remaining p)]
      exact G.port_degree _

end QMAForkState
end ContinuumCoulomb

end

end OAI
