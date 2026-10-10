import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDegreeReduction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialExchange
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridNeighbors

namespace OAI

/-! Apply the constant-round degree reduction to the actual spatial exchange family. -/

noncomputable section
namespace ContinuumCoulomb
open MediatorGraph
open scoped BigOperators Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def termIndex : M.Term ≃ Fin (Fintype.card M.Term) := Fintype.equivFin _
def indexedLeft (e : Fin (Fintype.card M.Term)) : Fin M.n := M.left (M.termIndex.symm e)
def indexedRight (e : Fin (Fintype.card M.Term)) : Fin M.n := M.right (M.termIndex.symm e)
def indexedWeight (e : Fin (Fintype.card M.Term)) : ℝ := M.weight (M.termIndex.symm e)

theorem indexed_distinct (e : Fin (Fintype.card M.Term)) : M.indexedLeft e ≠ M.indexedRight e :=
  M.distinct _

theorem graphDegree_bound (v : Fin M.n) : qmaGraphDegree M.left M.right v ≤ 9*B := by
  have h := qmaGrid_incidence_bound M.cell M.anchor (fun e => {M.left e,M.right e})
    (by
      intro e q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact (M.geometry e).1
      · exact (M.geometry e).2) M.termDensity v
  simpa [qmaGraphDegree,eq_comm] using h

theorem indexed_degree_bound (v : Fin M.n) :
    qmaGraphDegree M.indexedLeft M.indexedRight v ≤ 9*B := by
  have h := M.termIndex.symm.sum_comp
    (fun e => if M.left e = v ∨ M.right e = v then (1:ℕ) else 0)
  change qmaGraphDegree M.indexedLeft M.indexedRight v = qmaGraphDegree M.left M.right v at h
  exact h.le.trans (M.graphDegree_bound v)

theorem indexed_matrix : qmaExchangeMatrix M.indexedLeft M.indexedRight M.indexedWeight M.constant =
    qmaExchangeMatrix M.left M.right (fun e => (M.weight e:ℝ)) M.constant := by
  have h := M.termIndex.symm.sum_comp (fun e => ((M.weight e:ℝ):ℂ) •
    sourceHeisenbergMatrix M.n (M.left e) (M.right e))
  unfold qmaExchangeMatrix
  exact congrArg (fun s => s+(M.constant:ℂ) • 1) h

def degreeReduction (N : ℝ) : QMAWeightedForkNetwork M.n :=
  qmaDegreeReduction M.indexedLeft M.indexedRight M.indexedWeight M.constant N (9*B)

theorem degreeReduction_degree (N : ℝ) :
    ∀ v, qmaGraphDegree (M.degreeReduction N).graph.state.fullLeft
      (M.degreeReduction N).graph.state.fullRight v ≤ 3 :=
  qmaDegreeReduction_degree M.indexedLeft M.indexedRight M.indexed_distinct M.indexedWeight
    M.constant N (9*B) M.indexed_degree_bound

theorem degreeReduction_energy {N : ℝ} (hN : 0 < N) :
    |(M.degreeReduction N).energy-M.energy| ≤ (((9*B:ℕ):ℝ)+1)/N := by
  have h := qmaDegreeReduction_energy M.indexedLeft M.indexedRight M.indexed_distinct
    M.indexedWeight M.constant hN (9*B)
  rw [M.indexed_matrix] at h
  exact h

theorem degreeReduction_vertices (N : ℝ) :
    (M.degreeReduction N).graph.n ≤ M.n+2*Fintype.card M.Term+36*B*Fintype.card M.Term := by
  have h := qmaDegreeReduction_vertices M.indexedLeft M.indexedRight M.indexedWeight M.constant N (9*B)
  calc
    _ ≤ M.n+2*Fintype.card M.Term+4*(9*B)*Fintype.card M.Term := h
    _ = _ := by ring

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
