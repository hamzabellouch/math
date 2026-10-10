import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalDegreeReduction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalSpatialPackage

namespace OAI

/-! A rational degree-three spatial simulator for the actual exchange construction. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem degreeThree_spatial {N : ℚ} (hN : 0 < N) :
    let C := (1+9*B+2*(9*B)^2)*A
    ∃ H : QMASpatialExchangeModel C (27*C),
      H.rows = M.rows ∧ H.width = M.width ∧
      H.n ≤ M.n+2*Fintype.card M.Term+36*B*Fintype.card M.Term ∧
      |H.energy-M.energy| ≤ (((9*B:ℕ):ℝ)+1)/(N:ℝ) ∧
      ∀ v, qmaGraphDegree H.left H.right v ≤ 3 := by
  dsimp only
  let P := M.placedDegreeReduction
  let G := qmaRationalDegreeReduction M.indexedLeft M.indexedRight
    (fun e => M.weight (M.termIndex.symm e)) M.constant N (9*B)
  have hr : G.real = M.degreeReduction N :=
    qmaRationalDegreeReduction_real M.indexedLeft M.indexedRight
      (fun e => M.weight (M.termIndex.symm e)) M.constant N (9*B)
  have hg : G.graph = P.graph := by
    calc
      G.graph = G.real.graph := rfl
      _ = (M.degreeReduction N).graph := congrArg QMAWeightedForkNetwork.graph hr
      _ = P.graph := (M.placedDegreeReduction_graph N).symm
  have hd : ∀ v, qmaGraphDegree P.graph.state.fullLeft P.graph.state.fullRight v ≤ 3 := by
    change ∀ v, qmaGraphDegree M.placedDegreeReduction.graph.state.fullLeft
      M.placedDegreeReduction.graph.state.fullRight v ≤ 3
    rw [M.placedDegreeReduction_graph N]
    exact M.degreeReduction_degree N
  obtain ⟨H,hrows,hwidth,hn,he,hdH⟩ := qmaRationalPlacedPackage G P hg
    M.placedDegreeReduction_density hd M.placedDegreeReduction_local
  refine ⟨H,hrows,hwidth,?_,?_,hdH⟩
  · rw [hn,show G.graph = (M.degreeReduction N).graph from congrArg QMAWeightedForkNetwork.graph hr]
    exact M.degreeReduction_vertices N
  · rw [he,hr]
    exact M.degreeReduction_energy (by exact_mod_cast hN)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
