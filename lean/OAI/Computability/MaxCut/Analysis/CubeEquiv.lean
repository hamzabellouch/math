import Mathlib
import OAI.Computability.MaxCut.Estimates.Dictator

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Hastad

/-- Fixed binary radix indexing, rather than a chosen `Fintype.equivFin`. -/
def cubeEquiv (q : ℕ) : Cube (Fin q) ≃ Fin (2 ^ q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Row-major indexing before the explicit finite-field blowup. -/
def vertexEquiv (n q : ℕ) : (Fin n × Cube (Fin q)) ≃ Fin (n * 2 ^ q) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) (cubeEquiv q)).trans finProdFinEquiv

noncomputable def output {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1 : ℚ) 1) (K : ℕ) : ScaledGraph :=
  (ofInstance g).output t ht (vertexEquiv g.vertices q) K

 theorem output_vertex_bound {q : ℕ} (g : Instance q) (t : ℚ)
    (ht : t ∈ Set.Icc (-1 : ℚ) 1) (K : ℕ) :
    (output g t ht K).graph.vertices ≤
      (g.vertices * 2 ^ q) * (2 * (K * (g.vertices * 2 ^ q + 1) ^ 2 + 1)) ^ 6 :=
  Game.output_vertex_bound _ _ _ _ _

end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
