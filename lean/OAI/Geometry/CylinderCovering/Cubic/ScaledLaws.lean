import OAI.Geometry.CylinderCovering.Angular.CubicScaledFamily
import OAI.Geometry.CylinderCovering.Angular.CubicCost

namespace OAI

noncomputable section
namespace CylinderCovering.Cubic
open Set TriangularCovering

lemma scaledFiniteFamily_vertex_laws (ε : ℝ) (hε : 0 < ε) :
    ∀ j : Fin (n ε),
      let a := node (n ε) j
      let b := node (n ε) (j + 1)
      let T := cap ε a b / 2
      (scaledFiniteFamily ε hε (lowerIndex ε j)).axis =
        normalizedDirection (lowerDirection ε a b) ∧
      (scaledFiniteFamily ε hε (lowerIndex ε j)).base =
        projection (normalizedDirection (lowerDirection ε a b)) ''
          convexHull ℝ (range (TriangularCovering.lowerVertices a b T)) ∧
      (scaledFiniteFamily ε hε (upperIndex ε j)).axis =
        normalizedDirection (upperDirection ε a b) ∧
      (scaledFiniteFamily ε hε (upperIndex ε j)).base =
        projection (normalizedDirection (upperDirection ε a b)) ''
          convexHull ℝ (range (TriangularCovering.upperVertices a b T)) := by
  intro j
  simp only [lowerIndex, upperIndex, scaledFiniteFamily, Function.comp_apply,
    Fin.cast_cast, Fin.cast_eq_self, Fin.append_left, Fin.append_right]
  exact ⟨rfl, rfl, rfl, rfl⟩

lemma scaled_lowerDirection (τ a b : ℝ) :
    lowerDirection (τ / 2) a b =
      tiltV τ (TriangularCovering.alpha a b) (TriangularCovering.beta a b) := by
  ext i
  fin_cases i <;>
    dsimp [lowerDirection, tiltV, alpha, beta, TriangularCovering.alpha, TriangularCovering.beta] <;>
    ring

lemma scaled_upperDirection (τ a b : ℝ) :
    upperDirection (τ / 2) a b =
      tiltW τ (TriangularCovering.alpha a b) (TriangularCovering.beta a b) := by
  ext i
  fin_cases i <;>
    dsimp [upperDirection, tiltW, alpha, beta, TriangularCovering.alpha, TriangularCovering.beta] <;>
    ring

lemma lower_vertices_contract (a b T : ℝ) (i : Fin 3) :
    point 0 0 (1 / 2) + (1 / 2 : ℝ) • CubicLowerGeometry.vertices a b T i =
      TriangularCovering.lowerVertices a b (T / 2) i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    dsimp [CubicLowerGeometry.vertices, TriangularCovering.lowerVertices, point] <;> ring

lemma upper_vertices_contract (a b T : ℝ) (i : Fin 3) :
    point 0 0 (1 / 2) + (1 / 2 : ℝ) • TriangularCovering.upperVertices a b T i =
      TriangularCovering.upperVertices a b (T / 2) i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    dsimp [TriangularCovering.upperVertices, point] <;> ring

end CylinderCovering.Cubic

end

end OAI
