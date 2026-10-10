import OAI.Analysis.Triangular.Signs.SineGridDefs

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors20 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 20 k j) ∧ cellBarrier 20 < ∏ j : Fin 15,(cellFactor 20 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 20 k j) ∧ cellBarrier 20 < ∏ j : Fin 15,(cellFactor 20 k j)^2 by decide +kernel) k
lemma cellGeometry20 (k : Fin 100) :
    0≤cellMagnitude 20 k ∧ cellMagnitude 20 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 20 → 0≤cellSeparation 20 k j ∧ cellSeparation 20 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 20 k ∧ cellMagnitude 20 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 20 → 0≤cellSeparation 20 k j ∧ cellSeparation 20 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors21 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 21 k j) ∧ cellBarrier 21 < ∏ j : Fin 15,(cellFactor 21 k j)^2 by decide +kernel) k
lemma cellGeometry21 (k : Fin 100) :
    0≤cellMagnitude 21 k ∧ cellMagnitude 21 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 21 → 0≤cellSeparation 21 k j ∧ cellSeparation 21 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 21 k ∧ cellMagnitude 21 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 21 → 0≤cellSeparation 21 k j ∧ cellSeparation 21 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors22 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 22 k j) ∧ cellBarrier 22 < ∏ j : Fin 15,(cellFactor 22 k j)^2 by decide +kernel) k
lemma cellGeometry22 (k : Fin 100) :
    0≤cellMagnitude 22 k ∧ cellMagnitude 22 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 22 → 0≤cellSeparation 22 k j ∧ cellSeparation 22 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 22 k ∧ cellMagnitude 22 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 22 → 0≤cellSeparation 22 k j ∧ cellSeparation 22 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors23 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 23 k j) ∧ cellBarrier 23 < ∏ j : Fin 15,(cellFactor 23 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 23 k j) ∧ cellBarrier 23 < ∏ j : Fin 15,(cellFactor 23 k j)^2 by decide +kernel) k
lemma cellGeometry23 (k : Fin 100) :
    0≤cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0≤cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 23 k ∧ cellMagnitude 23 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 23 → 0≤cellSeparation 23 k j ∧ cellSeparation 23 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors24 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 24 k j) ∧ cellBarrier 24 < ∏ j : Fin 15,(cellFactor 24 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 24 k j) ∧ cellBarrier 24 < ∏ j : Fin 15,(cellFactor 24 k j)^2 by decide +kernel) k
lemma cellGeometry24 (k : Fin 100) :
    0≤cellMagnitude 24 k ∧ cellMagnitude 24 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 24 → 0≤cellSeparation 24 k j ∧ cellSeparation 24 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 24 k ∧ cellMagnitude 24 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 24 → 0≤cellSeparation 24 k j ∧ cellSeparation 24 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors25 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 25 k j) ∧ cellBarrier 25 < ∏ j : Fin 15,(cellFactor 25 k j)^2 by decide +kernel) k
lemma cellGeometry25 (k : Fin 100) :
    0≤cellMagnitude 25 k ∧ cellMagnitude 25 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 25 → 0≤cellSeparation 25 k j ∧ cellSeparation 25 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 25 k ∧ cellMagnitude 25 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 25 → 0≤cellSeparation 25 k j ∧ cellSeparation 25 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors26 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 26 k j) ∧ cellBarrier 26 < ∏ j : Fin 15,(cellFactor 26 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 26 k j) ∧ cellBarrier 26 < ∏ j : Fin 15,(cellFactor 26 k j)^2 by decide +kernel) k
lemma cellGeometry26 (k : Fin 100) :
    0≤cellMagnitude 26 k ∧ cellMagnitude 26 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 26 → 0≤cellSeparation 26 k j ∧ cellSeparation 26 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 26 k ∧ cellMagnitude 26 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 26 → 0≤cellSeparation 26 k j ∧ cellSeparation 26 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors27 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 27 k j) ∧ cellBarrier 27 < ∏ j : Fin 15,(cellFactor 27 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 27 k j) ∧ cellBarrier 27 < ∏ j : Fin 15,(cellFactor 27 k j)^2 by decide +kernel) k
lemma cellGeometry27 (k : Fin 100) :
    0≤cellMagnitude 27 k ∧ cellMagnitude 27 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 27 → 0≤cellSeparation 27 k j ∧ cellSeparation 27 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 27 k ∧ cellMagnitude 27 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 27 → 0≤cellSeparation 27 k j ∧ cellSeparation 27 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors28 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 28 k j) ∧ cellBarrier 28 < ∏ j : Fin 15,(cellFactor 28 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 28 k j) ∧ cellBarrier 28 < ∏ j : Fin 15,(cellFactor 28 k j)^2 by decide +kernel) k
lemma cellGeometry28 (k : Fin 100) :
    0≤cellMagnitude 28 k ∧ cellMagnitude 28 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 28 → 0≤cellSeparation 28 k j ∧ cellSeparation 28 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 28 k ∧ cellMagnitude 28 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 28 → 0≤cellSeparation 28 k j ∧ cellSeparation 28 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors29 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 29 k j) ∧ cellBarrier 29 < ∏ j : Fin 15,(cellFactor 29 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 29 k j) ∧ cellBarrier 29 < ∏ j : Fin 15,(cellFactor 29 k j)^2 by decide +kernel) k
lemma cellGeometry29 (k : Fin 100) :
    0≤cellMagnitude 29 k ∧ cellMagnitude 29 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 29 → 0≤cellSeparation 29 k j ∧ cellSeparation 29 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 29 k ∧ cellMagnitude 29 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 29 → 0≤cellSeparation 29 k j ∧ cellSeparation 29 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
