import OAI.Analysis.Triangular.Signs.SineGridDefs

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors00 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 0 k j) ∧ cellBarrier 0 < ∏ j : Fin 15,(cellFactor 0 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 0 k j) ∧ cellBarrier 0 < ∏ j : Fin 15,(cellFactor 0 k j)^2 by decide +kernel) k
lemma cellGeometry00 (k : Fin 100) :
    0≤cellMagnitude 0 k ∧ cellMagnitude 0 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 0 → 0≤cellSeparation 0 k j ∧ cellSeparation 0 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 0 k ∧ cellMagnitude 0 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 0 → 0≤cellSeparation 0 k j ∧ cellSeparation 0 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors01 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 1 k j) ∧ cellBarrier 1 < ∏ j : Fin 15,(cellFactor 1 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 1 k j) ∧ cellBarrier 1 < ∏ j : Fin 15,(cellFactor 1 k j)^2 by decide +kernel) k
lemma cellGeometry01 (k : Fin 100) :
    0≤cellMagnitude 1 k ∧ cellMagnitude 1 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 1 → 0≤cellSeparation 1 k j ∧ cellSeparation 1 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 1 k ∧ cellMagnitude 1 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 1 → 0≤cellSeparation 1 k j ∧ cellSeparation 1 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors02 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 2 k j) ∧ cellBarrier 2 < ∏ j : Fin 15,(cellFactor 2 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 2 k j) ∧ cellBarrier 2 < ∏ j : Fin 15,(cellFactor 2 k j)^2 by decide +kernel) k
lemma cellGeometry02 (k : Fin 100) :
    0≤cellMagnitude 2 k ∧ cellMagnitude 2 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 2 → 0≤cellSeparation 2 k j ∧ cellSeparation 2 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 2 k ∧ cellMagnitude 2 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 2 → 0≤cellSeparation 2 k j ∧ cellSeparation 2 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors03 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 3 k j) ∧ cellBarrier 3 < ∏ j : Fin 15,(cellFactor 3 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 3 k j) ∧ cellBarrier 3 < ∏ j : Fin 15,(cellFactor 3 k j)^2 by decide +kernel) k
lemma cellGeometry03 (k : Fin 100) :
    0≤cellMagnitude 3 k ∧ cellMagnitude 3 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 3 → 0≤cellSeparation 3 k j ∧ cellSeparation 3 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 3 k ∧ cellMagnitude 3 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 3 → 0≤cellSeparation 3 k j ∧ cellSeparation 3 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors04 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 4 k j) ∧ cellBarrier 4 < ∏ j : Fin 15,(cellFactor 4 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 4 k j) ∧ cellBarrier 4 < ∏ j : Fin 15,(cellFactor 4 k j)^2 by decide +kernel) k
lemma cellGeometry04 (k : Fin 100) :
    0≤cellMagnitude 4 k ∧ cellMagnitude 4 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 4 → 0≤cellSeparation 4 k j ∧ cellSeparation 4 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 4 k ∧ cellMagnitude 4 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 4 → 0≤cellSeparation 4 k j ∧ cellSeparation 4 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors05 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 5 k j) ∧ cellBarrier 5 < ∏ j : Fin 15,(cellFactor 5 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 5 k j) ∧ cellBarrier 5 < ∏ j : Fin 15,(cellFactor 5 k j)^2 by decide +kernel) k
lemma cellGeometry05 (k : Fin 100) :
    0≤cellMagnitude 5 k ∧ cellMagnitude 5 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 5 → 0≤cellSeparation 5 k j ∧ cellSeparation 5 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 5 k ∧ cellMagnitude 5 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 5 → 0≤cellSeparation 5 k j ∧ cellSeparation 5 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors06 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 6 k j) ∧ cellBarrier 6 < ∏ j : Fin 15,(cellFactor 6 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 6 k j) ∧ cellBarrier 6 < ∏ j : Fin 15,(cellFactor 6 k j)^2 by decide +kernel) k
lemma cellGeometry06 (k : Fin 100) :
    0≤cellMagnitude 6 k ∧ cellMagnitude 6 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 6 → 0≤cellSeparation 6 k j ∧ cellSeparation 6 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 6 k ∧ cellMagnitude 6 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 6 → 0≤cellSeparation 6 k j ∧ cellSeparation 6 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors07 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 7 k j) ∧ cellBarrier 7 < ∏ j : Fin 15,(cellFactor 7 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 7 k j) ∧ cellBarrier 7 < ∏ j : Fin 15,(cellFactor 7 k j)^2 by decide +kernel) k
lemma cellGeometry07 (k : Fin 100) :
    0≤cellMagnitude 7 k ∧ cellMagnitude 7 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 7 → 0≤cellSeparation 7 k j ∧ cellSeparation 7 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 7 k ∧ cellMagnitude 7 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 7 → 0≤cellSeparation 7 k j ∧ cellSeparation 7 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors08 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 8 k j) ∧ cellBarrier 8 < ∏ j : Fin 15,(cellFactor 8 k j)^2 by decide +kernel) k
lemma cellGeometry08 (k : Fin 100) :
    0≤cellMagnitude 8 k ∧ cellMagnitude 8 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 8 → 0≤cellSeparation 8 k j ∧ cellSeparation 8 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 8 k ∧ cellMagnitude 8 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 8 → 0≤cellSeparation 8 k j ∧ cellSeparation 8 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors09 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 9 k j) ∧ cellBarrier 9 < ∏ j : Fin 15,(cellFactor 9 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 9 k j) ∧ cellBarrier 9 < ∏ j : Fin 15,(cellFactor 9 k j)^2 by decide +kernel) k
lemma cellGeometry09 (k : Fin 100) :
    0≤cellMagnitude 9 k ∧ cellMagnitude 9 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 9 → 0≤cellSeparation 9 k j ∧ cellSeparation 9 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 9 k ∧ cellMagnitude 9 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 9 → 0≤cellSeparation 9 k j ∧ cellSeparation 9 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
