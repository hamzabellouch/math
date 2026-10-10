import OAI.Analysis.Triangular.Signs.SineGridDefs

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors10 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 10 k j) ∧ cellBarrier 10 < ∏ j : Fin 15,(cellFactor 10 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 10 k j) ∧ cellBarrier 10 < ∏ j : Fin 15,(cellFactor 10 k j)^2 by decide +kernel) k
lemma cellGeometry10 (k : Fin 100) :
    0≤cellMagnitude 10 k ∧ cellMagnitude 10 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 10 → 0≤cellSeparation 10 k j ∧ cellSeparation 10 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 10 k ∧ cellMagnitude 10 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 10 → 0≤cellSeparation 10 k j ∧ cellSeparation 10 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors11 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 11 k j) ∧ cellBarrier 11 < ∏ j : Fin 15,(cellFactor 11 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 11 k j) ∧ cellBarrier 11 < ∏ j : Fin 15,(cellFactor 11 k j)^2 by decide +kernel) k
lemma cellGeometry11 (k : Fin 100) :
    0≤cellMagnitude 11 k ∧ cellMagnitude 11 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 11 → 0≤cellSeparation 11 k j ∧ cellSeparation 11 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 11 k ∧ cellMagnitude 11 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 11 → 0≤cellSeparation 11 k j ∧ cellSeparation 11 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors12 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 12 k j) ∧ cellBarrier 12 < ∏ j : Fin 15,(cellFactor 12 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 12 k j) ∧ cellBarrier 12 < ∏ j : Fin 15,(cellFactor 12 k j)^2 by decide +kernel) k
lemma cellGeometry12 (k : Fin 100) :
    0≤cellMagnitude 12 k ∧ cellMagnitude 12 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 12 → 0≤cellSeparation 12 k j ∧ cellSeparation 12 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 12 k ∧ cellMagnitude 12 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 12 → 0≤cellSeparation 12 k j ∧ cellSeparation 12 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors13 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 13 k j) ∧ cellBarrier 13 < ∏ j : Fin 15,(cellFactor 13 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 13 k j) ∧ cellBarrier 13 < ∏ j : Fin 15,(cellFactor 13 k j)^2 by decide +kernel) k
lemma cellGeometry13 (k : Fin 100) :
    0≤cellMagnitude 13 k ∧ cellMagnitude 13 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 13 → 0≤cellSeparation 13 k j ∧ cellSeparation 13 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 13 k ∧ cellMagnitude 13 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 13 → 0≤cellSeparation 13 k j ∧ cellSeparation 13 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors14 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 14 k j) ∧ cellBarrier 14 < ∏ j : Fin 15,(cellFactor 14 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 14 k j) ∧ cellBarrier 14 < ∏ j : Fin 15,(cellFactor 14 k j)^2 by decide +kernel) k
lemma cellGeometry14 (k : Fin 100) :
    0≤cellMagnitude 14 k ∧ cellMagnitude 14 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 14 → 0≤cellSeparation 14 k j ∧ cellSeparation 14 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 14 k ∧ cellMagnitude 14 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 14 → 0≤cellSeparation 14 k j ∧ cellSeparation 14 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors15 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 15 k j) ∧ cellBarrier 15 < ∏ j : Fin 15,(cellFactor 15 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 15 k j) ∧ cellBarrier 15 < ∏ j : Fin 15,(cellFactor 15 k j)^2 by decide +kernel) k
lemma cellGeometry15 (k : Fin 100) :
    0≤cellMagnitude 15 k ∧ cellMagnitude 15 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 15 → 0≤cellSeparation 15 k j ∧ cellSeparation 15 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 15 k ∧ cellMagnitude 15 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 15 → 0≤cellSeparation 15 k j ∧ cellSeparation 15 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors16 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 16 k j) ∧ cellBarrier 16 < ∏ j : Fin 15,(cellFactor 16 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 16 k j) ∧ cellBarrier 16 < ∏ j : Fin 15,(cellFactor 16 k j)^2 by decide +kernel) k
lemma cellGeometry16 (k : Fin 100) :
    0≤cellMagnitude 16 k ∧ cellMagnitude 16 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 16 → 0≤cellSeparation 16 k j ∧ cellSeparation 16 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 16 k ∧ cellMagnitude 16 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 16 → 0≤cellSeparation 16 k j ∧ cellSeparation 16 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors17 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 17 k j) ∧ cellBarrier 17 < ∏ j : Fin 15,(cellFactor 17 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 17 k j) ∧ cellBarrier 17 < ∏ j : Fin 15,(cellFactor 17 k j)^2 by decide +kernel) k
lemma cellGeometry17 (k : Fin 100) :
    0≤cellMagnitude 17 k ∧ cellMagnitude 17 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 17 → 0≤cellSeparation 17 k j ∧ cellSeparation 17 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 17 k ∧ cellMagnitude 17 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 17 → 0≤cellSeparation 17 k j ∧ cellSeparation 17 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors18 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 18 k j) ∧ cellBarrier 18 < ∏ j : Fin 15,(cellFactor 18 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 18 k j) ∧ cellBarrier 18 < ∏ j : Fin 15,(cellFactor 18 k j)^2 by decide +kernel) k
lemma cellGeometry18 (k : Fin 100) :
    0≤cellMagnitude 18 k ∧ cellMagnitude 18 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 18 → 0≤cellSeparation 18 k j ∧ cellSeparation 18 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 18 k ∧ cellMagnitude 18 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 18 → 0≤cellSeparation 18 k j ∧ cellSeparation 18 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellFactors19 (k : Fin 100) :
    (∀ j : Fin 15, 0≤cellFactor 19 k j) ∧ cellBarrier 19 < ∏ j : Fin 15,(cellFactor 19 k j)^2 := by
  exact (show ∀ k : Fin 100,
    (∀ j : Fin 15, 0≤cellFactor 19 k j) ∧ cellBarrier 19 < ∏ j : Fin 15,(cellFactor 19 k j)^2 by decide +kernel) k
lemma cellGeometry19 (k : Fin 100) :
    0≤cellMagnitude 19 k ∧ cellMagnitude 19 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 19 → 0≤cellSeparation 19 k j ∧ cellSeparation 19 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0≤cellMagnitude 19 k ∧ cellMagnitude 19 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 19 → 0≤cellSeparation 19 k j ∧ cellSeparation 19 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
