import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace OAI

noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

abbrev Coord := Fin 2 → ℝ

abbrev Ambient := EuclideanSpace ℝ (Fin 3)

def square : Set Coord := {p | ∀ i, p i ∈ Set.Ioo (-1 : ℝ) 1}

def LocalSmoothPositive (U : Opens Coord)
    (g : U → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i j, ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, ℝ) ∞ (fun p => g p i j)) ∧
    ∀ p, (g p).PosDef

end SmoothLocal.Geometry

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinate_square_isOpen : IsOpen square := by
  have heq : square = ⋂ i : Fin 2,
      (fun p : Coord => p i) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext p
    simp [square]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

end SmoothLocal.ODE

namespace SmoothLocal.Geometry

def coordinateSquareOpen : Opens Coord :=
  ⟨square, SmoothLocal.ODE.coordinate_square_isOpen⟩

theorem exists_local_metric_without_local_immersion :
    ∃ g : coordinateSquareOpen → Matrix (Fin 2) (Fin 2) ℝ,
      LocalSmoothPositive coordinateSquareOpen g ∧
      ∀ U : Opens Coord, ∀ hUS : (U : Set Coord) ⊆ square,
        (0 : Coord) ∈ U → ∀ F : U → Ambient,
          ¬ (ContMDiff 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) ∞ F ∧
            ∀ p : U, ∀ v w : Coord,
              (inner ℝ : Ambient → Ambient → ℝ) (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p v)
                (mfderiv 𝓘(ℝ, Coord) 𝓘(ℝ, Ambient) F p w) =
                  v ⬝ᵥ (g ⟨p, hUS p.property⟩ *ᵥ w)) := by
  sorry

end SmoothLocal.Geometry

end

end OAI
