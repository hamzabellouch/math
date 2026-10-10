import OAI.Geometry.IsometricImmersion.CoordinateMain
import OAI.Geometry.IsometricImmersion.LocalDomains

namespace OAI

noncomputable section
open Set TopologicalSpace
open scoped ContDiff Topology Manifold Matrix

namespace SmoothLocal.Geometry

def coordinateSquareOpen : Opens Coord :=
  ⟨square, SmoothLocal.ODE.coordinate_square_isOpen⟩

theorem zero_mem_coordinateSquareOpen : (0 : Coord) ∈ coordinateSquareOpen := by
  intro i
  norm_num

theorem relativelyOpen_square_iff {U : Set Coord} (hUS : U ⊆ square) :
    IsOpen ((Subtype.val : coordinateSquareOpen → Coord) ⁻¹' U) ↔ IsOpen U := by
  constructor
  · intro h
    have he : (Subtype.val : coordinateSquareOpen → Coord) ''
        (Subtype.val ⁻¹' U) = U := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hp
        exact ⟨⟨p, hUS hp⟩, hp, rfl⟩
    have ho := coordinateSquareOpen.isOpen.isOpenMap_subtype_val _ h
    exact (congrArg IsOpen he).mp ho
  · intro h
    exact h.preimage continuous_subtype_val

theorem counterexampleMetric_local_smoothPositive :
    LocalSmoothPositive coordinateSquareOpen (fun p => counterexampleMetric p) :=
  (localSmoothPositive_restrict_iff coordinateSquareOpen counterexampleMetric).mpr
    counterexampleMetric_smoothPositive

theorem counterexampleMetric_no_subtype_isometric_immersion
    (U : Opens Coord) (hUS : (U : Set Coord) ⊆ square)
    (h0 : (0 : Coord) ∈ U) (F : U → Ambient) :
    ¬ LocalIsometric counterexampleMetric U F := by
  intro hF
  exact counterexampleMetric_no_local_isometric_immersion U.isOpen hUS h0
    (openDomainExtend U F 0) ((localIsometric_extend_iff _ U F 0).mp hF)

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
  refine ⟨fun p => counterexampleMetric p, counterexampleMetric_local_smoothPositive, ?_⟩
  intro U hUS h0 F hF
  exact counterexampleMetric_no_subtype_isometric_immersion U hUS h0 F hF

end SmoothLocal.Geometry

end

end OAI
