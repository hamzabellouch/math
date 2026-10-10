import OAI.GroupTheory.PolycyclicRecognition.Geometry.ManifoldRelatedBracket
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothLieNaturality

namespace OAI

/-! # Differentiating C-infinity Lie-group homomorphisms

The differential preserves brackets because the associated invariant
vector fields are related by the homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition.SmoothLie

open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ∞ H]

local instance : LieGroup (𝓘(ℝ, E)) (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞) (by simp)
local instance : LieGroup (𝓘(ℝ, F)) (minSmoothness ℝ 3) H :=
  LieGroup.of_le (n := ∞) (by simp)

def homDifferentialLinear (φ : G →* H) :
    GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, F)) H :=
  (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 : E →L[ℝ] F).toLinearMap

theorem mfderiv_hom_map_bracket (φ : G →* H)
    (hφ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ)
    (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    homDifferentialLinear (E := E) (F := F) φ ⁅v, w⁆ = ⁅homDifferentialLinear (E := E) (F := F) φ v, homDifferentialLinear (E := E) (F := F) φ w⁆ := by
  have hd := hφ.mdifferentiable (by simp)
  have hh := mfderiv_mlieBracket_of_manifold_related hφ
    (contMDiff_invariantVectorField_infty v) (contMDiff_invariantVectorField_infty w)
    (contMDiff_invariantVectorField_infty (homDifferentialLinear (E := E) (F := F) φ v))
    (contMDiff_invariantVectorField_infty (homDifferentialLinear (E := E) (F := F) φ w))
    (mfderiv_hom_invariant φ hd v) (mfderiv_hom_invariant φ hd w) 1
  let B : H → F := fun y => VectorField.mlieBracket (𝓘(ℝ, F))
    (mulInvariantVectorField (homDifferentialLinear (E := E) (F := F) φ v))
    (mulInvariantVectorField (homDifferentialLinear (E := E) (F := F) φ w)) y
  exact hh.trans (congrArg B φ.map_one)

def homLieDifferential (φ : G →* H)
    (hφ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ) :
    GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, F)) H where
  toLinearMap := homDifferentialLinear (E := E) (F := F) φ
  map_lie' := fun {v w} => mfderiv_hom_map_bracket φ hφ v w

@[simp] theorem homLieDifferential_apply (φ : G →* H)
    (hφ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    homLieDifferential φ hφ v = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 v := rfl

end PolycyclicRecognition.SmoothLie

end

end OAI
