import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.NormalPatch

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

def hermitianCenterExtension {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain) :
    SchwartzMap Space (Space →L[ℝ] Space) :=
  SchwartzCutoff.schwartz D.domain_open
    ((coordinateJ_smooth J p).mono D.domain_subset) hφ hc hφD

lemma hermitianCenterExtension_eq {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {b : Space} (hφb : φ b = 1) :
    hermitianCenterExtension J p D hφ hc hφD b = coordinateJ J p b := by
  simp only [hermitianCenterExtension,SchwartzCutoff.schwartz_apply,hφb,one_smul]

lemma hermitianCenterExtension_square {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {b : Space} (hφb : φ b = 1) (v : Space) :
    hermitianCenterExtension J p D hφ hc hφD b
      (hermitianCenterExtension J p D hφ hc hφD b v) = -v := by
  have hb : b ∈ D.domain := hφD (subset_tsupport φ (by simp [Function.mem_support,hφb]))
  rw [hermitianCenterExtension_eq J p D hφ hc hφD hφb]
  exact coordinateJ_square J p (D.domain_subset hb) v

end TamingCompatibility.GeometricChart

end

end OAI
