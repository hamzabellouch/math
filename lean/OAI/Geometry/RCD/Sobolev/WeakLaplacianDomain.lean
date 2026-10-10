import OAI.Geometry.RCD.Coordinates.OpenRegularCutoff

namespace OAI

/-! # The linear domain of the weak L² Laplacian -/

open MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

lemma IsWeakLaplacian.add {f g : SobolevSpace μ hQ} {df dg : Lp ℝ 2 μ}
    (hf : IsWeakLaplacian μ hQ f df) (hg : IsWeakLaplacian μ hQ g dg) :
    IsWeakLaplacian μ hQ (f+g) (df+dg) := by
  intro φ
  rw [energyForm_add_left,hf,hg,inner_add_left]
  ring

lemma IsWeakLaplacian.smul {f : SobolevSpace μ hQ} {df : Lp ℝ 2 μ}
    (hf : IsWeakLaplacian μ hQ f df) (c : ℝ) :
    IsWeakLaplacian μ hQ (c • f) (c • df) := by
  intro φ
  rw [energyForm_smul_left,hf,real_inner_smul_left]
  ring

/-- The existence domain, with no bound on the size of its Laplacian. -/
def weakLaplacianDomain : Submodule ℝ (SobolevSpace μ hQ) where
  carrier := {f | ∃ d, IsWeakLaplacian μ hQ f d}
  zero_mem' := ⟨0,by intro φ; simp [energyForm]⟩
  add_mem' := by rintro f g ⟨df,hf⟩ ⟨dg,hg⟩; exact ⟨df+dg,hf.add μ hQ hg⟩
  smul_mem' := by rintro c f ⟨df,hf⟩; exact ⟨c • df,hf.smul μ hQ c⟩

end RegularPointCoordinates

end

end OAI
