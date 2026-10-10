import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
Finite-dimensional Lipschitz extension turns partial parameterizations into maps on entire balls
while retaining their images and controlling the Lipschitz constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_ball_lipschitz_extension {n d : ℕ} (r : ℝ) (A : Set (Ambient n))
    (hA : A ⊆ ball (0 : Ambient n) r) (f : Ambient n → Ambient d) (M : ℝ≥0)
    (hf : LipschitzOnWith M f A) :
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * M) g ∧ f '' A ⊆ range g := by
  obtain ⟨F, hF, hEq⟩ := hf.extend_finite_dimension
  refine ⟨(ball (0 : Ambient n) r).domRestrict F, hF.restrict _, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact ⟨⟨x, hA hx⟩, (hEq hx).symm⟩

theorem uniformlyRectifiable_of_partial_parameterizations {n d : ℕ}
    (μ : Measure (Ambient d)) (θ : ℝ) (hθ : 0 < θ) (M : ℝ≥0)
    (hpieces : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ∃ A : Set (Ambient n), A ⊆ ball (0 : Ambient n) r ∧
        ∃ f : Ambient n → Ambient d, LipschitzOnWith M f A ∧
          ENNReal.ofReal (θ * r ^ n) ≤ μ (ball x r ∩ f '' A)) :
    UniformlyRectifiable n μ := by
  refine ⟨θ, hθ, lipschitzExtensionConstant (Ambient d) * M, ?_⟩
  intro x hx r hr
  obtain ⟨A, hA, f, hf, hmass⟩ := hpieces x hx r hr
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_extension r A hA f M hf
  exact ⟨g, hg, hmass.trans (measure_mono (Set.inter_subset_inter_right _ hcover))⟩

end

end RieszRectifiability

end OAI
