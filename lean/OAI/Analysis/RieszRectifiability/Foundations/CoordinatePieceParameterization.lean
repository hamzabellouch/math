import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BallLipschitzExtension

namespace OAI

/-!
# Parameterizing pieces from separating coordinates

Coordinates taking a set into a Euclidean ball and satisfying an antilipschitz
bound have a Lipschitz inverse on their image. Extending this inverse to the
ball produces a Lipschitz map whose range covers the original set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_ball_lipschitz_cover_of_coordinates {n d : ℕ}
    (E : Set (Ambient d)) (r : ℝ) (c : Ambient d → Ambient n) (M : ℝ≥0)
    (hball : ∀ x ∈ E, c x ∈ ball (0 : Ambient n) r)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ (M : ℝ) * dist (c x) (c y)) :
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) * M) g ∧ E ⊆ range g := by
  have ha : AntilipschitzWith M (E.domRestrict c) :=
    AntilipschitzWith.of_le_mul_dist (fun x y => hsep x x.property y y.property)
  have hinj : Set.InjOn c E := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (ha.injective (show E.domRestrict c ⟨x, hx⟩ = E.domRestrict c ⟨y, hy⟩ from hxy))
  have hs : Set.SurjOn c E (c '' E) := Set.surjOn_image c E
  have hLip : LipschitzOnWith M (Function.invFunOn c E) (c '' E) :=
    lipschitzOnWith_iff_restrict.mpr
      (ha.to_rightInvOn' hs.mapsTo_invFunOn hs.rightInvOn_invFunOn)
  have hdomain : c '' E ⊆ ball (0 : Ambient n) r := by
    rintro _ ⟨x, hx, rfl⟩
    exact hball x hx
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_extension r (c '' E) hdomain
    (Function.invFunOn c E) M hLip
  refine ⟨g, hg, ?_⟩
  rw [hinj.invFunOn_image Set.Subset.rfl] at hcover
  exact hcover

theorem uniformlyRectifiable_of_big_coordinate_pieces {n d : ℕ}
    (μ : Measure (Ambient d)) (θ : ℝ) (hθ : 0 < θ) (M : ℝ≥0)
    (hpieces : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ∃ E : Set (Ambient d), E ⊆ ball x r ∧ ENNReal.ofReal (θ * r ^ n) ≤ μ E ∧
        ∃ c : Ambient d → Ambient n,
          (∀ y ∈ E, c y ∈ ball (0 : Ambient n) r) ∧
          (∀ y ∈ E, ∀ z ∈ E, dist y z ≤ (M : ℝ) * dist (c y) (c z))) :
    UniformlyRectifiable n μ := by
  refine ⟨θ, hθ, lipschitzExtensionConstant (Ambient d) * M, ?_⟩
  intro x hx r hr
  obtain ⟨E, hE, hmass, c, hball, hsep⟩ := hpieces x hx r hr
  obtain ⟨g, hg, hcover⟩ := exists_ball_lipschitz_cover_of_coordinates E r c M hball hsep
  exact ⟨g, hg, hmass.trans (measure_mono (fun y hy => ⟨hE hy, hcover hy⟩))⟩

end

end RieszRectifiability

end OAI
