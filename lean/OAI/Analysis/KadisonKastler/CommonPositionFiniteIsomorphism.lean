import OAI.Analysis.KadisonKastler.PublishedStandardIsomorphism
import OAI.Analysis.KadisonKastler.CommonPositionTransfer

namespace OAI

/-! # The finite-factor isomorphism transferred from common position

The published common-position representation supplies the standard
positions and the conjugation estimate. The scalar boundary theorem
then constructs an isomorphism, which is transported to the original
represented factors with the explicit comparison error.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H K : Type u}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]
  {M N R : VonNeumannAlgebra H} {hRM : R ≤ M} {hRN : R ≤ N} {g : ℝ}

namespace CommonTracialPositionData

/-- The common-position and scalar boundary inputs give an isomorphism
of the original factors with the full transported estimate. -/
theorem exists_finiteFactor_isomorphism
    (d : CommonTracialPositionData M N R hRM hRN g K)
    (hBoundary : PublishedBoundary.{u}) (hTom : PublishedFieldTomiyamaFamily K)
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (hgap : kkDistance M N < g)
    {b : ℝ} (hb : 2 * d.tolerance < b) (hbsmall : b < 1 / 100000) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      ∀ x, ‖(θ x : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤
        (378 * b + d.tolerance + 2 * g) * ‖x‖ := by
  have hb0 : 0 ≤ b :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) d.tolerance_nonneg).trans hb.le
  obtain ⟨θ, hθ⟩ := exists_standard_finiteFactor_isomorphism_of_published
    hBoundary hTom (d.left_isII1 hM) (d.right_isII1 hN)
    d.leftPosition d.rightPosition d.same_vector hbsmall
    (d.distance_le.trans_lt hb) (d.conjugations_sub_le hirr hb)
  exact ⟨d.transportEquiv θ, fun x =>
    d.transportEquiv_bound θ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 378) hb0) hθ hgap x⟩

end CommonTracialPositionData

end

end KadisonKastler

end OAI
