import OAI.Analysis.KadisonKastler.OperatorCochainStar
import OAI.Analysis.KadisonKastler.RectangularRowNorm

namespace OAI

/-! Involution symmetrization preserves cochain bounds in the represented algebra. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cochainSharp_bound {D : A →ₗ[ℂ] A} {c : ℝ}
    (hD : CompletelyBoundedBy D c) : CompletelyBoundedBy (cochainSharp D) c := by
  intro p q X
  rw [matrix_cochainSharp, norm_conjTranspose_finite]
  simpa only [norm_conjTranspose_finite] using hD q p X.conjTranspose

theorem bilinearSharp_bound
    {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) : HaagerupBound (bilinearSharp f) c := by
  intro p r q X Y
  rw [matrix_bilinearSharp, norm_conjTranspose_finite]
  have h := hf q r p Y.conjTranspose X.conjTranspose
  simpa only [norm_conjTranspose_finite, mul_assoc, mul_comm, mul_left_comm] using h

theorem cochainSymmetrize_bound
    {D : A →ₗ[ℂ] A} {c : ℝ}
    (hD : CompletelyBoundedBy D c) : CompletelyBoundedBy (cochainSymmetrize D) c := by
  intro p q X
  have he : CStarMatrix.mapₗ (cochainSymmetrize D) X =
      (1/2 : ℂ) • (CStarMatrix.mapₗ D X + CStarMatrix.mapₗ (cochainSharp D) X) := by
    ext i j
    rfl
  rw [he, norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    (1/2 : ℝ) * ‖CStarMatrix.mapₗ D X + CStarMatrix.mapₗ (cochainSharp D) X‖ ≤
        (1/2 : ℝ) * (c * ‖X‖ + c * ‖X‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (norm_add_le _ _).trans (add_le_add (hD p q X) (cochainSharp_bound hD p q X))
    _ = _ := by ring

theorem cochainSymmetrize_residual_bound
    {f : A →ₗ[ℂ] A →ₗ[ℂ] A}
    (hstar : ∀ x y, star (f x y) = f (star y) (star x))
    (D : A →ₗ[ℂ] A) {c : ℝ}
    (hres : HaagerupBound (f - linearCoboundary D) c) :
    HaagerupBound (f - linearCoboundary (cochainSymmetrize D)) c := by
  rw [cochainSymmetrize_residual f hstar D]
  have h := (hres.add (bilinearSharp_bound hres)).smul (1/2 : ℂ)
  convert h using 1
  norm_num
  ring


end

end KadisonKastler

end OAI
