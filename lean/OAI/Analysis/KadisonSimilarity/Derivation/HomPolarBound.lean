import OAI.Analysis.KadisonSimilarity.Representation.RegularizedPolarFactor
import OAI.Analysis.KadisonSimilarity.Derivation.DicksonAdjoint

namespace OAI

/-! The polar estimate for a bounded homomorphism, proved with approximate
polar factors in the source algebra. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Approximate polar factorization transfers to an adjoint-vector estimate. -/
theorem hom_adjoint_polar_bound (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M)
    (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (x h : A) (hh : 0 ≤ h)
    (hsq : x * star x = h * h) (ξ : H) :
    ‖(π.1 x).adjoint ξ‖ ≤ M * ‖(π.1 h).adjoint ξ‖ := by
  have happrox (ε : ℝ) (hε : 0 < ε) :
      ‖(π.1 x).adjoint ξ‖ ≤ M * ‖(π.1 h).adjoint ξ‖ + (M * ‖ξ‖) * ε := by
    let v := positiveShiftReciprocal h ε * x
    let e := x - h * v
    have hv : ‖π.1 v‖ ≤ M :=
      (hπ v).trans ((mul_le_mul_of_nonneg_left
        (norm_positiveShiftReciprocal_mul_le x h hh hsq hε) hM).trans_eq (mul_one M))
    have he : ‖π.1 e‖ ≤ M * ε :=
      (hπ e).trans (mul_le_mul_of_nonneg_left (regularizedPolar_error x h hh hsq hε) hM)
    have hx : x = h * v + e := by dsimp [e]; abel
    have hid : (π.1 x).adjoint ξ =
        (π.1 v).adjoint ((π.1 h).adjoint ξ) + (π.1 e).adjoint ξ := by
      conv_lhs => rw [hx, map_add, map_mul]
      simp only [← star_eq_adjoint, star_add, star_mul, add_apply, mul_apply_eq_comp]
    rw [hid]
    calc
      _ ≤ ‖(π.1 v).adjoint ((π.1 h).adjoint ξ)‖ + ‖(π.1 e).adjoint ξ‖ := norm_add_le _ _
      _ ≤ ‖π.1 v‖ * ‖(π.1 h).adjoint ξ‖ + ‖π.1 e‖ * ‖ξ‖ := by
        exact add_le_add
          (by simpa only [adjoint.norm_map] using
            (π.1 v).adjoint.le_opNorm ((π.1 h).adjoint ξ))
          (by simpa only [adjoint.norm_map] using (π.1 e).adjoint.le_opNorm ξ)
      _ ≤ M * ‖(π.1 h).adjoint ξ‖ + (M * ε) * ‖ξ‖ := by gcongr
      _ = _ := by ring
  apply le_of_forall_pos_le_add
  intro δ hδ
  let C := M * ‖ξ‖
  have hC : 0 ≤ C := mul_nonneg hM (norm_nonneg ξ)
  have hden : 0 < C + 1 := by positivity
  have heps : 0 < δ / (C + 1) := div_pos hδ hden
  refine (happrox (δ / (C + 1)) heps).trans ?_
  apply add_le_add (le_refl _)
  change C * (δ / (C + 1)) ≤ δ
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- The positive square root of `xx*` is enough; a polar partial isometry
or an extension of the homomorphism to a bidual is unnecessary. -/
theorem hom_adjoint_sqrt_bound (π : BoundedUnitalHom A H) {M : ℝ} (hM : 0 ≤ M)
    (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖) (x : A) (ξ : H) :
    ‖(π.1 x).adjoint ξ‖ ≤ M * ‖(π.1 (CFC.sqrt (x * star x))).adjoint ξ‖ := by
  exact hom_adjoint_polar_bound π hM hπ x _ (CFC.sqrt_nonneg _)
    (CFC.sqrt_mul_sqrt_self _ (mul_star_self_nonneg x)).symm ξ

end KadisonSimilarity

end

end OAI
