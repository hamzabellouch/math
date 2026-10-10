import OAI.Geometry.NodalSets.Elliptic.RealDifferentiatedEquation
import OAI.Geometry.NodalSets.Elliptic.RealTransportQuadratic

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

lemma realGradientSquare_nonneg (W : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    0 ≤ realGradientSquare W x := Finset.sum_nonneg (fun _i _ ↦ sq_nonneg _)

lemma real_partial_sq_le_gradient (W : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    (Yau.coordPartial W x i)^2 ≤ realGradientSquare W x :=
  Finset.single_le_sum (fun j _ ↦ sq_nonneg (Yau.coordPartial W x j)) (Finset.mem_univ i)

lemma real_matrix_flux_square_bound (A : Matrix (Fin 4) (Fin 4) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) (v : Yau.Jets.Coord) :
    (∑ i, (∑ j, A i j*v j)^2) ≤ 16*B^2*(∑ j, v j^2) := by
  have row (i : Fin 4) : (∑ j, A i j*v j)^2 ≤ 4*B^2*(∑ j, v j^2) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) v
    have hc : (∑ j, A i j^2) ≤ 4*B^2 := by
      calc
        (∑ j, A i j^2) ≤ ∑ _j : Fin 4, B^2 := Finset.sum_le_sum (fun j _ ↦ by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hA i j))
        _ = 4*B^2 := by simp
    exact hcs.trans (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun j _ ↦ sq_nonneg (v j))))
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ row i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  norm_num at h
  nlinarith only [h]

lemma realDerivativeErrorFlux_square_bound (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (W : Yau.Jets.Coord → ℝ) (k : Fin 4) (x : Yau.Jets.Coord) (B : ℝ) (hB : 0 ≤ B)
    (hC : ∀ i j, |Yau.coordPartial (fun y ↦ C y i j) x k| ≤ B) :
    (∑ i, (realDerivativeErrorFlux C W k x i)^2) ≤ 16*B^2*realGradientSquare W x :=
  real_matrix_flux_square_bound (fun i j ↦ Yau.coordPartial (fun y ↦ C y i j) x k) B hB hC (realCoordGradient W x)

lemma real_coordDiv_neg (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) (x : Yau.Jets.Coord) :
    Yau.coordDiv (fun y i ↦ -F y i) x = -Yau.coordDiv F x := by
  unfold Yau.coordDiv Yau.coordPartial
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg (fun derivative : Yau.Jets.Coord →L[ℝ] ℝ ↦ derivative (Pi.single index 1))
    (((hF index).differentiable (by simp)).differentiableAt.hasFDerivAt.neg.fderiv)

lemma real_differentiated_density_signed (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W : Yau.Jets.Coord → ℝ) (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j))
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (he : ∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=0) (k : Fin 4) :
    ∀ x, Yau.coordDiv (realMatrixFlux C (fun y ↦ Yau.coordPartial W y k)) x+
      V x*Yau.coordPartial W x k =
      Yau.coordDiv (fun y i ↦ -realDerivativeErrorFlux C W k y i) x+
        (-(Yau.coordPartial V x k)*W x) := by
  intro x
  rw [real_coordDiv_neg _ (realDerivativeErrorFlux_smooth C W k hC hW)]
  have h := real_differentiated_density_equation C V W hC hV hW he k x
  linarith only [h]

end
end Yau.Geometry

end OAI
