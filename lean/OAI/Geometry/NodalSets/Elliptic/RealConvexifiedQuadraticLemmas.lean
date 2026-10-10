import OAI.Geometry.NodalSets.Elliptic.RealConvexifiedPhase

namespace OAI

noncomputable section

namespace Yau.Geometry

open Matrix
open scoped ContDiff

lemma real_flux_rank_one (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hs : ∀ x i j, B x i j = B x j i) (psi : Yau.Jets.Coord → ℝ)
    (x xi : Yau.Jets.Coord) :
    (∑ i, ∑ j, ∑ k, B x i j*Yau.coordPartial psi x i*realMatrixFlux B psi x k*xi k*xi j) =
      (∑ k, realMatrixFlux B psi x k*xi k)^2 := by
  have hf : (∑ i, ∑ j, B x i j*Yau.coordPartial psi x i*xi j) =
      (∑ j, realMatrixFlux B psi x j*xi j) := by
    rw [Finset.sum_comm]
    simp only [realMatrixFlux,Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro i _
    rw [hs x i j]
  calc
    _ = (∑ i, ∑ j, B x i j*Yau.coordPartial psi x i*xi j)*
        (∑ k, realMatrixFlux B psi x k*xi k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    _ = _ := by rw [hf,pow_two]

theorem real_convexified_quadratic (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ)
    (x : Yau.Jets.Coord) (hx : psi x = 0) (xi : Yau.Jets.Coord) :
    realTransportQuadratic B (realMatrixFlux B (realConvexifiedPhase psi K)) x xi =
      realTransportQuadratic B (realMatrixFlux B psi) x xi +
      4*K*(∑ k, realMatrixFlux B psi x k*xi k)^2 := by
  rw [← real_flux_rank_one B hs psi x xi]
  simp only [realTransportQuadratic]
  simp_rw [realMatrixFlux_convexified_derivative B hB psi hpsi K x hx]
  simp only [realMatrixFlux_convexified B psi hpsi,hx,mul_zero,add_zero,one_mul,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _; ring

open Metric

def realCoordinateSquare (x0 x : Yau.Jets.Coord) : ℝ := ∑ i, (x i-x0 i)^2

lemma realCoordinateSquare_smooth (x0 : Yau.Jets.Coord) :
    ContDiff ℝ ∞ (realCoordinateSquare x0) :=
  ContDiff.sum (fun i _ ↦ ((contDiff_apply ℝ ℝ i).sub contDiff_const).pow 2)

lemma realCoordinateSquare_zero (x0 : Yau.Jets.Coord) : realCoordinateSquare x0 x0 = 0 := by
  simp [realCoordinateSquare]

lemma realCoordinateSquare_nonneg (x0 x : Yau.Jets.Coord) : 0 ≤ realCoordinateSquare x0 x :=
  Finset.sum_nonneg (fun index _ ↦ sq_nonneg (x index - x0 index))

lemma realCoordinateSquare_norm (x0 x : Yau.Jets.Coord) : ‖x-x0‖^2 ≤ realCoordinateSquare x0 x :=
  coord_norm_sq_le_sum_sq (x-x0)

lemma realCoordinateSquare_partial_center (x0 : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (realCoordinateSquare x0) x0 i = 0 := by
  have hf (j : Fin 4) : ContDiff ℝ ∞ (fun x : Yau.Jets.Coord ↦ x j-x0 j) :=
    (contDiff_apply ℝ ℝ j).sub contDiff_const
  have he : realCoordinateSquare x0 = fun x ↦ ∑ j, (x j-x0 j)*(x j-x0 j) := by
    funext x; simp [realCoordinateSquare,pow_two]
  rw [he,Yau.real_coordPartial_sum _ (fun j ↦ (hf j).mul (hf j))]
  apply Finset.sum_eq_zero
  intro j _
  rw [Yau.real_coordPartial_mul _ _ (hf j) (hf j)]
  simp

def realIndentedPhase (psi : Yau.Jets.Coord → ℝ) (x0 : Yau.Jets.Coord)
    (x : Yau.Jets.Coord) : ℝ := psi x-realCoordinateSquare x0 x

lemma realIndentedPhase_smooth (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (x0 : Yau.Jets.Coord) : ContDiff ℝ ∞ (realIndentedPhase psi x0) :=
  hpsi.sub (realCoordinateSquare_smooth x0)

lemma realIndentedPhase_center (psi : Yau.Jets.Coord → ℝ) (x0 : Yau.Jets.Coord) :
    realIndentedPhase psi x0 x0 = psi x0 := by simp [realIndentedPhase,realCoordinateSquare_zero]

lemma realIndentedPhase_gradient_center (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (x0 : Yau.Jets.Coord) : realCoordGradient (realIndentedPhase psi x0) x0 = realCoordGradient psi x0 := by
  ext i
  simp only [realCoordGradient]
  unfold Yau.coordPartial realIndentedPhase
  rw [fderiv_fun_sub (hpsi.differentiable (by simp) x0)
    ((realCoordinateSquare_smooth x0).differentiable (by simp) x0)]
  have hh := realCoordinateSquare_partial_center x0 i
  simp only [Yau.coordPartial] at hh
  simp only [_root_.sub_apply,hh,sub_zero]

lemma realIndentedPhase_annulus (psi : Yau.Jets.Coord → ℝ) (x0 x : Yau.Jets.Coord)
    (s : ℝ) (hs : 0 ≤ s) (hd : s ≤ dist x x0) (hpsi : psi x ≤ 0) :
    realIndentedPhase psi x0 x ≤ -s^2 := by
  have hn := realCoordinateSquare_norm x0 x
  rw [dist_eq_norm] at hd
  have hsq : s^2 ≤ ‖x-x0‖^2 := by nlinarith only [hs,hd,norm_nonneg (x-x0)]
  dsimp [realIndentedPhase]
  linarith

lemma realConvexifiedPhase_negative_bound (psi : Yau.Jets.Coord → ℝ) (K : ℝ) (hK : 0 < K)
    (x : Yau.Jets.Coord) (hlow : -(1/(2*K)) < psi x) (hhigh : psi x ≤ 0) :
    realConvexifiedPhase psi K x ≤ psi x/2 := by
  have hk2 : 0 < 2*K := by positivity
  have hmul : -(1:ℝ) < (2*K)*psi x := by
    have hh := (div_lt_iff₀ hk2).mp (show (-1)/(2*K) < psi x by simpa only [neg_div] using hlow)
    linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1/2+K*psi x) hhigh
  dsimp [realConvexifiedPhase]
  nlinarith only [hp]

end Yau.Geometry

end

end OAI
