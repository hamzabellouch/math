import OAI.Geometry.NodalSets.Elliptic.RealCarlemanLocalConditions

namespace OAI

namespace Yau.Geometry
open Matrix
open scoped ContDiff
noncomputable section

def realConvexifiedPhase (psi : Yau.Jets.Coord → ℝ) (K : ℝ) (x : Yau.Jets.Coord) : ℝ :=
  psi x+K*(psi x)^2

lemma realConvexifiedPhase_smooth (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ) :
    ContDiff ℝ ∞ (realConvexifiedPhase psi K) := hpsi.add (contDiff_const.mul (hpsi.pow 2))

lemma realConvexifiedPhase_partial (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (K : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (realConvexifiedPhase psi K) x i = (1+2*K*psi x)*Yau.coordPartial psi x i := by
  have he : realConvexifiedPhase psi K = fun y ↦ psi y+K*(psi y*psi y) := by funext y; simp [realConvexifiedPhase,pow_two]
  rw [he,Yau.real_coordPartial_add _ _ hpsi (contDiff_const.mul (hpsi.mul hpsi)),
    Yau.real_coordPartial_const_mul _ (hpsi.mul hpsi),Yau.real_coordPartial_mul _ _ hpsi hpsi]
  ring

lemma realConvexifiedPhase_factor_partial (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi)
    (K : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (fun y ↦ 1+2*K*psi y) x i = 2*K*Yau.coordPartial psi x i := by
  rw [Yau.real_coordPartial_add _ _ contDiff_const (contDiff_const.mul hpsi),
    Yau.real_coordPartial_const_mul psi hpsi]
  simp [Yau.coordPartial]

lemma realMatrixFlux_convexified (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    realMatrixFlux B (realConvexifiedPhase psi K) x i = (1+2*K*psi x)*realMatrixFlux B psi x i := by
  simp only [realMatrixFlux,realConvexifiedPhase_partial psi hpsi,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; ring

lemma realMatrixEnergy_convexified (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K) x =
      (1+2*K*psi x)^2*realMatrixEnergy B psi psi x := by
  simp only [realMatrixEnergy_apply,realConvexifiedPhase_partial psi hpsi,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

lemma realMatrixFlux_convexified_derivative (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ)
    (x : Yau.Jets.Coord) (hx : psi x = 0) (i k : Fin 4) :
    Yau.coordPartial (fun y ↦ realMatrixFlux B (realConvexifiedPhase psi K) y k) x i =
      Yau.coordPartial (fun y ↦ realMatrixFlux B psi y k) x i +
      2*K*Yau.coordPartial psi x i*realMatrixFlux B psi x k := by
  have he : (fun y ↦ realMatrixFlux B (realConvexifiedPhase psi K) y k) =
      (fun y ↦ (1+2*K*psi y)*realMatrixFlux B psi y k) :=
    funext (fun y ↦ realMatrixFlux_convexified B psi hpsi K y k)
  rw [he,Yau.real_coordPartial_mul _ _ (contDiff_const.add (contDiff_const.mul hpsi))
    (realMatrixFlux_smooth B psi hB hpsi k),realConvexifiedPhase_factor_partial psi hpsi,hx]
  ring

lemma realMatrixEnergy_convexified_derivative (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ)
    (x : Yau.Jets.Coord) (hx : psi x = 0) (i : Fin 4) :
    Yau.coordPartial (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K)) x i =
      Yau.coordPartial (realMatrixEnergy B psi psi) x i +
      4*K*realMatrixEnergy B psi psi x*Yau.coordPartial psi x i := by
  have he : realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K) =
      fun y ↦ ((1+2*K*psi y)*(1+2*K*psi y))*realMatrixEnergy B psi psi y := by
    funext y; rw [realMatrixEnergy_convexified B psi hpsi]; ring
  have hF : ContDiff ℝ ∞ (fun y ↦ 1+2*K*psi y) := contDiff_const.add (contDiff_const.mul hpsi)
  rw [he,Yau.real_coordPartial_mul _ _ (hF.mul hF) (realMatrixEnergy_smooth B hB psi psi hpsi hpsi),
    Yau.real_coordPartial_mul _ _ hF hF,realConvexifiedPhase_factor_partial psi hpsi,hx]
  ring

theorem real_convexified_cubic (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (psi : Yau.Jets.Coord → ℝ) (hpsi : ContDiff ℝ ∞ psi) (K : ℝ)
    (x : Yau.Jets.Coord) (hx : psi x = 0) :
    Yau.pairing (realMatrixEnergy B (realConvexifiedPhase psi K) (realConvexifiedPhase psi K))
        (realMatrixFlux B (realConvexifiedPhase psi K)) x =
      Yau.pairing (realMatrixEnergy B psi psi) (realMatrixFlux B psi) x +
      4*K*(realMatrixEnergy B psi psi x)^2 := by
  simp only [Yau.pairing,realMatrixFlux_convexified B psi hpsi,
    realMatrixEnergy_convexified_derivative B hB psi hpsi K x hx,hx,mul_zero,add_zero,one_mul,
    add_mul,Finset.sum_add_distrib]
  have he : (∑ i, 4*K*realMatrixEnergy B psi psi x*Yau.coordPartial psi x i*realMatrixFlux B psi x i) =
      4*K*realMatrixEnergy B psi psi x*Yau.pairing psi (realMatrixFlux B psi) x := by
    simp only [Yau.pairing,Finset.mul_sum,mul_assoc]
  rw [he,realMatrixEnergy_pairing]
  ring

end
end Yau.Geometry

end OAI
