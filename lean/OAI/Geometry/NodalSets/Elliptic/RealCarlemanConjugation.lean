import OAI.Geometry.NodalSets.Elliptic.RealEllipticProducts
import OAI.Geometry.NodalSets.Elliptic.RealWeightedCommutator

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_coordPartial_exp (phi : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (t : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (fun y ↦ Real.exp (t*phi y)) x i =
      t*Real.exp (t*phi x)*Yau.coordPartial phi x i := by
  unfold Yau.coordPartial
  rw [(((contDiff_const.mul hphi).differentiable (by simp) x).hasFDerivAt.exp).fderiv]
  rw [fderiv_fun_mul (differentiableAt_const _) (hphi.differentiable (by simp) x)]
  simp
  ring

lemma realMatrixEnergy_exp (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (phi v : Yau.Jets.Coord → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (t : ℝ) (x : Yau.Jets.Coord) :
    realMatrixEnergy B (fun y ↦ Real.exp (t*phi y)) v x =
      t*Real.exp (t*phi x)*realMatrixEnergy B phi v x := by
  simp only [realMatrixEnergy_apply,real_coordPartial_exp phi hphi,Finset.mul_sum,mul_assoc]

theorem real_carleman_conjugation (gamma phi v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hphi : ContDiff ℝ ∞ phi) (hv : ContDiff ℝ ∞ v) (t : ℝ) (x : Yau.Jets.Coord) :
    Real.exp (t*phi x)*realWeightedElliptic gamma B (fun y ↦ Real.exp (-t*phi y)*v y) x =
      realWeightedElliptic gamma B v x + t^2*realMatrixEnergy B phi phi x*v x -
      t*Yau.weightedSkewTransport gamma (realMatrixFlux B phi) v x := by
  rw [real_weighted_elliptic_product gamma B _ v hg hgn hB hs ((contDiff_const.mul hphi).exp) hv,
    real_weighted_elliptic_exp gamma phi B hg hgn hB hphi,
    realMatrixEnergy_exp B phi v hphi,
    realMatrixEnergy_symmetric B hs phi v]
  have he : Real.exp (t*phi x)*Real.exp (-t*phi x) = 1 := by
    rw [← Real.exp_add,show t*phi x + -t*phi x = 0 by ring,Real.exp_zero]
  unfold Yau.weightedSkewTransport
  rw [realMatrixEnergy_pairing]
  change _ = realWeightedElliptic gamma B v x + t^2*realMatrixEnergy B phi phi x*v x -
    t*(2*realMatrixEnergy B v phi x+realWeightedElliptic gamma B phi x*v x)
  linear_combination (realWeightedElliptic gamma B v x + t^2*realMatrixEnergy B phi phi x*v x -
    t*(2*realMatrixEnergy B v phi x+realWeightedElliptic gamma B phi x*v x))*he

theorem real_carleman_integral_identity (gamma phi v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hphi : ContDiff ℝ ∞ phi) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v) (t : ℝ) :
    (∫ x, gamma x*(Real.exp (t*phi x)*realWeightedElliptic gamma B
      (fun y ↦ Real.exp (-t*phi y)*v y) x)^2) =
      (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*realMatrixEnergy B phi phi x*v x)^2) +
      t^2*(∫ x, gamma x*(Yau.weightedSkewTransport gamma (realMatrixFlux B phi) v x)^2) +
      2*t*(∫ x, gamma x*realTransportDeformation B (realMatrixFlux B phi) v x) -
      t*(∫ x, gamma x*v x^2*realWeightedElliptic gamma B (realWeightedElliptic gamma B phi) x) +
      2*t^3*(∫ x, gamma x*Yau.pairing (realMatrixEnergy B phi phi) (realMatrixFlux B phi) x*v x^2) := by
  simp_rw [real_carleman_conjugation gamma phi v B hg hgn hB hs hphi hv]
  exact real_weighted_commutator_identity gamma (realMatrixEnergy B phi phi) v B (realMatrixFlux B phi)
    hg hgn (realMatrixEnergy_smooth B hB phi phi hphi hphi) hv hc hB hs
    (realMatrixFlux_smooth B phi hB hphi) t

end
end Yau.Geometry

end OAI
