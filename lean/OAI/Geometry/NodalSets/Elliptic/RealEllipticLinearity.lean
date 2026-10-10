import OAI.Geometry.NodalSets.Elliptic.RealEllipticLocalityLemmas
import OAI.Geometry.NodalSets.Elliptic.RealTransportDerivatives

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section

lemma real_partial_linear_combination (u v : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (c : ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    Yau.coordPartial (fun y ↦ c*u y+v y) x i = c*Yau.coordPartial u x i+Yau.coordPartial v x i := by
  rw [Yau.real_coordPartial_add _ _ (contDiff_const.mul hu) hv,Yau.real_coordPartial_const_mul u hu]

lemma realWeightedElliptic_linear_combination (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hg : ContDiff ℝ ∞ gamma)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (c : ℝ) (x : Yau.Jets.Coord) :
    realWeightedElliptic gamma B (fun y ↦ c*u y+v y) x =
      c*realWeightedElliptic gamma B u x+realWeightedElliptic gamma B v x := by
  have he (i : Fin 4) : (fun y ↦ gamma y*realMatrixFlux B (fun z ↦ c*u z+v z) y i) =
      fun y ↦ c*(gamma y*realMatrixFlux B u y i)+gamma y*realMatrixFlux B v y i := by
    funext y
    simp only [realMatrixFlux,real_partial_linear_combination u v hu hv,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro j _; ring
  unfold realWeightedElliptic Yau.weightedDiv Yau.coordDiv
  simp_rw [he,real_partial_linear_combination _ _
    (hg.mul (realMatrixFlux_smooth B u hB hu _)) (hg.mul (realMatrixFlux_smooth B v hB hv _))]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

lemma realEllipticResidual_linear_combination (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (u v : Yau.Jets.Coord → ℝ) (hg : ContDiff ℝ ∞ gamma)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (c : ℝ) (x : Yau.Jets.Coord) :
    realEllipticResidual gamma potential B (fun y ↦ c*u y+v y) x =
      c*realEllipticResidual gamma potential B u x+realEllipticResidual gamma potential B v x := by
  unfold realEllipticResidual
  rw [realWeightedElliptic_linear_combination gamma B u v hg hB hu hv]
  ring

end
end Yau.Geometry

end OAI
