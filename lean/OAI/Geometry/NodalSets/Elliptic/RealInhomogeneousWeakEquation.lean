import OAI.Geometry.NodalSets.Elliptic.RealDifferentiatedEquation

namespace OAI

namespace Yau.Geometry
open MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_coord_integration_by_parts (phi : Yau.Jets.Coord → ℝ)
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (F : Yau.Jets.Coord → Yau.Jets.Coord) (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) :
    Integrable (Yau.pairing phi F) ∧ Integrable (fun x ↦ phi x*Yau.coordDiv F x) ∧
      (∫ x, Yau.pairing phi F x) = -(∫ x, phi x*Yau.coordDiv F x) := by
  have hh := Yau.compact_weighted_integration_by_parts (fun _ ↦ 1) phi contDiff_const
    (fun _ ↦ one_ne_zero) hphi hc F hF
  simpa only [Yau.weightedDiv,inv_one,one_mul] using hh

theorem real_inhomogeneous_density_test (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V W f phi : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord)
    (hC : ∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (hf : ContDiff ℝ ∞ f)
    (hF : ∀ i, ContDiff ℝ ∞ (fun x ↦ F x i))
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (he : ∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x) :
    Integrable (realMatrixEnergy C phi W) ∧
    Integrable (fun x ↦ phi x*V x*W x) ∧
    Integrable (Yau.pairing phi F) ∧ Integrable (fun x ↦ phi x*f x) ∧
    (∫ x, realMatrixEnergy C phi W x) = (∫ x, phi x*V x*W x)+
      (∫ x, Yau.pairing phi F x)-(∫ x, phi x*f x) := by
  obtain ⟨hiP,hiD,hP⟩ := real_coord_integration_by_parts phi hphi hc (realMatrixFlux C W)
    (realMatrixFlux_smooth C W hC hW)
  obtain ⟨hiF,hiDF,hFE⟩ := real_coord_integration_by_parts phi hphi hc F hF
  have hiV : Integrable (fun x ↦ phi x*V x*W x) :=
    ((hphi.mul hV).mul hW).continuous.integrable_of_hasCompactSupport hc.mul_right.mul_right
  have hif : Integrable (fun x ↦ phi x*f x) :=
    (hphi.mul hf).continuous.integrable_of_hasCompactSupport hc.mul_right
  have hid : (∫ x, phi x*Yau.coordDiv (realMatrixFlux C W) x+phi x*V x*W x) =
      (∫ x, phi x*Yau.coordDiv F x+phi x*f x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    linear_combination phi x*he x
  rw [integral_add hiD hiV,integral_add hiDF hif] at hid
  have hpEq : Yau.pairing phi (realMatrixFlux C W) = realMatrixEnergy C phi W :=
    funext (realMatrixEnergy_pairing C phi W)
  rw [hpEq] at hiP hP
  refine ⟨hiP,hiV,hiF,hif,?_⟩
  linarith only [hid,hP,hFE]

end
end Yau.Geometry

end OAI
