import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothFactorRotations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HomExponentialDerivative

namespace OAI

/-! # Differentiating the individual compact rotations -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
  (β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H →* MulAut G)
  (hβ : ∀ z (x : T.kernelIdeal) d,
    β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
      F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) * F.inclusionD d)

include hExp hβ in
theorem contMDiff_individual_rotation
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (fun g => β z g) := by
  let R : E →L[ℝ] E := tangentTorusUnitAction H z
  have hR : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) ∞ (fun _ : G => R) := contMDiff_const
  have hs := F.contMDiff_action hExp β hβ (fun _ : G => z) (fun _ => R) hR (fun _ _ => rfl)
  have hc : ContMDiff (𝓘(ℝ,E)) ((𝓘(ℝ,E)).prod (𝓘(ℝ,E))) ∞
      (fun g : G => ((1 : G),g)) := contMDiff_const.prodMk contMDiff_id
  simpa only [Function.comp_def] using hs.comp hc

include hβ in
theorem rotation_exp_nilradical
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) (x : T.kernelIdeal) :
    β z (Exp x) = Exp (T.nilradicalRotation H z x) := by
  have hh := hβ z x (1 : F.D.carrier)
  simpa only [map_one,mul_one,F.compatibleN] using hh

include hβ in
theorem rotation_fixes_cartan_factor
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) (d : F.D.carrier) :
    β z (F.inclusionD d) = F.inclusionD d := by
  have hh := hβ z 0 d
  simpa only [map_zero,F.isExpN.map_zero,map_one,one_mul] using hh

include hβ in
theorem rotation_exp_cartan
    (z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H) (h : H) :
    β z (Exp h) = Exp h := by
  have hh := F.rotation_fixes_cartan_factor β hβ z (F.ExpD (F.D.equiv h))
  simpa only [F.compatibleD] using hh

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
