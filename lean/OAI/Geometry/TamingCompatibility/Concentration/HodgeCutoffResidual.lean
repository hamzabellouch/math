import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCutoffFamilies

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.CutoffFamilies
open OperatorCalculus NormalHeatResidual UniformJets FlatHeat Filter Set
open scoped Topology ContDiff
variable {P W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
lemma residual_zero_off (a : Fin 4 → Fin 4 → P × V → ℝ)
    (b : Fin 4 → P × V → W →L[ℝ] W) (c : P × V → W →L[ℝ] W)
    (χ : V → ℝ) (q : P) (t : ℝ) {z : V} (hz : z ∉ tsupport χ) :
    residual (fun y => principal a χ (q,y)) (fun y => first a b χ (q,y))
      (fun y => zero a b c χ (q,y)) t z = 0 := by
  have hdd (j : Fin 4) : fderiv ℝ (fun y => fderiv ℝ χ y (EuclideanSpace.single j 1)) z = 0 :=
    fderiv_of_notMem_tsupport ℝ (fun hh => hz (tsupport_fderiv_apply_subset ℝ _ hh))
  simp [NormalHeatResidual.residual,principal,first,zero,cutoffPrincipal,cutoffFirst,cutoffZero,
    image_eq_zero_of_notMem_tsupport hz,fderiv_of_notMem_tsupport ℝ hz,hdd]

end TamingCompatibility.GeometricHilbert.CutoffFamilies

end
end

end

end OAI
