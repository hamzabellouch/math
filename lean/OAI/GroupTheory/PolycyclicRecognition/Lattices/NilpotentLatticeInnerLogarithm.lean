import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeInnerAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CanonicalNilpotentLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential
import Mathlib.Algebra.Lie.Nilpotent

namespace OAI

/-! # Inner logarithms in the actual nilpotent lattice model -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {H : Type} [Group H] [Group.IsNilpotent H] (C : NilpotentLatticeCoordinates H)
local instance innerLogRationalModule : Module ℚ C.carrier :=
  Module.compHom C.carrier (algebraMap ℚ ℝ)

/-- The finite logarithm of a lattice inner automorphism is exactly the inner
Lie derivation, including its normalization at the lattice element. -/
theorem automorphismLinear_inner_log (t : H) :
    nilpotentLog (C.automorphismLinear (MulAut.conj t) - 1) =
      LieAlgebra.ad ℝ C.carrier (C.equiv t) := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) C.carrier
  let := NormedAlgebra.restrictScalars ℚ ℝ (C.carrier →L[ℝ] C.carrier)
  have hn : IsNilpotent (LieAlgebra.ad ℝ C.carrier (C.equiv t)) :=
    LieModule.isNilpotent_toEnd_of_isNilpotent ℝ C.carrier C.carrier _
  apply E.injective
  have he : E (nilpotentLog (C.automorphismLinear (MulAut.conj t) - 1)) =
      nilpotentLog (E (C.automorphismLinear (MulAut.conj t) - 1)) :=
    (nilpotentLog_map E.toRingHom _ (C.automorphismLinear_inner_unipotent t)).symm
  rw [he, map_sub, map_one]
  change nilpotentLog
    (LinearMap.toContinuousLinearMap (C.automorphismLinear (MulAut.conj t)) - 1) = _
  have hn' : IsNilpotent
      (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ C.carrier (C.equiv t))) :=
    hn.map E.toRingHom
  rw [C.automorphismLinear_inner_exp, analytic_exp_eq_nilpotent_exp hn', nilpotentLog_exp _ hn']
  rfl

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
