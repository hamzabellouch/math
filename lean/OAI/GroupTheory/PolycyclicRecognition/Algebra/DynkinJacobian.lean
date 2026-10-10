import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieWordDerivative
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FilteredDeterminant

namespace OAI

/-! # Unit Jacobian of left translation in nilpotent BCH coordinates -/

noncomputable section
namespace PolycyclicRecognition

open LieModule

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]

def rightVariableDifferential : Fin 2 → L →ₗ[ℝ] L := ![0, 1]

theorem hasFDerivAt_rightDynkin {c : ℕ} (coeff : DynkinCoefficients c 2) (x y : L) :
    HasFDerivAt (fun z => finiteDynkinPolynomial coeff ![x, z])
      (finiteDynkinDifferential coeff ![x, y] (rightVariableDifferential (L := L))).toContinuousLinearMap y := by
  apply hasFDerivAt_finiteDynkinPolynomial coeff (fun z => ![x, z]) (rightVariableDifferential (L := L)) y
  intro i
  fin_cases i
  · exact hasFDerivAt_const (𝕜 := ℝ) x y
  · exact hasFDerivAt_id (𝕜 := ℝ) y

theorem rightDynkinDifferential_zero {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hunit : ∀ y : L, finiteDynkinPolynomial coeff ![0, y] = y) :
    finiteDynkinDifferential coeff ![0, 0] (rightVariableDifferential (L := L)) = 1 := by
  have hd := hasFDerivAt_rightDynkin coeff (0 : L) 0
  have heq : (fun y : L => finiteDynkinPolynomial coeff ![0, y]) = id := funext hunit
  rw [heq] at hd
  have hh := hd.unique (hasFDerivAt_id (𝕜 := ℝ) (0 : L))
  ext v
  exact congrArg (fun D : L →L[ℝ] L => D v) hh

theorem rightDynkinDifferential_det {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hunit : ∀ y : L, finiteDynkinPolynomial coeff ![0, y] = y)
    {d : ℕ} (hd : lowerCentralSeries ℝ L L d = ⊥) (x y : L) :
    LinearMap.det (finiteDynkinDifferential coeff ![x, y] (rightVariableDifferential (L := L))) = 1 := by
  apply det_eq_one_of_raises_filtration (fun k => (lowerCentralSeries ℝ L L k).toSubmodule)
    (by simp) (congrArg LieSubmodule.toSubmodule hd)
  intro k v hv
  have hh := finiteDynkinDifferential_sub_mem_succ coeff ![x, y] ![0, 0]
    (rightVariableDifferential (L := L)) k v (by
      intro i
      fin_cases i
      · exact (lowerCentralSeries ℝ L L k).zero_mem
      · exact hv)
  rw [rightDynkinDifferential_zero coeff hunit] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
