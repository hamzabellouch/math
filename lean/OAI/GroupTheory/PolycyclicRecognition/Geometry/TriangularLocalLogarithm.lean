import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialLocalSeparation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularExponentialKernel
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Algebra

namespace OAI

/-! # The local logarithm in the full real upper triangular algebra -/

noncomputable section
namespace PolycyclicRecognition

open Filter Topology
open scoped Matrix.Norms.Operator

abbrev RealTriangularAlgebra (n : ℕ) :=
  ↥(Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n))

instance (n : ℕ) : IsTopologicalRing (RealTriangularAlgebra n) :=
  IsTopologicalSemiring.toIsTopologicalRing inferInstance

variable {n : ℕ}

theorem realTriangularAlgebra_coe_exp (a : RealTriangularAlgebra n) :
    ((NormedSpace.exp a : RealTriangularAlgebra n) : Matrix (Fin n) (Fin n) ℝ) =
      NormedSpace.exp (a : Matrix (Fin n) (Fin n) ℝ) := by
  let : NormedAlgebra ℚ (RealTriangularAlgebra n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp
    (Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin n → Fin n)).val.toRingHom
    continuous_subtype_val a

theorem realTriangularAlgebra_exp_kernel (a : RealTriangularAlgebra n)
    (ha : NormedSpace.exp a = 1) : a = 0 := by
  apply Subtype.ext
  have he := congrArg (fun b : RealTriangularAlgebra n =>
    (b : Matrix (Fin n) (Fin n) ℝ)) ha
  rw [realTriangularAlgebra_coe_exp] at he
  exact (triangular_exp_eq_one_iff _ a.property).mp he

theorem realTriangularAlgebra_local_logarithm :
    ∃ log : RealTriangularAlgebra n → RealTriangularAlgebra n,
      ContinuousAt log 1 ∧ log 1 = 0 ∧
      ∀ᶠ z in 𝓝 (1 : RealTriangularAlgebra n), NormedSpace.exp (log z) = z ∧
        ∀ a, NormedSpace.exp a = z → a = log z :=
  exists_unique_local_logarithm realTriangularAlgebra_exp_kernel

end PolycyclicRecognition

end

end OAI
