import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicContinuity

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set
namespace PrimeDegreePackets.Adelic

 
instance realPGLTopology (n : ℕ) : TopologicalSpace PGL(Fin n, ℝ) :=
  inferInstanceAs (TopologicalSpace (GL (Fin n) ℝ ⧸ Subgroup.center (GL (Fin n) ℝ)))
instance realPGLTopologicalGroup (n : ℕ) : IsTopologicalGroup PGL(Fin n, ℝ) :=
  inferInstanceAs (IsTopologicalGroup (GL (Fin n) ℝ ⧸ Subgroup.center (GL (Fin n) ℝ)))

 
def realTorus {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) : Subgroup PGL(Fin n, ℝ) :=
  (ProjGenLinGroup.mk.comp (rowRegularUnits (b.baseChange ℝ))).range

 
def realTorusIdentity {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) : Set PGL(Fin n, ℝ) :=
  (fun t : realTorus b => (t : PGL(Fin n, ℝ))) '' connectedComponent (1 : realTorus b)

 
def AllowedRealDiagonalizer {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (h : PGL(Fin n, ℝ)) : Prop :=
  (fun t => h⁻¹ * t * h) '' realTorusIdentity b =
    SpecialLinearGroup.toPGL '' positiveDiagonal n

end PrimeDegreePackets.Adelic

end

end OAI
