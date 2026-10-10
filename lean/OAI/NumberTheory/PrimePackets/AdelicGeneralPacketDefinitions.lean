import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicDiagonalizerDefinitions
import OAI.NumberTheory.PrimePackets.AdelicHaarExistence
import OAI.NumberTheory.PrimePackets.AdelicProbability

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set MeasureTheory
namespace PrimeDegreePackets.Adelic

 

def generalAdelicOrbit {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (h : PGL(Fin n, ℝ))
    (g : GL (Fin n) RationalFiniteAdeles) (t : (TensorAdeles K)ˣ) : AmbientQuotient n :=
  DoubleCoset.mk (rationalProjectiveGroup n) (finiteProjectiveIntegral n)
    (adelicRegular b t * (h,ProjGenLinGroup.mk g))

end PrimeDegreePackets.Adelic

end

end OAI
