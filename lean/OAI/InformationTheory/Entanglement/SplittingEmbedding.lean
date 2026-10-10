import OAI.Analysis.Quantum.PPTSquare.FieldExtension
import OAI.Analysis.Quantum.PPTSquare.SplittingSetup
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

noncomputable section
open Polynomial
namespace SplittingEmbedding
abbrev f : ℤ[X] := PencilAlgebra.N0Num.charpoly
abbrev K := SplittingSetup.Split f
def phi : K →ₐ[ℚ] ℂ := Polynomial.SplittingField.lift (f.map (Int.castRingHom ℚ)) (IsAlgClosed.splits _)
end SplittingEmbedding

end

end OAI
