import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PolygonStringSimplicial
import OAI.GroupTheory.SimpleAmenable.Simplicial.RestrictedNerve

namespace OAI

section

section
open CategoryTheory
namespace SimpleAmenable.PolygonObject

noncomputable def stringResolutionHomologyIso (a j : ℕ) :
    (SimplicialDiagonal.diagonal.obj (stringDoubleNerve a)).homology DiagonalResolution.Z j ≅
      (nerve (PolygonObject a)).homology DiagonalResolution.Z j :=
  RestrictedNerve.homologyIso (positionalProperty a) j
end SimpleAmenable.PolygonObject

end

end

end OAI
