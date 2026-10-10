import OAI.Combinatorics.Crossing.FinitePolygonalComposition

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b a' b' : Plane}

def castEndpoints (P : PolygonalChain O a b) (ha : a'=a) (hb : b'=b) : PolygonalChain O a' b' where
  pieces := P.pieces
  vertices := P.vertices
  first := P.first.trans ha.symm
  last := P.last.trans hb.symm
  start_mem := ha.symm ▸ P.start_mem
  inside := P.inside

theorem castEndpoints_pieces (P : PolygonalChain O a b) (ha : a'=a) (hb : b'=b) :
    (P.castEndpoints ha hb).pieces=P.pieces := rfl

theorem castEndpoints_vertices (P : PolygonalChain O a b) (ha : a'=a) (hb : b'=b) :
    (P.castEndpoints ha hb).vertices=P.vertices := rfl

end Zarankiewicz.PolygonalChain

end

end OAI
