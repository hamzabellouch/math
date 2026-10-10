import Mathlib
import OAI.Algebra.GroupRing.GraphConeCW
import OAI.Algebra.GroupRing.AttachmentHEP

namespace OAI



section
namespace TorsionFreeZeroDivisors.VertexCollapse
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
noncomputable section
variable {G S Q Y : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] [PathConnectedSpace Y]
variable (s : S→G) (a : Q→C(Sphere 2,Cayley.Graph s)) (f : C(CellPresentation.Cover s a,Y)) (y : Y)
def vertexPath (g : G) : Path (f (CellPresentation.inclusion s a (Cayley.vertex s g))) y :=
  PathConnectedSpace.somePath _ _
def vertices : C(unitInterval × G,Y) :=
  ((⟨fun g=>(vertexPath s a f y g).toContinuousMap,continuous_of_discreteTopology⟩ :
    C(G,C(unitInterval,Y))).uncurry).comp ⟨Prod.swap,continuous_swap⟩
lemma vertices_zero (g : G) : vertices s a f y (0,g)=f (CellPresentation.inclusion s a (Cayley.vertex s g)) :=
  Path.source _
lemma vertices_one (g : G) : vertices s a f y (1,g)=y := Path.target _
def graph : C(unitInterval × Cayley.Graph s,Y) :=
  AttachmentHEP.extend (equivariantFamily (G:=G) (Cayley.attaching s))
    (f.comp (CellPresentation.inclusion s a)) (vertices s a f y) (vertices_zero s a f y)
lemma graph_zero (z : Cayley.Graph s) : graph s a f y (0,z)=f (CellPresentation.inclusion s a z) :=
  AttachmentHEP.extend_zero _ _ _ _ z
lemma graph_vertex (t : unitInterval) (g : G) : graph s a f y (t,Cayley.vertex s g)=vertices s a f y (t,g) := rfl
/-- Homotope an actual map on the whole presentation complex so that EVERY
vertex goes to one basepoint. Both cell layers are extended, not collapsed by
an unproved quotient/homotopy-equivalence assertion. -/
def map : C(CellPresentation.Cover s a,Y) :=
  AttachmentHEP.endpoint (equivariantFamily (G:=G) a) f (graph s a f y) (graph_zero s a f y)
def homotopy : f.Homotopy (map s a f y) :=
  AttachmentHEP.homotopy (equivariantFamily (G:=G) a) f (graph s a f y) (graph_zero s a f y)
lemma map_vertex (g : G) : map s a f y (CellPresentation.inclusion s a (Cayley.vertex s g))=y :=
  vertices_one s a f y g
end
end TorsionFreeZeroDivisors.VertexCollapse


end



end OAI
