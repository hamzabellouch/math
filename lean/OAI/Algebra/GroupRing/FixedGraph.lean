import Mathlib
import OAI.Algebra.GroupRing.Cayley

namespace OAI



section
namespace TorsionFreeZeroDivisors.FixedGraph
open GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval
noncomputable section
variable {G S Y : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] [SimplyConnectedSpace Y]
  (s : S→G) (f : C(Cayley.Graph s,Y)) (y : Y) (hv : ∀g,f (Cayley.vertex s g)=y)
def vertices (g : G) : Path y (f (Cayley.vertex s g)) := (Path.refl y).cast rfl (hv g)
lemma compatible (g : G) (a : S) :
    ((vertices s f y hv g).trans ((Cayley.edge s g a).map f.continuous)).Homotopic
      (vertices s f y hv (g*s a)) := by
  apply Path.Homotopic.Quotient.eq.mp
  exact Subsingleton.elim _ _
def homotopy : f.Homotopy (.const _ y) :=
  Cayley.graphNullhomotopy s f y (vertices s f y hv) (compatible s f y hv)
lemma homotopy_vertex (t : unitInterval) (g : G) : homotopy s f y hv (t,Cayley.vertex s g)=y := by
  change ((Path.refl (f (Cayley.vertex s g))).trans (vertices s f y hv g).symm) t=y
  rw [Path.trans_apply]
  split_ifs <;> simp [vertices,hv]
end
end TorsionFreeZeroDivisors.FixedGraph

end



end OAI
