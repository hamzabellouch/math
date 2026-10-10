import Mathlib
import OAI.Geometry.HyperbolicGroups.VoltageGraphHomotopy
import OAI.Geometry.HyperbolicGroups.VoltageTriangleHomotopy
import OAI.Geometry.HyperbolicGroups.VoltageEdgeCorrection
import OAI.Geometry.HyperbolicGroups.BasedTriangleContraction
import OAI.Geometry.HyperbolicGroups.PrismConcat

namespace OAI

/-! A literal contracting prism on each lifted triangle once its genuine pi2
obstruction is the coboundary of the constructed directed cochain. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare HSpacePathObstruction
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
  (L : G → V → V → v.LoopClass z)
  (hs : ∀ g a, L g a a = 1)
  (hr : ∀ {a b}, {a,b} ∈ K.faces → ∀ g, L (g*v.value a b) b a = (L g a b)⁻¹)

def correctedEdge {a b : V} (h : {a,b} ∈ K.faces) (g : G) : C(I × I,v.TotalSpace) :=
  PrismConcat.concat (v.edgeHomotopy z h g) (v.correctionSquare z L h g)
    (fun s => (v.edgeHomotopy_final z h g s).trans (v.correctionSquare_initial z L h g s).symm)

lemma correctedEdge_agree {a b c d : V} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces)
    (g k : G) (t s r : I) (he : v.edgeLift h g s = v.edgeLift h' k r) :
    v.correctedEdge z L h g (t,s) = v.correctedEdge z L h' k (t,r) :=
  PrismConcat.agree _ _ _ _ _ _ s r
    (fun t => v.edgeHomotopy_agree z h h' g k t s r he)
    (fun t => (v.correctionEdgeData z L).agree h h' g k t s r he) t
lemma correctedEdge_initial {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.correctedEdge z L h g (0,s) = v.edgeLift h g s := by
  rw [correctedEdge,PrismConcat.initial,v.edgeHomotopy_initial]
lemma correctedEdge_final {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.correctedEdge z L h g (1,s) = z := by
  rw [correctedEdge,PrismConcat.final,v.correctionSquare_final]

lemma correctedEdge_fixed (a : V) (g : G) (he : v.vertexLift a g = z) (t r : I) :
    v.correctedEdge z L (edge_self K a) g (t,r) = z := by
  apply PrismConcat.constant_at
  · intro t
    change v.edgeHomotopy z (edge_self K a) g (t,r) = z
    simp only [edgeHomotopy,ite_true,eq_self]
    exact v.vertexTrack_fixed z a g he t
  · intro t
    change ((Path.refl (Path.refl z)).trans (v.correctionLoop z L (edge_self K a) g)) t r = z
    simp only [correctionLoop,ite_true,eq_self,Path.refl_trans_refl]
    rfl

variable {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G)
abbrev triangleObstruction : v.LoopClass z :=
  BasedTriangleContraction.theta z (v.basedTriangle z h g)
    (v.basedTriangle_bottom z h g) (v.basedTriangle_left z h g) (v.basedTriangle_right z h g)
variable (hL : L g a c * v.triangleObstruction z h g = L g a b * L (g*v.value a b) b c)

include hs hr hL in
lemma triangleLoops_correct :
    loopClass (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g) *
      v.triangleObstruction z h g =
    loopClass (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g) *
    loopClass (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b)) := by
  simp only [v.correctionLoop_class z L hs hr]
  exact hL

def terminalContraction : C(I × Triangle,v.TotalSpace) :=
  BasedTriangleContraction.contraction z (v.basedTriangle z h g)
    (v.basedTriangle_bottom z h g) (v.basedTriangle_left z h g) (v.basedTriangle_right z h g)
    (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g)
    (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g)
    (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b))
    (v.triangleLoops_correct z L hs hr h g hL)
lemma terminalContraction_initial (p : Triangle) :
    v.terminalContraction z L hs hr h g hL (0,p) = v.basedTriangle z h g p :=
  BasedTriangleContraction.contraction_initial _ _ _ _ _ _ _ _ _ p
lemma terminalContraction_final (p : Triangle) : v.terminalContraction z L hs hr h g hL (1,p) = z :=
  BasedTriangleContraction.contraction_final _ _ _ _ _ _ _ _ _ p
lemma terminalContraction_bottom (t s : I) :
    v.terminalContraction z L hs hr h g hL (t,quotient (s,0)) =
      v.correctionSquare z L (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g (t,s) :=
  BasedTriangleContraction.contraction_bottom _ _ _ _ _ _ _ _ _ t s
lemma terminalContraction_left (t s : I) :
    v.terminalContraction z L hs hr h g hL (t,quotient (0,s)) =
      v.correctionSquare z L (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g (t,s) :=
  BasedTriangleContraction.contraction_left _ _ _ _ _ _ _ _ _ t s
lemma terminalContraction_right (t s : I) :
    v.terminalContraction z L hs hr h g hL (t,quotient (1,s)) =
      v.correctionSquare z L (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,s) :=
  BasedTriangleContraction.contraction_right _ _ _ _ _ _ _ _ _ t s

def correctedTriangle : C(I × Triangle,v.TotalSpace) :=
  PrismConcat.concat (v.triangleHomotopy z h g) (v.terminalContraction z L hs hr h g hL)
    (fun p => (v.terminalContraction_initial z L hs hr h g hL p).symm)
lemma correctedTriangle_initial (p : Triangle) :
    v.correctedTriangle z L hs hr h g hL (0,p) = v.triangleLift h g p :=
  (PrismConcat.initial (v.triangleHomotopy z h g) (v.terminalContraction z L hs hr h g hL)
    (fun q => (v.terminalContraction_initial z L hs hr h g hL q).symm) p).trans
      (v.triangleHomotopy_initial z h g p)
lemma correctedTriangle_final (p : Triangle) : v.correctedTriangle z L hs hr h g hL (1,p) = z :=
  (PrismConcat.final (v.triangleHomotopy z h g) (v.terminalContraction z L hs hr h g hL)
    (fun q => (v.terminalContraction_initial z L hs hr h g hL q).symm) p).trans
      (v.terminalContraction_final z L hs hr h g hL p)
lemma correctedTriangle_bottom (t s : I) :
    v.correctedTriangle z L hs hr h g hL (t,quotient (s,0)) =
      v.correctedEdge z L (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g (t,s) :=
  PrismConcat.agree _ _ _ _ _ _ _ _ (fun t => v.triangleHomotopy_bottom z h g t s)
    (fun t => v.terminalContraction_bottom z L hs hr h g hL t s) t
lemma correctedTriangle_left (t s : I) :
    v.correctedTriangle z L hs hr h g hL (t,quotient (0,s)) =
      v.correctedEdge z L (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g (t,s) :=
  PrismConcat.agree _ _ _ _ _ _ _ _ (fun t => v.triangleHomotopy_left z h g t s)
    (fun t => v.terminalContraction_left z L hs hr h g hL t s) t
lemma correctedTriangle_right (t s : I) :
    v.correctedTriangle z L hs hr h g hL (t,quotient (1,s)) =
      v.correctedEdge z L (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,s) :=
  PrismConcat.agree _ _ _ _ _ _ _ _ (fun t => v.triangleHomotopy_right z h g t s)
    (fun t => v.terminalContraction_right z L hs hr h g hL t s) t

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
