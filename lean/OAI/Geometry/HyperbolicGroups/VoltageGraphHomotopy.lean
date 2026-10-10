import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronVoltage
import OAI.Geometry.HyperbolicGroups.EdgeContraction
import OAI.Geometry.HyperbolicGroups.VoltageEdges

namespace OAI

/-! A coherent contraction of the actual lifted one-skeleton. The negative
orientation uses spatial reversal of the SAME square, not another choice. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

omit [Fintype V] [LinearOrder V] [TopologicalSpace G] [DiscreteTopology G] in
lemma value_reverse_mul {a b : V} (h : {a,b} ∈ K.faces) (g : G) :
    (g * v.value a b) * v.value b a = g := by
  rw [mul_assoc,v.reverse h,mul_inv_cancel,mul_one]

variable [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
def vertexTrack (a : V) (g : G) : Path (v.vertexLift a g) z := by
  classical
  exact if h : v.vertexLift a g = z then (Path.refl z).cast h rfl
  else (PathConnectedSpace.joined (v.vertexLift a g) z).some

omit [LinearOrder V] in
lemma vertexTrack_fixed (a : V) (g : G) (h : v.vertexLift a g = z) (t : I) :
    v.vertexTrack z a g t = z := by
  simp [vertexTrack,h]

def rawEdgeHomotopy {a b : V} (h : {a,b} ∈ K.faces) (g : G) : C(I × I,v.TotalSpace) :=
  EdgeContraction.contraction (v.edgeLift h g) (v.vertexTrack z a g)
    (v.vertexTrack z b (g * v.value a b))

def edgeHomotopy {a b : V} (h : {a,b} ∈ K.faces) (g : G) : C(I × I,v.TotalSpace) :=
  if a = b then (v.vertexTrack z a g).toContinuousMap.comp (⟨Prod.fst,continuous_fst⟩ : C(I × I,I))
  else if a < b then v.rawEdgeHomotopy z h g
  else (v.rawEdgeHomotopy z (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
    (g*v.value a b)).comp ⟨fun ts => (ts.1,unitInterval.symm ts.2),by fun_prop⟩

lemma edgeHomotopy_initial {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.edgeHomotopy z h g (0,s) = v.edgeLift h g s := by
  unfold edgeHomotopy
  split_ifs with hab hlt
  · subst b
    change v.vertexTrack z a g 0 = _
    rw [Path.source]
    exact (v.edgeLift_self a g s).symm
  · exact EdgeContraction.contraction_initial _ _ _ s
  · change v.rawEdgeHomotopy z _ _ (0,unitInterval.symm s) = _
    rw [rawEdgeHomotopy,EdgeContraction.contraction_initial,v.edgeLift_reverse,unitInterval.symm_symm]

lemma edgeHomotopy_final {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.edgeHomotopy z h g (1,s) = z := by
  unfold edgeHomotopy
  split_ifs
  · exact Path.target _
  · exact EdgeContraction.contraction_final _ _ _ s
  · exact EdgeContraction.contraction_final _ _ _ (unitInterval.symm s)

lemma edgeHomotopy_left {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.edgeHomotopy z h g (t,0) = v.vertexTrack z a g t := by
  unfold edgeHomotopy
  split_ifs
  · rfl
  · exact EdgeContraction.contraction_left _ _ _ t
  · change v.rawEdgeHomotopy z _ _ (t,unitInterval.symm 0) = _
    rw [unitInterval.symm_zero,rawEdgeHomotopy,EdgeContraction.contraction_right,v.value_reverse_mul h]

lemma edgeHomotopy_right {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.edgeHomotopy z h g (t,1) = v.vertexTrack z b (g*v.value a b) t := by
  unfold edgeHomotopy
  split_ifs with hab hlt
  · subst b
    change v.vertexTrack z a g t = v.vertexTrack z a (g*v.value a a) t
    rw [v.self a,mul_one]
  · exact EdgeContraction.contraction_right _ _ _ t
  · change v.rawEdgeHomotopy z _ _ (t,unitInterval.symm 1) = _
    rw [unitInterval.symm_one,rawEdgeHomotopy,EdgeContraction.contraction_left]

lemma edgeHomotopy_reverse {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t s : I) :
    v.edgeHomotopy z (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
      (g*v.value a b) (t,s) = v.edgeHomotopy z h g (t,unitInterval.symm s) := by
  by_cases hab : a = b
  · subst b
    simp only [edgeHomotopy,ite_true,eq_self]
    change v.vertexTrack z a (g*v.value a a) t = v.vertexTrack z a g t
    rw [v.self a,mul_one]
  by_cases hlt : a < b
  · have hnl : ¬ b < a := not_lt_of_gt hlt
    simp only [edgeHomotopy,hab,Ne.symm hab,ite_false,hlt,hnl,ite_true,ContinuousMap.comp_apply]
    rw [v.value_reverse_mul h]
    rfl
  · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)
    simp only [edgeHomotopy,hab,Ne.symm hab,ite_false,hlt,hgt,ite_true,ContinuousMap.comp_apply]
    change _ = v.rawEdgeHomotopy z _ _ (t,unitInterval.symm (unitInterval.symm s))
    rw [unitInterval.symm_symm]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
