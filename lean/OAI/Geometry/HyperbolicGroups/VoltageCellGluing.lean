import Mathlib
import OAI.Geometry.HyperbolicGroups.ClosedCoverGluing
import OAI.Geometry.HyperbolicGroups.VoltageClosedCells

namespace OAI

/-! Genuine homotopy gluing on the locally finite family of closed lifted
simplices, with no alteration of the voltage-cover topology. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  {X : Type*} [TopologicalSpace X]

def faceLiftHomeomorph (q : FaceAnchor (K := K) × G) :
    closedFace (K := K) q.1.val.1 ≃ₜ v.liftedClosedFace q :=
  (v.faceLift_closedEmbedding q.1.property.1 q.1.property.2 q.2).isEmbedding.toHomeomorph

variable (H : ∀ q : FaceAnchor (K := K) × G, C(I × closedFace (K := K) q.1.val.1,X))
  (ha : ∀ i j t x y,
    v.faceLift i.1.property.1 i.1.property.2 i.2 x = v.faceLift j.1.property.1 j.1.property.2 j.2 y →
      H i (t,x) = H j (t,y))

def homotopyOnRange (q : FaceAnchor (K := K) × G) : C(I × v.liftedClosedFace q,X) :=
  (H q).comp ((ContinuousMap.id I).prodMap
    ⟨(v.faceLiftHomeomorph q).symm,(v.faceLiftHomeomorph q).symm.continuous⟩)

include ha in
lemma homotopyOnRange_agree (i j : FaceAnchor (K := K) × G) (t : I) x
    (hi : x ∈ v.liftedClosedFace i) (hj : x ∈ v.liftedClosedFace j) :
    v.homotopyOnRange H i (t,⟨x,hi⟩) = v.homotopyOnRange H j (t,⟨x,hj⟩) := by
  apply ha
  have h1 := congrArg Subtype.val ((v.faceLiftHomeomorph i).apply_symm_apply ⟨x,hi⟩)
  have h2 := congrArg Subtype.val ((v.faceLiftHomeomorph j).apply_symm_apply ⟨x,hj⟩)
  exact h1.trans h2.symm

/-- The actual global continuous prism. -/
def glueFaceHomotopies : C(I × v.TotalSpace,X) :=
  ClosedCoverGluing.gluePrism v.liftedClosedFace v.liftedClosedFace_cover
    v.liftedClosedFace_closed v.liftedClosedFace_locallyFinite
    (v.homotopyOnRange H) (v.homotopyOnRange_agree H ha)

lemma glueFaceHomotopies_apply (q : FaceAnchor (K := K) × G) (t : I)
    (x : closedFace (K := K) q.1.val.1) :
    v.glueFaceHomotopies H ha (t,v.faceLift q.1.property.1 q.1.property.2 q.2 x) = H q (t,x) := by
  rw [glueFaceHomotopies,ClosedCoverGluing.gluePrism_apply _ _ _ _ _ _ q t
    ⟨_,Set.mem_range_self x⟩]
  change H q (t,(v.faceLiftHomeomorph q).symm ((v.faceLiftHomeomorph q) x)) = _
  rw [(v.faceLiftHomeomorph q).symm_apply_apply]

lemma glueFaceHomotopies_endpoint (f : v.TotalSpace → X) (t : I)
    (hf : ∀ q x, H q (t,x) = f (v.faceLift q.1.property.1 q.1.property.2 q.2 x))
    (e : v.TotalSpace) : v.glueFaceHomotopies H ha (t,e) = f e := by
  obtain ⟨q,hq⟩ := Set.iUnion_eq_univ_iff.mp v.liftedClosedFace_cover e
  obtain ⟨x,rfl⟩ := hq
  rw [glueFaceHomotopies_apply,hf]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
