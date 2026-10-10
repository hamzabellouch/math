import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronMonodromy

namespace OAI

/-! The triangle relations and rooted path groupoid calculations in the
actual realization. -/
noncomputable section

open Set
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

omit [Fintype V] in
lemma edge_of_subset {s : Finset V} (hs : s ∈ K.faces) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) : {a,b} ∈ K.faces := by
  apply (K.isRelLowerSet_faces hs).2 _ (by simp)
  simpa using (Finset.insert_subset_iff.mpr ⟨ha,Finset.singleton_subset_iff.mpr hb⟩)

omit [Fintype V] in
lemma edge_self (a : V) : {a,a} ∈ K.faces := by simpa using K.singleton_mem a

@[simp] lemma edgePath_self (a : V) (h : {a,a} ∈ K.faces) :
    edgePath K h = Path.refl (vertex K a) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact AffineMap.lineMap_same_apply _ _

lemma edgePath_triangle {a b c : V} (hs : {a,b,c} ∈ K.faces)
    (hab : {a,b} ∈ K.faces) (hbc : {b,c} ∈ K.faces) (hac : {a,c} ∈ K.faces) :
    ((edgePath K hab).trans (edgePath K hbc)).Homotopic (edgePath K hac) := by
  apply homotopic_in_face K hs
  · intro t
    have ht := mem_range_self (f := (edgePath K hab).trans (edgePath K hbc)) t
    rw [Path.trans_range] at ht
    rcases ht with ⟨u,hu⟩|⟨u,hu⟩ <;> rw [←hu]
    · unfold edgePath facePath
      exact straight_mem_face K _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp)) u
    · unfold edgePath facePath
      exact straight_mem_face K _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp)) u
  · intro t
    unfold edgePath facePath
    exact straight_mem_face K _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp)) t

namespace RootedPaths
variable {K} (o : V) (R : ∀ a : V, Path.Homotopic.Quotient (vertex K o) (vertex K a))

abbrev PiOne := (FundamentalGroup (Carrier K) (vertex K o))ᵐᵒᵖ

def based {a b : V} (p : Path.Homotopic.Quotient (vertex K a) (vertex K b)) : PiOne (K := K) o :=
  MulOpposite.op ((R a).trans (p.trans (R b).symm))

omit [DecidableEq V] in
lemma based_refl (a : V) : based o R (.refl (vertex K a)) = 1 := by
  apply MulOpposite.unop_injective
  change (R a).trans ((Path.Homotopic.Quotient.refl _).trans (R a).symm) = .refl _
  simp

omit [DecidableEq V] in
lemma based_trans {a b c : V} (p : Path.Homotopic.Quotient (vertex K a) (vertex K b))
    (q : Path.Homotopic.Quotient (vertex K b) (vertex K c)) :
    based o R (p.trans q) = based o R p * based o R q := by
  apply MulOpposite.unop_injective
  change (R a).trans ((p.trans q).trans (R c).symm) =
    ((R a).trans (p.trans (R b).symm)).trans ((R b).trans (q.trans (R c).symm))
  simp only [Path.Homotopic.Quotient.trans_assoc]
  have hc : (R b).symm.trans ((R b).trans (q.trans (R c).symm)) = q.trans (R c).symm := by
    rw [←Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  rw [hc]

omit [DecidableEq V] in
lemma based_route (hR : R o = .refl _) (a : V) : based o R (R a) = 1 := by
  apply MulOpposite.unop_injective
  change (R o).trans ((R a).trans (R a).symm) = .refl _
  rw [hR,Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.refl_trans]

omit [DecidableEq V] in
lemma based_loop (hR : R o = .refl _) (p : FundamentalGroup (Carrier K) (vertex K o)) :
    based o R p = MulOpposite.op p := by
  apply MulOpposite.unop_injective
  change (R o).trans (p.trans (R o).symm) = p
  rw [hR]
  have hr : (Path.Homotopic.Quotient.refl (vertex K o)).symm = .refl _ := rfl
  rw [hr,Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.refl_trans]

/-- Every edge yields the actual loop obtained by the fixed endpoint routes. -/
def edgeLoop (a b : V) : PiOne (K := K) o :=
  if h : {a,b} ∈ K.faces then based o R (.mk (edgePath K h)) else 1

lemma edgeLoop_of_edge {a b : V} (h : {a,b} ∈ K.faces) :
    edgeLoop o R a b = based o R (.mk (edgePath K h)) := dite_eq_left h

/-- The actual triangle disks imply a group-valued flat cocycle. -/
def voltage : Voltage K (PiOne (K := K) o) where
  value := edgeLoop o R
  self a := by rw [edgeLoop_of_edge o R (edge_self K a),edgePath_self]; exact based_refl o R a
  triangle a b c h := by
    have hab := edge_of_subset K h (a := a) (b := b) (by simp) (by simp)
    have hbc := edge_of_subset K h (a := b) (b := c) (by simp) (by simp)
    have hac := edge_of_subset K h (a := a) (b := c) (by simp) (by simp)
    rw [edgeLoop_of_edge o R hab,edgeLoop_of_edge o R hbc,edgeLoop_of_edge o R hac,
      ←based_trans]
    congr 1
    exact Path.Homotopic.Quotient.eq.mpr (edgePath_triangle K h hab hbc hac)

lemma eval_chain {a b : V} (p : EdgeChain K a b) :
    Voltage.EdgeChain.eval (voltage o R) p = based o R p.pathClass := by
  induction p with
  | nil a => exact (based_refl o R a).symm
  | @cons a b c h p ih =>
    rw [Voltage.EdgeChain.eval_cons,ih,EdgeChain.pathClass_cons,based_trans]
    congr 1
    exact edgeLoop_of_edge o R h
end RootedPaths

/-- Actual edge-chain routes exist in every path-connected finite realization. -/
def edgeRoutes [PathConnectedSpace (Carrier K)] (o : V) (a : V) : EdgeChain K o a :=
  if h : a = o then h.symm ▸ .nil o else
    (edgePath_representative K (PathConnectedSpace.somePath (vertex K o) (vertex K a))).choose

@[simp] lemma edgeRoutes_self [PathConnectedSpace (Carrier K)] (o : V) :
    edgeRoutes K o o = .nil o := by simp [edgeRoutes]

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
