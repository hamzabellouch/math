import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronDeck
import OAI.Geometry.HyperbolicGroups.EdgeChain

namespace OAI

/-! Actual path-homotopy invariance of edge voltages, obtained from the
constructed covering and its literal charts. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def inChart (a : V) (x : Carrier K) (g : G) : v.TotalSpace :=
  (v.core.localTriv a).toOpenPartialHomeomorph.symm (x,g)

@[simp] lemma inChart_proj (a : V) (x : Carrier K) (g : G) :
    v.proj (v.inChart a x g) = x := rfl

@[simp] lemma inChart_coordinate (a : V) (x : Carrier K) (g : G) :
    v.coordinate (v.inChart a x g) = g * v.value a (v.core.indexAt x) := rfl

def chartFiber (a : V) (x : Carrier K) (g : G) : v.proj ⁻¹' {x} :=
  ⟨v.inChart a x g,rfl⟩

def vertexFiber (a : V) (g : G) : v.proj ⁻¹' {vertex K a} :=
  ⟨⟨vertex K a,g⟩,rfl⟩

lemma indexAt_vertex (a : V) : v.core.indexAt (vertex K a) = a :=
  (vertex_in_openStar K (v.core.mem_baseSet_at (vertex K a))).symm

@[simp] lemma chartFiber_vertex (a : V) (g : G) :
    v.chartFiber a (vertex K a) g = v.vertexFiber a g := by
  apply Subtype.ext
  apply v.totalSpace_ext
  · rfl
  · change g * v.value a (v.core.indexAt (vertex K a)) = g
    rw [indexAt_vertex,v.self,mul_one]

lemma chartFiber_change (x : Carrier K) {a b : V}
    (ha : x ∈ openStar K a) (hb : x ∈ openStar K b) (g : G) :
    v.chartFiber b x (g * v.value a b) = v.chartFiber a x g := by
  apply Subtype.ext
  apply v.totalSpace_ext
  · rfl
  change (g * v.value a b) * v.value b (v.core.indexAt x) = g * v.value a (v.core.indexAt x)
  rw [mul_assoc,v.triangle a b _ (triangle_of_positive K x ha hb (v.core.mem_baseSet_at x))]

def liftInChart {x y : Carrier K} (a : V) (p : Path x y)
    (hp : ∀ t, p t ∈ openStar K a) (g : G) :
    Path (v.inChart a x g) (v.inChart a y g) where
  toFun t := v.inChart a (p t) g
  continuous_toFun := (v.core.localTriv a).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
    (p.continuous.prodMk continuous_const) (fun t => (v.core.localTriv a).mem_target.mpr (hp t))
  source' := by rw [p.source]
  target' := by rw [p.target]

lemma monodromy_inChart {x y : Carrier K} (a : V) (p : Path x y)
    (hp : ∀ t, p t ∈ openStar K a) (g : G) :
    v.isCoveringMap.monodromy (.mk p) (v.chartFiber a x g) = v.chartFiber a y g := by
  apply v.isCoveringMap.monodromy_eq_of_map_eq (.mk (v.liftInChart a p hp g))
  rfl

lemma monodromy_starPath (a : V) (x : Carrier K) (hx : x ∈ openStar K a) (g : G) :
    v.isCoveringMap.monodromy (.mk (starPath K a x hx)) (v.vertexFiber a g) =
      v.chartFiber a x g := by
  simpa only [chartFiber_vertex] using v.monodromy_inChart a (starPath K a x hx)
    (starPath_mem K a x hx) g

lemma monodromy_symm {x y : Carrier K} (p : Path.Homotopic.Quotient x y)
    (e : v.proj ⁻¹' {x}) :
    v.isCoveringMap.monodromy p.symm (v.isCoveringMap.monodromy p e) = e := by
  rw [←v.isCoveringMap.monodromy_trans_apply,Path.Homotopic.Quotient.trans_symm,
    v.isCoveringMap.monodromy_refl]
  rfl

/-- The midpoint lies in both endpoint stars, even for a collapsed edge. -/
def edgeMid {a b : V} (h : {a,b} ∈ K.faces) : Carrier K :=
  edgePath K h ⟨1/2,by norm_num,by norm_num⟩

lemma edgeMid_left {a b : V} (h : {a,b} ∈ K.faces) :
    edgeMid h ∈ openStar K a := by
  change 0 < (AffineMap.lineMap (vertex K a).val (vertex K b).val (1/2 : ℝ)) a
  rw [AffineMap.lineMap_apply_module]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have ha : (vertex K a).val a = 1 := by simp [vertex]
  rw [ha]
  have hb := (vertex K b).property.1 a
  linarith

lemma edgeMid_right {a b : V} (h : {a,b} ∈ K.faces) :
    edgeMid h ∈ openStar K b := by
  change 0 < (AffineMap.lineMap (vertex K a).val (vertex K b).val (1/2 : ℝ)) b
  rw [AffineMap.lineMap_apply_module]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hb : (vertex K b).val b = 1 := by simp [vertex]
  rw [hb]
  have ha := (vertex K a).property.1 b
  linarith

lemma monodromy_edge {a b : V} (h : {a,b} ∈ K.faces) (g : G) :
    v.isCoveringMap.monodromy (.mk (edgePath K h)) (v.vertexFiber a g) =
      v.vertexFiber b (g * v.value a b) := by
  let x : Carrier K := edgeMid h
  have ha : x ∈ openStar K a := edgeMid_left h
  have hb : x ∈ openStar K b := edgeMid_right h
  have hh := Path.Homotopic.Quotient.eq.mpr (radial_bridge K x ha hb)
  rw [←hh,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm,
    v.isCoveringMap.monodromy_trans_apply,v.monodromy_starPath]
  rw [←v.chartFiber_change x ha hb g]
  rw [←v.monodromy_starPath b x hb (g * v.value a b),v.monodromy_symm]

namespace EdgeChain
variable {v} {a b : V}
def eval (v : Voltage K G) {a b : V} (p : FinitePolyhedron.EdgeChain K a b) : G := by
  induction p with
  | nil _ => exact 1
  | @cons a b c h q ih => exact v.value a b * ih

omit [Fintype V] [TopologicalSpace G] [DiscreteTopology G] in
@[simp] lemma eval_nil (a : V) : eval v (.nil a) = 1 := rfl
omit [Fintype V] [TopologicalSpace G] [DiscreteTopology G] in
@[simp] lemma eval_cons {a b c : V} (h : {a,b} ∈ K.faces) (q : FinitePolyhedron.EdgeChain K b c) :
    eval v (.cons h q) = v.value a b * eval v q := rfl

lemma monodromy (q : FinitePolyhedron.EdgeChain K a b) (g : G) :
    v.isCoveringMap.monodromy q.pathClass (v.vertexFiber a g) =
      v.vertexFiber b (g * eval v q) := by
  induction q generalizing g with
  | nil a => simp [FinitePolyhedron.EdgeChain.pathClass_nil,v.isCoveringMap.monodromy_refl]
  | cons h q ih =>
    rw [FinitePolyhedron.EdgeChain.pathClass_cons,v.isCoveringMap.monodromy_trans_apply,
      v.monodromy_edge,ih,eval_cons,mul_assoc]
end EdgeChain

/-- Every literal triangular cocycle is invariant under actual continuous
relative-endpoint path homotopies, not just formal triangle moves. -/
theorem eval_eq_of_homotopic {a b : V} (p q : FinitePolyhedron.EdgeChain K a b)
    (h : p.path.Homotopic q.path) : EdgeChain.eval v p = EdgeChain.eval v q := by
  have hh := congrArg (fun z => v.isCoveringMap.monodromy z (v.vertexFiber a 1))
    (Path.Homotopic.Quotient.eq.mpr h)
  rw [EdgeChain.monodromy,EdgeChain.monodromy] at hh
  have he := congrArg (fun z : v.proj ⁻¹' {vertex K b} => v.coordinate z.val) hh
  simpa only [vertexFiber,coordinate,one_mul] using he

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
