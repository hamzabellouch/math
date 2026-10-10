import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedron

namespace OAI

/-! A literal flat principal covering of a barycentric polyhedron, obtained
from edge voltages satisfying exactly the two-dimensional face relations.
The topology is Mathlib's fiber-bundle gluing topology, not the product.
This construction does not assert that the cover is simply connected. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] (K : AbstractSimplicialComplex V)

/-- The open star of a vertex in the actual barycentric realization. -/
def openStar (v : V) : Set (Carrier K) := {x | 0 < x.val v}

lemma openStar_isOpen (v : V) : IsOpen (openStar K v) :=
  isOpen_lt continuous_const ((continuous_apply v).comp continuous_subtype_val)

lemma exists_positive (x : Carrier K) : ∃ v, 0 < x.val v := by
  by_contra! h
  have hz : ∀ v, x.val v = 0 := fun v => le_antisymm (h v) (x.property.1 v)
  have hh := x.property.2.1
  simp only [hz,Finset.sum_const_zero] at hh
  norm_num at hh

variable [DecidableEq V]

lemma face_of_positive (x : Carrier K) {s : Finset V} (hs : s.Nonempty)
    (hpos : ∀ v ∈ s, 0 < x.val v) : s ∈ K.faces := by
  obtain ⟨t,ht,hxt⟩ := x.property.2.2
  refine (K.isRelLowerSet_faces ht).2 ?_ hs
  intro v hv
  by_contra hn
  have hp := hpos v hv
  rw [hxt v hn] at hp
  exact lt_irrefl _ hp

lemma triangle_of_positive (x : Carrier K) {a b c : V}
    (ha : 0 < x.val a) (hb : 0 < x.val b) (hc : 0 < x.val c) :
    {a,b,c} ∈ K.faces := by
  apply face_of_positive K x (by simp)
  intro v hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl|rfl|rfl <;> assumption

variable (G : Type*) [Group G]

/-- An edge-voltage cocycle. Values off the edge set are immaterial. -/
structure Voltage where
  value : V → V → G
  self : ∀ v, value v v = 1
  triangle : ∀ a b c, {a,b,c} ∈ K.faces → value a b * value b c = value a c

namespace Voltage
variable {K G} (v : Voltage K G)

omit [Fintype V] in
lemma reverse {a b : V} (h : {a,b} ∈ K.faces) : v.value b a = (v.value a b)⁻¹ := by
  have hh := v.triangle a b a (by
    have hf : ({a,b,a} : Finset V) = {a,b} := by ext z; simp; tauto
    rw [hf]; exact h)
  rw [v.self] at hh
  exact eq_inv_of_mul_eq_one_right hh

variable [TopologicalSpace G] [DiscreteTopology G]

/-- Charts retain the positive barycentric coordinate of their chosen vertex.
Multiplicative transition functions are locally constant, with the literal
triangular relation providing their cocycle identity. -/
def core : FiberBundleCore V (Carrier K) G where
  baseSet := openStar K
  isOpen_baseSet := openStar_isOpen K
  indexAt x := (exists_positive K x).choose
  mem_baseSet_at x := (exists_positive K x).choose_spec
  coordChange i j _ g := g * v.value i j
  coordChange_self i _ _ g := by rw [v.self,mul_one]
  continuousOn_coordChange i j :=
    ((continuous_of_discreteTopology : Continuous (fun g : G => g * v.value i j)).comp continuous_snd).continuousOn
  coordChange_comp i j k x hx g := by
    rw [mul_assoc,v.triangle i j k (triangle_of_positive K x hx.1.1 hx.1.2 hx.2)]

abbrev TotalSpace := v.core.TotalSpace
abbrev proj : v.TotalSpace → Carrier K := v.core.proj

lemma isCoveringMap : IsCoveringMap v.proj := FiberBundle.isCoveringMap

lemma proj_surjective : Function.Surjective v.proj := fun x => ⟨⟨x,(1 : G)⟩,rfl⟩

end Voltage
end HyperbolicObstruction.FinitePolyhedron
end

end OAI
