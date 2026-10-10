import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorFoundations

namespace OAI

universe u

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

noncomputable def closedStarSpan {B : Type*} [CStarAlgebra B] (s : Set B) :
    StarSubalgebra ℂ B := (StarAlgebra.adjoin ℂ s).topologicalClosure

lemma closedStarSpan_closed {B : Type*} [CStarAlgebra B] (s : Set B) :
    IsClosed (closedStarSpan s : Set B) := isClosed_closure

lemma subset_closedStarSpan {B : Type*} [CStarAlgebra B] (s : Set B) :
    s ⊆ closedStarSpan s := fun _ hx =>
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ s hx)

lemma closedStarSpan_le {B : Type*} [CStarAlgebra B] (s : Set B)
    (S : StarSubalgebra ℂ B) (hS : IsClosed (S : Set B)) (hs : s ⊆ S) :
    closedStarSpan s ≤ S :=
  StarSubalgebra.topologicalClosure_minimal
    (StarAlgebra.adjoin_le hs) hS

@[instance_reducible]
noncomputable def closedStarSpanCStar {B : Type*} [CStarAlgebra B] (s : Set B) :
    CStarAlgebra (closedStarSpan s) := by
  letI := closedStarSpan_closed s
  infer_instance

structure GroupRepresentation (G : Type u) [Group G] where
  hilbert : ComplexHilbert.{u}
  [nontrivial : Nontrivial hilbert]
  group : G →* unitary (hilbert →L[ℂ] hilbert)

attribute [instance] GroupRepresentation.nontrivial

def FullGroupAmbient (G : Type u) [Group G] : Type (u + 1) :=
  lp (fun π : GroupRepresentation G => π.hilbert →L[ℂ] π.hilbert) ∞

instance (G : Type u) [Group G] : CStarAlgebra (FullGroupAmbient G) := by
  unfold FullGroupAmbient
  exact { }

instance (G : Type u) [Group G] : CoeFun (FullGroupAmbient G)
    (fun _ => ∀ π : GroupRepresentation G, π.hilbert →L[ℂ] π.hilbert) := ⟨fun x => x.val⟩

variable {G : Type u} [Group G]

def fullGroupOperator (g : G) : FullGroupAmbient G :=
  ⟨fun π => π.group g, memℓp_infty ⟨1, by
    rintro _ ⟨π, rfl⟩
    exact le_of_eq (CStarRing.norm_coe_unitary (π.group g))⟩⟩

lemma fullGroupOperator_one : fullGroupOperator (1 : G) = 1 := by
  apply Subtype.ext
  funext π
  change (π.group 1 : π.hilbert →L[ℂ] π.hilbert) = 1
  simp

lemma fullGroupOperator_mul (g h : G) :
    fullGroupOperator (g * h) = fullGroupOperator g * fullGroupOperator h := by
  apply Subtype.ext
  funext π
  change (π.group (g * h) : π.hilbert →L[ℂ] π.hilbert) = (π.group g : _) * π.group h
  simp

lemma fullGroupOperator_inv (g : G) : fullGroupOperator g⁻¹ = star (fullGroupOperator g) := by
  apply Subtype.ext
  funext π
  change (π.group g⁻¹ : π.hilbert →L[ℂ] π.hilbert) = star (π.group g : _)
  rw [map_inv]
  rfl

def fullGroupSubalgebra (G : Type u) [Group G] : StarSubalgebra ℂ (FullGroupAmbient G) :=
  closedStarSpan (Set.range (fullGroupOperator (G := G)))

def FullGroupAlgebra (G : Type u) [Group G] : Type (u + 1) := fullGroupSubalgebra G

instance : CStarAlgebra (FullGroupAlgebra G) := closedStarSpanCStar _

def fullGroupElement (g : G) : FullGroupAlgebra G :=
  ⟨fullGroupOperator g, subset_closedStarSpan _ ⟨g, rfl⟩⟩

@[simp]
lemma fullGroupElement_one : fullGroupElement (1 : G) = 1 :=
  Subtype.ext fullGroupOperator_one

@[simp]
lemma fullGroupElement_mul (g h : G) :
    fullGroupElement (g * h) = fullGroupElement g * fullGroupElement h :=
  Subtype.ext (fullGroupOperator_mul g h)

@[simp]
lemma fullGroupElement_inv (g : G) : fullGroupElement g⁻¹ = star (fullGroupElement g) :=
  Subtype.ext (fullGroupOperator_inv g)

lemma fullGroupElement_unitary (g : G) : fullGroupElement g ∈ unitary (FullGroupAlgebra G) := by
  constructor
  · rw [← fullGroupElement_inv, ← fullGroupElement_mul, inv_mul_cancel, fullGroupElement_one]
  · rw [← fullGroupElement_inv, ← fullGroupElement_mul, mul_inv_cancel, fullGroupElement_one]

def fullGroupUnitary : G →* unitary (FullGroupAlgebra G) where
  toFun g := ⟨fullGroupElement g, fullGroupElement_unitary g⟩
  map_one' := Subtype.ext fullGroupElement_one
  map_mul' g h := Subtype.ext (fullGroupElement_mul g h)

def fullGroupEvaluation (π : GroupRepresentation G) :
    FullGroupAlgebra G →⋆ₐ[ℂ] (π.hilbert →L[ℂ] π.hilbert) where
  toFun x := x.val π
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp]
lemma fullGroupEvaluation_element (π : GroupRepresentation G) (g : G) :
    fullGroupEvaluation π (fullGroupElement g) = π.group g := rfl

lemma norm_fullGroup_le_iff (x : FullGroupAlgebra G) {c : ℝ} (hc : 0 ≤ c) :
    ‖x‖ ≤ c ↔ ∀ π : GroupRepresentation G, ‖fullGroupEvaluation π x‖ ≤ c := by
  constructor
  · exact fun h π =>
      (NonUnitalStarAlgHom.norm_apply_le (fullGroupEvaluation π).toNonUnitalStarAlgHom x).trans h
  · intro h
    change ‖(x.val : FullGroupAmbient G)‖ ≤ c
    exact lp.norm_le_of_forall_le hc h

lemma fullGroupEvaluation_separates (x y : FullGroupAlgebra G)
    (h : ∀ π : GroupRepresentation G, fullGroupEvaluation π x = fullGroupEvaluation π y) : x = y := by
  apply Subtype.ext
  apply Subtype.ext
  funext π
  exact h π

end WeakPureInfiniteness
end

end OAI
