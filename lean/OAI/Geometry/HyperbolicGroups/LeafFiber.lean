import Mathlib
import OAI.Geometry.HyperbolicGroups.StarFiber

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

/-- A total extension of the specified distinct leaf values. The filler only
occupies other field names and plays no part in the pinned statistic. -/
def leafValues (U : Finset F) (b : B ↪ A) (a₀ : A) : Var (B := B) U → A
  | .inl _ => a₀
  | .inr jf => b jf.1

omit [Fintype F] [Fintype B] [Fintype A] [DecidableEq F] [DecidableEq B]
  [DecidableEq A] [Nonempty B] in
lemma leafValues_fieldwise (U : Finset F) (b : B ↪ A) (a₀ : A) :
    PinnedAssignments.Fieldwise (field U) (leafValues U b a₀) := by
  apply (fieldwise_iff U _).mpr
  intro f j k h
  exact b.injective h

omit [Fintype A] [DecidableEq B] [DecidableEq A] [Nonempty B] in
lemma leaf_pin_fieldwise (U : Finset F) (e : F) (b : B ↪ A) (a₀ : A) :
    PinnedAssignments.PinFieldwise (field U) (leafPins U e) (leafValues U b a₀) := by
  intro v _ w _
  exact leafValues_fieldwise U b a₀ v w

def starLeaves (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (w : TableModel.Entry (A := A) support → Bool) (z : Stars (B := B) support U w) : B ↪ A where
  toFun j := z.val (coord U j e)
  inj' := by
    intro j k h
    exact (fieldwise_iff U z.val).mp z.property.1 ⟨e,he⟩ (by simpa [coord,he] using h)

omit [Fintype A] [DecidableEq B] [DecidableEq A] [Nonempty B] in
lemma leaves_eq_iff (U : Finset F) (e : F) (he : e ∉ U) (b : B ↪ A) (a₀ : A)
    (σ : Var (B := B) U → A) :
    (∀ j, σ (coord U j e) = b j) ↔ ∀ v ∈ leafPins U e, σ v = leafValues U b a₀ v := by
  constructor
  · intro h v hv
    have ht := (mem_leafPins U e v).mp hv
    cases v with
    | inl f => exact False.elim (he ((show f.val = e from ht) ▸ f.property))
    | inr jf =>
      obtain ⟨j,f⟩ := jf
      have hf : f = ⟨e,he⟩ := Subtype.ext ht
      subst f
      simpa [coord,he,leafValues] using h j
  · intro h j
    have hv : coord (B := B) U j e ∈ leafPins U e := by simp
    simpa [coord,he,leafValues] using h _ hv

omit [DecidableEq R] in
/-- The leaf count is the exact fiber size of the uniform present-star law,
not the count of a surrogate independently resampled star. -/
theorem card_leaf_fiber (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (w : TableModel.Entry (A := A) support → Bool) (b : B ↪ A) (a₀ : A) :
    Fintype.card {z : Stars (B := B) support U w // starLeaves support U e he w z = b} =
      leafCount support U e (leafValues U b a₀) w := by
  classical
  let ξ := leafValues U b a₀
  let H : (Var (B := B) U → A) → Prop := BernoulliCandidates.Present (row support U) w
  let E := {z : Var (B := B) U → A // PinnedAssignments.Fieldwise (field U) z ∧
    (∀ v ∈ leafPins U e, z v = ξ v) ∧ H z}
  let e₁ : {z : Stars (B := B) support U w // starLeaves support U e he w z = b} ≃ E :=
    { toFun := fun z => ⟨z.val.val,z.val.property.1,
        (leaves_eq_iff U e he b a₀ z.val.val).mp (fun j => by
          have hh := congrArg (fun f : B ↪ A => f j) z.property
          exact hh),z.val.property.2⟩
      invFun := fun z => ⟨⟨z.val,z.property.1,z.property.2.2⟩,by
        apply DFunLike.ext
        intro j
        exact (leaves_eq_iff U e he b a₀ z.val).mpr z.property.2.1 j⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ := PinnedAssignments.fiberEquiv (field U) (leafPins U e) ξ H
  let C := PinnedAssignments.candidates (field U) (leafPins U e) ξ
  let row' := fun τ => row support U (PinnedAssignments.extend (leafPins U e) ξ τ)
  let e₃ : {τ : PinnedAssignments.Free (leafPins U e) → A // τ ∈ C ∧ H (PinnedAssignments.extend (leafPins U e) ξ τ)} ≃
      ↥(C.filter (BernoulliCandidates.Present row' w)) :=
    { toFun := fun τ => ⟨τ.val,Finset.mem_filter.mpr τ.property⟩
      invFun := fun τ => ⟨τ.val,Finset.mem_filter.mp τ.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe,leafCount,BernoulliCandidates.count,C,row',ξ] using
    Fintype.card_congr ((e₁.trans e₂).trans e₃)

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
