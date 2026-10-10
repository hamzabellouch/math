import Mathlib
import OAI.Geometry.HyperbolicGroups.StarVariance

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace PinnedAssignments
variable {W F A : Type*} [Fintype W] [Fintype F] [Fintype A]
  [DecidableEq W] [DecidableEq F] [DecidableEq A]

omit [Fintype W] [Fintype A] [DecidableEq A] in
lemma extend_restrict (P : Finset W) (ξ σ : W → A) (hσ : ∀ v ∈ P, σ v = ξ v) :
    extend P ξ (fun v : Free P => σ v.val) = σ := by
  funext v
  by_cases hv : v ∈ P
  · simp [extend,hv,hσ v hv]
  · simp [extend,hv]

/-- No incidence or probabilistic assumption is hidden in the pinned-fiber
bijection: free assignments extend uniquely, with the original fieldwise rule. -/
def fiberEquiv (tag : W → F) (P : Finset W) (ξ : W → A) (H : (W → A) → Prop) :
    {σ : W → A // Fieldwise tag σ ∧ (∀ v ∈ P, σ v = ξ v) ∧ H σ} ≃
      {τ : Free P → A // τ ∈ candidates tag P ξ ∧ H (extend P ξ τ)} where
  toFun σ := ⟨fun v => σ.val v.val,by
    have he := extend_restrict P ξ σ.val σ.property.2.1
    constructor
    · simp only [candidates,Finset.mem_filter,Finset.mem_univ,true_and,he]
      exact σ.property.1
    · rw [he]; exact σ.property.2.2⟩
  invFun τ := ⟨extend P ξ τ.val,by
    exact ⟨(Finset.mem_filter.mp τ.property.1).2,
      fun v hv => extend_pin P ξ τ.val v hv,τ.property.2⟩⟩
  left_inv σ := Subtype.ext (extend_restrict P ξ σ.val σ.property.2.1)
  right_inv τ := by
    apply Subtype.ext
    funext v
    exact extend_free P ξ τ.val v

end PinnedAssignments
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

omit [Fintype B] [Fintype A] [DecidableEq A] [Nonempty B] in
lemma branch_eq_iff (U : Finset F) (j₀ : B) (ξ σ : Var (B := B) U → A) :
    (∀ f, σ (coord U j₀ f) = ξ (coord U j₀ f)) ↔
      ∀ v ∈ branchPins U j₀, σ v = ξ v := by
  constructor
  · intro h v hv
    obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp hv
    exact h f
  · intro h f
    exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ f))

omit [Fintype R] [Fintype B] [Fintype A] [DecidableEq R] [DecidableEq A] in
lemma fixed_branch_present (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (τ : PinnedAssignments.Free (branchPins U j₀) → A)
    (w : TableModel.Entry (A := A) support → Bool)
    (hm : TableModel.IsMatch support w (fun f => ξ (coord U j₀ f))) :
    BernoulliCandidates.Present (row support U) w (PinnedAssignments.extend (branchPins U j₀) ξ τ) ↔
      BernoulliCandidates.Present
        (fun τ s => row support U (PinnedAssignments.extend (branchPins U j₀) ξ τ) (extPos support U j₀ s)) w τ := by
  constructor
  · intro h s
    exact h _
  · intro h
    apply (present_iff support U _ w).mpr
    intro j r
    by_cases hr : support r ⊆ U
    · have he : TableModel.row support (fun f => PinnedAssignments.extend (branchPins U j₀) ξ τ (coord U j f)) r =
          TableModel.row support (fun f => ξ (coord U j₀ f)) r := by
        unfold TableModel.row
        congr 1
        funext f
        have hf := hr f.property
        have hc : coord U j f.val = coord U j₀ f.val := by simp [coord,hf]
        dsimp only
        rw [hc]
        exact PinnedAssignments.extend_pin _ _ _ _ (by
          exact Finset.mem_image_of_mem (coord U j₀) (Finset.mem_univ f.val))
      rw [he]
      exact hm r
    · by_cases hj : j = j₀
      · subst j
        have he : TableModel.row support (fun f => PinnedAssignments.extend (branchPins U j₀) ξ τ (coord U j₀ f)) r =
            TableModel.row support (fun f => ξ (coord U j₀ f)) r := by
          unfold TableModel.row
          congr 1
          funext f
          exact PinnedAssignments.extend_pin _ _ _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ f.val))
        rw [he]
        exact hm r
      · exact h (⟨j,hj⟩,⟨r,hr⟩)

abbrev Stars (support : R → Finset F) (U : Finset F)
    (w : TableModel.Entry (A := A) support → Bool) :=
  {σ : Var (B := B) U → A // PinnedAssignments.Fieldwise (field U) σ ∧ BernoulliCandidates.Present (row support U) w σ}

abbrev Matches (support : R → Finset F) (w : TableModel.Entry (A := A) support → Bool) :=
  {σ : F → A // TableModel.IsMatch support w σ}

instance (support : R → Finset F) (U : Finset F) (w : TableModel.Entry (A := A) support → Bool) :
    Fintype (Stars (B := B) support U w) :=
  inferInstanceAs (Fintype {assignment : Var (B := B) U → A //
    PinnedAssignments.Fieldwise (field U) assignment ∧
      BernoulliCandidates.Present (row support U) w assignment})

instance (support : R → Finset F) (w : TableModel.Entry (A := A) support → Bool) :
    Fintype (Matches support w) :=
  inferInstanceAs (Fintype {assignment : F → A // TableModel.IsMatch support w assignment})

def starBranch (support : R → Finset F) (U : Finset F) (w : TableModel.Entry (A := A) support → Bool)
    (j : B) (σ : Stars (B := B) support U w) : Matches support w :=
  ⟨fun f => σ.val (coord U j f), (present_iff support U σ.val w).mp σ.property.2 j⟩

def branchValues (U : Finset F) (σ : F → A) : Var (B := B) U → A := fun v => σ (field U v)

omit [Fintype F] [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A] [Nonempty B] in
@[simp] lemma branchValues_coord (U : Finset F) (σ : F → A) (j : B) (f : F) :
    branchValues U σ (coord U j f) = σ f := by simp [branchValues]

omit [DecidableEq R] in
/-- The fixed-match extension statistic is exactly the size of the branch fiber
of actual, present, fieldwise-injective stars. -/
theorem card_branch_fiber (support : R → Finset F) (U : Finset F)
    (w : TableModel.Entry (A := A) support → Bool) (j₀ : B) (σ : Matches support w) :
    Fintype.card {z : Stars (B := B) support U w // starBranch support U w j₀ z = σ} =
      extensionCount support U j₀ (branchValues U σ.val) w := by
  classical
  let ξ := branchValues (B := B) U σ.val
  let H : (Var (B := B) U → A) → Prop := BernoulliCandidates.Present (row support U) w
  let E := {z : Var (B := B) U → A // PinnedAssignments.Fieldwise (field U) z ∧
    (∀ v ∈ branchPins U j₀, z v = ξ v) ∧ H z}
  let e₁ : {z : Stars (B := B) support U w // starBranch support U w j₀ z = σ} ≃ E :=
    { toFun := fun z => ⟨z.val.val,z.val.property.1,
        (branch_eq_iff U j₀ ξ z.val.val).mp (fun f => by
          have hh := congrFun (congrArg Subtype.val z.property) f
          simpa [starBranch,ξ] using hh),z.val.property.2⟩
      invFun := fun z => ⟨⟨z.val,z.property.1,z.property.2.2⟩,by
        apply Subtype.ext
        funext f
        simpa [starBranch,ξ] using (branch_eq_iff U j₀ ξ z.val).mpr z.property.2.1 f⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hm : TableModel.IsMatch support w (fun f => ξ (coord U j₀ f)) := by
    simpa [ξ] using σ.property
  let e₂ := PinnedAssignments.fiberEquiv (field U) (branchPins U j₀) ξ H
  let C := PinnedAssignments.candidates (field U) (branchPins U j₀) ξ
  let row' := fun τ s => row support U (PinnedAssignments.extend (branchPins U j₀) ξ τ) (extPos support U j₀ s)
  let e₃ : {τ : PinnedAssignments.Free (branchPins U j₀) → A // τ ∈ C ∧ H (PinnedAssignments.extend (branchPins U j₀) ξ τ)} ≃
      ↥(C.filter (BernoulliCandidates.Present row' w)) :=
    { toFun := fun τ => ⟨τ.val,Finset.mem_filter.mpr ⟨τ.property.1,
        (fixed_branch_present support U j₀ ξ τ.val w hm).mp τ.property.2⟩⟩
      invFun := fun τ => ⟨τ.val,(Finset.mem_filter.mp τ.property).1,
        (fixed_branch_present support U j₀ ξ τ.val w hm).mpr (Finset.mem_filter.mp τ.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe,extensionCount,BernoulliCandidates.count,C,row',ξ] using Fintype.card_congr ((e₁.trans e₂).trans e₃)

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
