import Mathlib
import OAI.Geometry.HyperbolicGroups.StarVariance
import OAI.Geometry.HyperbolicGroups.Conditioning

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

omit [Fintype R] [DecidableEq R] in
lemma residual_ne_branch (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (σ : PinnedAssignments.Free (branchPins U j₀) → A)
    (hσ : σ ∈ PinnedAssignments.candidates (field U) (branchPins U j₀) ξ)
    (s : ExtPos support U j₀) (r : R) :
    row support U (PinnedAssignments.extend (branchPins U j₀) ξ σ) (extPos support U j₀ s) ≠
      TableModel.row support (fun f => ξ (coord U j₀ f)) r := by
  intro he
  have hr : s.2.val = r := congrArg Sigma.fst he
  subst r
  have hf : ∃ f ∈ support s.2.val, f ∉ U := by
    simpa [Finset.subset_iff] using s.2.property
  obtain ⟨f,hf,hfu⟩ := hf
  have hex : (fun f : support s.2.val =>
      PinnedAssignments.extend (branchPins U j₀) ξ σ (coord U s.1.val f.val)) =
      (fun f : support s.2.val => ξ (coord U j₀ f.val)) := eq_of_heq (Sigma.mk.inj he).2
  have hread := congrFun hex ⟨f,hf⟩
  have hpin : coord U j₀ f ∈ branchPins U j₀ := Finset.mem_image_of_mem _ (Finset.mem_univ f)
  have hp := PinnedAssignments.extend_pin (branchPins U j₀) ξ σ _ hpin
  have hi := (Finset.mem_filter.mp hσ).2
  have hcoord := hi (coord U s.1.val f) (coord U j₀ f) (by simp) (hread.trans hp.symm)
  have hj : s.1.val = j₀ := by simpa [coord,hfu] using hcoord
  exact s.1.property hj

lemma extension_depends (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (w z : TableModel.Entry (A := A) support → Bool)
    (hwz : ∀ i, i ∉ Finset.univ.image (TableModel.row support (fun f => ξ (coord U j₀ f))) → w i = z i) :
    extensionCount support U j₀ ξ w = extensionCount support U j₀ ξ z := by
  unfold extensionCount BernoulliCandidates.count
  congr 1
  apply Finset.filter_congr
  intro σ hσ
  have ht (s : ExtPos support U j₀) :
      w (row support U (PinnedAssignments.extend (branchPins U j₀) ξ σ) (extPos support U j₀ s)) =
      z (row support U (PinnedAssignments.extend (branchPins U j₀) ξ σ) (extPos support U j₀ s)) := by
    apply hwz
    rintro hm
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hm
    exact residual_ne_branch support U j₀ ξ σ hσ s r hr.symm
  simp only [BernoulliCandidates.Present,ht]

/-- The entire law of the residual extension count is unchanged by conditioning
on the fixed branch being an actual match. -/
theorem extension_conditioning (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (g : ℕ → ℝ) :
    (TableModel.law support p hp).expect (fun w =>
      if TableModel.IsMatch support w (fun f => ξ (coord U j₀ f)) then
        g (extensionCount support U j₀ ξ w) else 0) =
      (∏ r, p r) * (TableModel.law support p hp).expect (fun w => g (extensionCount support U j₀ ξ w)) := by
  have hh := FiniteLaw.bernoulliProduct_event_mul (fun i : TableModel.Entry (A := A) support => p i.1)
    (fun i => hp i.1) (Finset.univ.image (TableModel.row support (fun f => ξ (coord U j₀ f))))
    (fun w => g (extensionCount support U j₀ ξ w))
    (fun w z h => congrArg g (extension_depends support U j₀ ξ w z h))
  have he (w : TableModel.Entry (A := A) support → Bool) :
      (∀ i ∈ Finset.univ.image (TableModel.row support (fun f => ξ (coord U j₀ f))), w i = true) ↔
        TableModel.IsMatch support w (fun f => ξ (coord U j₀ f)) := by
    simp [TableModel.IsMatch]
  simp only [he,Finset.prod_image (fun _ _ _ _ h => TableModel.row_injective support _ h)] at hh
  exact hh

lemma leaf_expect (support : R → Finset F) (U : Finset F) (e : F)
    (ξ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    (TableModel.law support p hp).expect (fun w => (leafCount support U e ξ w : ℝ)) =
      (PinnedAssignments.candidates (field U) (leafPins U e) ξ).card *
        ∏ s : Pos (B := B) support U, p (array support U s) := by
  apply BernoulliCandidates.expect_count
  · intro σ hσ
    exact row_injective support U _ ((fieldwise_iff U _).mp (Finset.mem_filter.mp hσ).2)
  · intros; rfl

lemma extension_expect (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    (TableModel.law support p hp).expect (fun w => (extensionCount support U j₀ ξ w : ℝ)) =
      (PinnedAssignments.candidates (field U) (branchPins U j₀) ξ).card *
        ∏ s : ExtPos support U j₀, p s.2.val := by
  apply BernoulliCandidates.expect_count
  · intro σ hσ
    exact ext_injective support U j₀ _ (Finset.mem_filter.mp hσ).2
  · intros; rfl

lemma leaf_expect_eq (support : R → Finset F) (U : Finset F) (e : F)
    (ξ ζ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hξ : PinnedAssignments.PinFieldwise (field U) (leafPins U e) ξ)
    (hζ : PinnedAssignments.PinFieldwise (field U) (leafPins U e) ζ) :
    (TableModel.law support p hp).expect (fun w => (leafCount support U e ξ w : ℝ)) =
      (TableModel.law support p hp).expect (fun w => (leafCount support U e ζ w : ℝ)) := by
  rw [leaf_expect,leaf_expect,PinnedAssignments.card_candidates_eq _ _ ξ ζ hξ hζ]

lemma extension_expect_eq (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ ζ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) :
    (TableModel.law support p hp).expect (fun w => (extensionCount support U j₀ ξ w : ℝ)) =
      (TableModel.law support p hp).expect (fun w => (extensionCount support U j₀ ζ w : ℝ)) := by
  rw [extension_expect,extension_expect,PinnedAssignments.card_candidates_eq _ _ ξ ζ
    (branch_pin_fieldwise U j₀ ξ) (branch_pin_fieldwise U j₀ ζ)]

end StarModel
end HyperbolicObstruction
end
end

section

end
end

end OAI
