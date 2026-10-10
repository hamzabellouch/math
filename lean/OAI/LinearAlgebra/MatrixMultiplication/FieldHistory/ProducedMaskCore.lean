import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Tensors
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.ProducedBase
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.Subdivision

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryProducedMasks

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws InheritedMasks
open JointCanonicalization
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeChildWidth (ε : ℝ) (h : Active K tick) : ℝ :=
  (ε / 16 ^ h.val.1.stage.val) / 8

def halfPositionEquiv (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) (right : Bool) :
    Fin (branchPopulation allocation dilation w b) ≃
      Fin (population allocation dilation (w.1.child b right, w.2)) where
  toFun := halfPosition allocation dilation w b right
  invFun := unhalfPosition allocation dilation w b right
  left_inv := unhalf_halfPosition allocation dilation w b right
  right_inv := half_unhalfPosition allocation dilation w b right

def childHalfWord (allocation : Allocation) (dilation : ℕ)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (v : HistoryWord allocation dilation (h.val.1.child b right, h.val.2)) :
    Fin (branchPopulation allocation dilation h.val b) →
      Fin (activeHalfLength h) → Fin 7 :=
  fun i j => v (halfPosition allocation dilation h.val b right i)
    (Fin.cast (child_length h.val.1 b right).symm j)

theorem subsingleton_typeWindow {P A : Type*} [Fintype P] [Nonempty P]
    [Subsingleton A] [DecidableEq A] (η : ℝ) (hη : 0 ≤ η) (w : P → A) :
    typeWindow (fun _ : A => 1) η w := by
  intro a
  have hcount : wordPopulation w a = Fintype.card P := by
    apply Fintype.card_congr
    exact
      { toFun := Subtype.val
        invFun := fun i => ⟨i, Subsingleton.elim _ _⟩
        left_inv := fun i => Subtype.ext rfl
        right_inv := fun i => rfl }
  have hpos : (0 : ℝ) < Fintype.card P := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P)
  simpa only [empiricalLaw, hcount, div_self (ne_of_gt hpos), sub_self, abs_zero] using hη

theorem childHalfWord_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (v : HistoryWord allocation dilation (h.val.1.child b right, h.val.2))
    (hv : residentMask allocation dilation ε (h.val.1.child b right, h.val.2) side v)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (h.val.1.childLaw
        (halfShape h.val.1.parentShape (h.val.1.splitShape b) right)
        (h.val.2.symm side) a : ℝ)) (nativeChildWidth ε h)
      (h.val.1.statistic ∘ childHalfWord allocation dilation h b right v) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent =>
      have hp' : 0 < population allocation dilation
          ((Work.stageA parent).child b right, phi) := by
        rw [branchPopulation_half allocation dilation (.stageA parent, phi) b right]
        exact hp
      have hw := (Subdivision.typeWindow_reindex
        (residentLaw ((Work.stageA parent).child b right, phi) side)
        (ε / 8) (fun i => residentStatistic ((Work.stageA parent).child b right) (v i))
        (halfPositionEquiv allocation dilation (.stageA parent, phi) b right)).mpr (hv hp')
      have he : nativeChildWidth ε (⟨(.stageA parent, phi), ht⟩ : Active K tick) = ε / 8 := by
        norm_num [nativeChildWidth, Work.stage]
      rw [he]
      exact hw
  | stageB parent =>
      have hp' : 0 < population allocation dilation
          ((Work.stageB parent).child b right, phi) := by
        rw [branchPopulation_half allocation dilation (.stageB parent, phi) b right]
        exact hp
      have hw := (Subdivision.typeWindow_reindex
        (residentLaw ((Work.stageB parent).child b right, phi) side)
        (ε / 128) (fun i => residentStatistic ((Work.stageB parent).child b right) (v i))
        (halfPositionEquiv allocation dilation (.stageB parent, phi) b right)).mpr (hv hp')
      have he : nativeChildWidth ε (⟨(.stageB parent, phi), ht⟩ : Active K tick) = ε / 128 := by
        norm_num [nativeChildWidth, Work.stage, div_div]
      rw [he]
      exact hw
  | stageC parent =>
      let : Nonempty (Fin (branchPopulation allocation dilation (.stageC parent, phi) b)) :=
        ⟨⟨0, hp⟩⟩
      let : Subsingleton (Work.stageC parent).Statistic := by
        change Subsingleton PUnit
        infer_instance
      simp only [Work.childLaw, Rat.cast_one]
      apply subsingleton_typeWindow
      unfold nativeChildWidth
      positivity

theorem afterB_mask_of_part_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (h : BPositive K) (phi : Placement) (side : Fin 3)
    (w : ∀ i : Fin 3, HistoryWord allocation dilation (.partC (h, i), phi))
    (hw : ∀ i, residentMask allocation dilation ε (.partC (h, i), phi) side (w i)) :
    residentMask allocation dilation ε (.afterB h.val, phi) side
      (fun j => w (bSubdivisionPositionEquiv allocation dilation h phi j).1
        (bSubdivisionPositionEquiv allocation dilation h phi j).2) := by
  intro hp
  let P : Fin 3 → Type := fun i =>
    Fin (population allocation dilation (.partC (h, i), phi))
  let e := bSubdivisionPositionEquiv allocation dilation h phi
  have hsize : 0 < Fintype.card (Σ i, P i) := by
    rw [← Fintype.card_congr e]
    simpa only [Fintype.card_fin] using hp
  have hwidth : ∀ _ : Fin 3, ε / 256 ≤ ε / 128 := by
    intro i
    linarith
  have hparts : Subdivision.partWindows P
      (residentLaw (.afterB h.val, phi) side) (fun _ => ε / 256)
      (fun i => CWCompleteStatistics.twoStatistic ∘ w i) := by
    intro i hi
    have hi' : 0 < population allocation dilation (.partC (h, i), phi) := by
      simpa only [P, Fintype.card_fin] using hi
    exact hw i hi'
  exact Subdivision.statisticWindow_concatenate_at
    (A := ResidentStatistic (.afterB h.val)) P e CWCompleteStatistics.twoStatistic
    (residentLaw (.afterB h.val, phi) side) (ε / 128) (fun _ => ε / 256)
    (div_nonneg hε (by norm_num)) hwidth hsize w hparts

def producedChildWord (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    HistoryWord allocation dilation (h.val.1.child b right, h.val.2) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => exact x ⟨(.afterA ⟨parent, b, right⟩, phi), ht.symm⟩
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · let g : BPositive K := ⟨⟨parent, b, right⟩, hp⟩
        let e := bSubdivisionPositionEquiv allocation dilation g phi
        exact fun j => x ⟨(.partC (g, (e j).1), phi), ht.symm⟩ (e j).2
      · exact x ⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩
  | stageC parent => exact x ⟨(.afterC (parent, b, right), phi), ht.symm⟩

theorem producedChildWord_mask (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    residentMask allocation dilation ε (h.val.1.child b right, h.val.2) side
      (producedChildWord allocation dilation x h b right) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => exact hx ⟨(.afterA ⟨parent, b, right⟩, phi), ht.symm⟩
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · dsimp only [producedChildWord]
        erw [dite_eq_left hp]
        exact afterB_mask_of_part_masks allocation dilation hε
          ⟨⟨parent, b, right⟩, hp⟩ phi side
          (fun i => x ⟨(.partC (⟨⟨parent, b, right⟩, hp⟩, i), phi), ht.symm⟩)
          (fun i => hx ⟨(.partC (⟨⟨parent, b, right⟩, hp⟩, i), phi), ht.symm⟩)
      · dsimp only [producedChildWord]
        erw [dite_eq_right hp]
        exact hx (⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩ : Produced K tick)
  | stageC parent => trivial

private theorem splitWord_eq_of_position (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (p : SplitPositions (K := K) (tick := tick) allocation dilation)
    (q : ProducedPositions (K := K) (tick := tick) allocation dilation)
    (hq : (producedPositionEquiv allocation dilation).symm p = q)
    (hlen : currentLength q.1.val.1 = activeHalfLength p.1) :
    splitWord allocation dilation x p =
      fun i => x q.1 q.2 (Fin.cast hlen.symm i) := by
  subst q
  rfl

theorem producedHalfWord_eq_childHalfWord (allocation : Allocation) (dilation : ℕ)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool) :
    producedHalfWord allocation dilation x h b right =
      childHalfWord allocation dilation h b right
        (producedChildWord allocation dilation x h b right) := by
  rcases h with ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA parent => rfl
  | stageB parent =>
      by_cases hp : positive (bShape (⟨parent, b, right⟩ : AfterB K)) = true
      · funext i
        let g : BPositive K := ⟨⟨parent, b, right⟩, hp⟩
        let part := bSubdivisionPositionEquiv allocation dilation g phi
          (halfPosition allocation dilation (.stageB parent, phi) b right i)
        let q : ProducedPositions (K := K) (tick := tick) allocation dilation :=
          ⟨⟨(.partC (g, part.1), phi), ht.symm⟩, part.2⟩
        have hq : (producedPositionEquiv allocation dilation).symm
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ = q := by
          simp only [producedPositionEquiv, Equiv.symm, Equiv.coe_fn_mk,
            splitToProduced, dite_eq_left hp]
          rfl
        dsimp only [producedHalfWord, producedChildWord]
        erw [dite_eq_left hp]
        exact splitWord_eq_of_position allocation dilation x
          ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ q hq rfl
      · funext i
        let q : ProducedPositions (K := K) (tick := tick) allocation dilation :=
          ⟨⟨(.afterB ⟨parent, b, right⟩, phi), ht.symm, hp⟩,
            halfPosition allocation dilation (.stageB parent, phi) b right i⟩
        have hq : (producedPositionEquiv allocation dilation).symm
            ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ = q := by
          simp only [producedPositionEquiv, Equiv.symm, Equiv.coe_fn_mk,
            splitToProduced, dite_eq_right hp]
          rfl
        dsimp only [producedHalfWord, producedChildWord]
        erw [dite_eq_right hp]
        exact splitWord_eq_of_position allocation dilation x
          ⟨⟨(.stageB parent, phi), ht⟩, b, right, i⟩ q hq rfl
  | stageC parent => rfl

theorem producedHalfWord_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (h.val.1.childLaw
        (halfShape h.val.1.parentShape (h.val.1.splitShape b) right)
        (h.val.2.symm side) a : ℝ)) (nativeChildWidth ε h)
      (h.val.1.statistic ∘ producedHalfWord allocation dilation x h b right) := by
  rw [producedHalfWord_eq_childHalfWord]
  exact childHalfWord_window allocation dilation hε side h b right _
    (producedChildWord_mask allocation dilation hε side x hx h b right) hp

theorem regroupBranch_window (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h))
    (h : Active K tick) (b : h.val.1.Branch) (right : Bool)
    (hp : 0 < branchPopulation allocation dilation h.val b) :
    typeWindow (fun a => (placedChildLawRat h.val (branchShape h.val b) side right a : ℝ))
      (nativeChildWidth ε h)
      (statistic h ∘ (if right then (regroupWords allocation dilation x).right
        (h, branchShape h.val b) else (regroupWords allocation dilation x).left
        (h, branchShape h.val b))) := by
  apply (Subdivision.typeWindow_reindex _ _ _ (branchClassEquiv allocation dilation h b)).mp
  have he : (statistic h ∘ (if right then (regroupWords allocation dilation x).right
      (h, branchShape h.val b) else (regroupWords allocation dilation x).left
      (h, branchShape h.val b))) ∘ branchClassEquiv allocation dilation h b =
        h.val.1.statistic ∘ producedHalfWord allocation dilation x h b right := by
    funext i
    have hi := regroupWords_branch allocation dilation x h b right i
    cases right <;> exact congrArg h.val.1.statistic hi
  rw [he]
  simpa only [placedChildLawRat_branchShape] using
    producedHalfWord_window allocation dilation hε side x hx h b right hp

theorem canonicalWindows_of_produced_masks (allocation : Allocation) (dilation : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (x : ProducedWords (K := K) (tick := tick) allocation dilation)
    (hx : ∀ h : Produced K tick, residentMask allocation dilation ε h.val side (x h)) :
    HistorySymmetry.childWindows
      (fun c : Active K tick × JointPopulation.Shape => statistic c.1)
      (fun c : Active K tick × JointPopulation.Shape => statistic c.1)
      (activeLaw (activeCounts allocation dilation) (fun c => leftLaw c.1 c.2 side))
      (activeLaw (activeCounts allocation dilation) (fun c => rightLaw c.1 c.2 side))
      (activeWidth (activeCounts allocation dilation) (fun c => nativeChildWidth ε c.1))
      (activeWidth (activeCounts allocation dilation) (fun c => nativeChildWidth ε c.1))
      (regroupWords allocation dilation x) := by
  rintro ⟨h, u⟩
  by_cases hp : 0 < activeCounts allocation dilation h u
  · obtain ⟨b, hb, hpos⟩ := shapeCounts_positive (branchShape h.val)
      (branchPopulation allocation dilation h.val) u hp
    subst u
    have hl := regroupBranch_window allocation dilation hε side x hx h b false hpos
    have hr := regroupBranch_window allocation dilation hε side x hx h b true hpos
    rw [activeLaw_of_pos (activeCounts allocation dilation)
      (fun c => leftLaw c.1 c.2 side) (h, branchShape h.val b) hp,
      activeLaw_of_pos (activeCounts allocation dilation)
      (fun c => rightLaw c.1 c.2 side) (h, branchShape h.val b) hp]
    dsimp only [leftLaw, rightLaw, childLaw, rightChildLaw, childLawRat, rightChildLawRat]
    simpa only [activeWidth, ite_eq_left hp, Bool.false_eq_true, ite_false, ite_true]
      using! And.intro hl hr
  · have hz : activeCounts allocation dilation h u = 0 := Nat.eq_zero_of_not_pos hp
    simp only [activeLaw, activeWidth, typeWindow, empiricalLaw,
      Fintype.card_fin, hz, Nat.cast_zero, div_zero, sub_zero, abs_zero,
      le_refl, implies_true, and_self, Nat.lt_irrefl, ite_false]

end MatrixMultiplication.AllFieldHistoryProducedMasks

end

end OAI
