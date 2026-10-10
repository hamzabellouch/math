import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateData
import OAI.Analysis.CircleDomains.Rigidity.BoundaryTrace
import OAI.Analysis.CircleDomains.Topology.AssignedCollarExclusion

namespace OAI

/-! A countable selected family uses only countably many nonzero bands.
Restricting to these marks preserves the actual graph, physical function
and masks; every discarded marked fiber is already a singleton. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateData.countable_band_support
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) :
    {s | C.upper s - C.lower s ≠ 0}.Countable :=
  CircleDomainRigidity.countable_band_support C.width_summable

 def MaskedCoordinateData.restrictMarks
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (A : Set S) (hsing : C.singular ∈ A)
    (hsupport : ∀ s, C.upper s - C.lower s ≠ 0 → s ∈ A) :
    MaskedCoordinateData G U π (fun s : A => σ s.val) where
  graph := C.graph
  graph_closed := C.graph_closed
  mask := C.mask
  mask_closed := C.mask_closed
  mask_frontier := C.mask_frontier
  singular := ⟨C.singular, hsing⟩
  Index := C.Index
  patch := C.patch
  patch_open := C.patch_open
  cover := C.cover
  branch := C.branch
  bound := C.bound
  branch_bounded := C.branch_bounded
  physical := C.physical
  measurable := C.measurable
  gradient_measurable := C.gradient_measurable
  smooth := C.smooth
  energy := C.energy
  physical_graph := C.physical_graph
  branch_smooth := C.branch_smooth
  branch_projection := C.branch_projection
  lower := fun s => C.lower s.val
  upper := fun s => C.upper s.val
  width_nonneg := fun s => C.width_nonneg s
  width_summable := C.width_summable.subtype (· ∈ A)
  marked_fiber := fun s => C.marked_fiber s
  marked_branch := fun s => C.marked_branch s
  free_fiber := by
    intro x hx hxrange
    by_cases hxo : x ∈ range σ
    · obtain ⟨s, rfl⟩ := hxo
      have hsA : s ∉ A := by
        intro hs
        exact hxrange ⟨⟨s, hs⟩, rfl⟩
      have hz : C.upper s - C.lower s = 0 := by
        by_contra h
        exact hsA (hsupport s h)
      have hband := C.marked_fiber s
      rw [sub_eq_zero.mp hz, Icc_self, image_singleton] at hband
      intro a ha b hb
      exact (mem_singleton_iff.mp (hband ha)).trans (mem_singleton_iff.mp (hband hb)).symm
    · exact C.free_fiber x hx hxo

 theorem MaskedCoordinateData.restrictMarks_sourceStokesBudget_le
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : MaskedCoordinateData G U π σ) (A : Set S) (hsing : C.singular ∈ A)
    (hsupport : ∀ s, C.upper s - C.lower s ≠ 0 → s ∈ A)
    {R : ℝ} (hR : 0 ≤ R) :
    (C.restrictMarks A hsing hsupport).sourceStokesBudget R ≤ C.sourceStokesBudget R := by
  let D := C.restrictMarks A hsing hsupport
  let e : {t : A // t ≠ D.singular} → {s : S // s ≠ C.singular} :=
    fun t => ⟨t.val.val, fun h => t.property (Subtype.ext h)⟩
  have he : Injective e := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun s : {s : S // s ≠ C.singular} => s.val) h
  have hs : (∑' t : {t : A // t ≠ D.singular}, (D.upper t - D.lower t) ^ 2) ≤
      ∑' s : {s : S // s ≠ C.singular}, (C.upper s - C.lower s) ^ 2 := by
    exact (D.width_summable.subtype (· ≠ D.singular)).tsum_le_tsum_of_inj e he
      (fun _ _ => sq_nonneg _) (fun _ => le_rfl)
      (C.width_summable.subtype (· ≠ C.singular))
  unfold sourceStokesBudget
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs)
  positivity

 theorem exists_common_countable_coordinate_marks
    {I S : Type*} [Countable I] {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (C : I → MaskedCoordinateData G U π σ) (B : Set S) (hB : B.Countable) :
    ∃ A : Set S, A.Countable ∧ B ⊆ A ∧
      (∀ i, (C i).singular ∈ A) ∧
      ∀ i s, (C i).upper s - (C i).lower s ≠ 0 → s ∈ A := by
  let A := B ∪ range (fun i => (C i).singular) ∪ ⋃ i, {s | (C i).upper s - (C i).lower s ≠ 0}
  refine ⟨A, (hB.union (countable_range _)).union
    (countable_iUnion fun i => (C i).countable_band_support), ?_, ?_, ?_⟩
  · intro s hs
    exact Or.inl (Or.inl hs)
  · intro i
    exact Or.inl (Or.inr (mem_range_self i))
  · intro i s hs
    exact Or.inr (mem_iUnion.mpr ⟨i, hs⟩)

 def RealCoordinateSubfamily.restrictMarks
    {L J S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : L → MaskedCoordinateData G U π σ} {ι : J → L}
    (R : RealCoordinateSubfamily C ι) (A : Set S)
    (hsing : ∀ l, (C l).singular ∈ A)
    (hsupport : ∀ l s, (C l).upper s - (C l).lower s ≠ 0 → s ∈ A) :
    RealCoordinateSubfamily (fun l => (C l).restrictMarks A (hsing l) (hsupport l)) ι where
  physical := R.physical
  quotient := R.quotient
  bound := R.bound
  bounded := R.bounded
  full_mask := R.full_mask
  smooth := R.smooth
  energy := R.energy
  pullback := R.pullback
  projection := R.projection
  width := fun j s => R.width j s.val

end CircleDomainRigidity.FiniteTransfer

end

end OAI
