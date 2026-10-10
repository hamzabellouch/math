import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateConeTraceSeparation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarConeKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOffsetThreshold

namespace OAI

/-! # The finite family of polar quotients that detects one root offset -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]

/-- One ray, and the two-ray cones independent of that ray. This is precisely
the finite family needed for a single neighboring root step. -/
def rootOffsetConeIndex (D : SupportDatum W I B) (j : I) :=
  Option {k : I // LinearIndependent ℝ
    ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]}

instance (D : SupportDatum W I B) (j : I) : Finite (rootOffsetConeIndex D j) := by
  unfold rootOffsetConeIndex
  infer_instance

instance (D : SupportDatum W I B) (j : I) : Nonempty (rootOffsetConeIndex D j) := ⟨none⟩

/-- The source polar cone attached to one member of the finite family. -/
def rootOffsetCone (D : SupportDatum W I B) (hne : ∀ i, D.weight i ≠ 0) (j : I) :
    rootOffsetConeIndex D j → ProperCone ℝ (StrongDual ℝ W)
  | none => closedWeightRay (D.weight j).toContinuousLinearMap (by simpa using hne j)
  | some k => closedTwoWeightCone (D.weight j).toContinuousLinearMap
      (D.weight k.val).toContinuousLinearMap k.property

theorem rootOffsetCone_salient (D : SupportDatum W I B) (hne : ∀ i, D.weight i ≠ 0)
    (j : I) (s : rootOffsetConeIndex D j) :
    (rootOffsetCone D hne j s : ConvexCone ℝ (StrongDual ℝ W)).Salient := by
  cases s with
  | none => exact closedWeightRay_salient (by simpa using hne j)
  | some k => exact closedTwoWeightCone_salient _ _ k.property

theorem weight_mem_rootOffsetCone (D : SupportDatum W I B) (hne : ∀ i, D.weight i ≠ 0)
    (j : I) (s : rootOffsetConeIndex D j) :
    (D.weight j).toContinuousLinearMap ∈ rootOffsetCone D hne j s := by
  cases s with
  | none =>
      exact (mem_closedWeightRay (by simpa using hne j) _).mpr
        ⟨1, zero_le_one, by simp⟩
  | some k =>
      exact (mem_closedTwoWeightCone _ _ k.property _).mpr
        ⟨1, 0, zero_le_one, le_rfl, by simp⟩

variable [Nonempty B]

/-- Source enlargement and bridge error can be fixed before the affine
label is selected, simultaneously for all quotients used by this root. -/
theorem exists_uniform_rootOffsetCone_threshold
    (D : SupportDatum W I B) (j : I)
    (target : templateSymmetryGroup D → rootOffsetConeIndex D j → ℝ)
    (htarget : ∀ A s, 0 < target A s)
    {source A B Λ c : ℝ} (hsource : 0 < source)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hΛ : 0 ≤ Λ) (hc : 0 ≤ c) :
    ∃ δ₀ ε : ℝ, 0 < δ₀ ∧ 0 < ε ∧ δ₀ ≤ source ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → c * δ ≤ 1 ∧
        ∀ L s, Λ * (A * δ + B * ε) ≤ target L s := by
  let index := templateSymmetryGroup D × rootOffsetConeIndex D j
  have hi : Nonempty index := ⟨(1, none)⟩
  let : Nonempty index := hi
  obtain ⟨δ₀, ε, hd, he, hds, hbound⟩ :=
    exists_uniform_source_offset_threshold (I := index)
      (fun p => target p.1 p.2) hA hB hΛ hc
      (fun p => htarget p.1 p.2) hsource
  refine ⟨δ₀, ε, hd, he, hds, ?_⟩
  intro δ hδ hδ₀
  exact ⟨(hbound (1, none) δ hδ hδ₀).1,
    fun L s => (hbound (L, s) δ hδ hδ₀).2⟩

/-- Forward and reverse volume inequalities for this finite family force
the two offsets to coincide. Each inequality uses its own actual quotient
trace, with positive multiplicity exactly on the transformed cone. -/
theorem eq_of_rootOffsetCone_trace_inequalities
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (hne : ∀ i, D.weight i ≠ 0) (j : I)
    (c : rootOffsetConeIndex D j → I → ℕ)
    (hout : ∀ s i, (D.weight i).toContinuousLinearMap ∉
      transformedPolarCone (rootOffsetCone D hne j s) A.val → c s i = 0)
    (hin : ∀ s i, (D.weight i).toContinuousLinearMap ∈
      transformedPolarCone (rootOffsetCone D hne j s) A.val → 0 < c s i)
    (x y : W)
    (hf : ∀ s, (∑ i, (c s i : ℝ) • (D.weight i).toContinuousLinearMap) (y - x) ≤ 0)
    (hr : ∀ s, (∑ i, (c s i : ℝ) • (D.weight i).toContinuousLinearMap) (x - y) ≤ 0) :
    x = y := by
  classical
  let cTwo : I → I → ℕ := fun k =>
    if h : LinearIndependent ℝ
        ![(D.weight j).toContinuousLinearMap, (D.weight k).toContinuousLinearMap]
    then c (some ⟨k, h⟩) else 0
  apply eq_of_transformed_pure_word_trace_inequalities D A hne j (c none) cTwo
    (hout none) (hin none) ?_ ?_ x y (hf none) (hr none) ?_ ?_
  · intro k hk i hi
    simpa only [cTwo, dite_eq_left hk] using hout (some ⟨k, hk⟩) i hi
  · intro k hk i hi
    simpa only [cTwo, dite_eq_left hk] using hin (some ⟨k, hk⟩) i hi
  · intro k hk
    simpa only [cTwo, dite_eq_left hk] using hf (some ⟨k, hk⟩)
  · intro k hk
    simpa only [cTwo, dite_eq_left hk] using hr (some ⟨k, hk⟩)

end PolycyclicRecognition

end

end OAI
