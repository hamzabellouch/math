import OAI.Analysis.IrrationalRotation.Model.TailSubspace
import OAI.Analysis.IrrationalRotation.Rotation.FieldWeightedShiftHalfline
import OAI.Analysis.IrrationalRotation.Product.ProductHilbert
import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.WeightedShift

theorem tailProjection_isStarProjection (m : ℤ) :
    IsStarProjection (tailProjection m) := isStarProjection_tailProjection m

@[simp] theorem tailProjection_single (m k : ℤ) (z : ℂ) :
    tailProjection m (lp.single 2 k z) =
      if m ≤ k then lp.single 2 k z else 0 := by
  ext j
  by_cases hj : j = k
  · subst j
    by_cases hk : m ≤ k <;> simp [tailProjection_apply, hk]
  · by_cases hk : m ≤ k <;> simp [tailProjection_apply, lp.single_apply, hj, hk]

theorem tailProjection_range_eq_closedSpan (m : ℤ) :
    (tailProjection m).range =
      (Submodule.span ℂ ((fun k : ℤ => (lp.single 2 k (1 : ℂ) : Hilbert)) ''
        Set.Ici m)).topologicalClosure := by
  classical
  let b : HilbertBasis ℤ ℂ Hilbert := default
  have hb (k : ℤ) : b k = (lp.single 2 k (1 : ℂ) : Hilbert) :=
    (HilbertBasis.repr_symm_single b k).symm
  apply le_antisymm
  · rintro ξ ⟨η, rfl⟩
    refine mem_closure_of_tendsto ((tailProjection m).hasSum (b.hasSum_repr η))
      (Eventually.of_forall ?_)
    intro s
    apply Submodule.sum_mem
    intro k hk
    rw [map_smul, hb, tailProjection_single]
    by_cases hmk : m ≤ k
    · rw [ite_eq_left hmk]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hmk, rfl⟩)
    · rw [ite_eq_right hmk, smul_zero]
      exact Submodule.zero_mem _
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro ξ ⟨k, hk, rfl⟩
      change m ≤ k at hk
      refine ⟨lp.single 2 k (1 : ℂ), ?_⟩
      change tailProjection m (lp.single 2 k (1 : ℂ)) = lp.single 2 k (1 : ℂ)
      simp only [tailProjection_single, ite_eq_left hk]
    · exact ContinuousLinearMap.IsIdempotentElem.isClosed_range
        (isStarProjection_tailProjection m).isIdempotentElem

theorem mem_range_tailProjection_iff (m : ℤ) (ξ : Hilbert) :
    ξ ∈ (tailProjection m).range ↔ ∀ k : ℤ, k < m → ξ k = 0 := by
  constructor
  · rintro ⟨η, rfl⟩ k hk
    change tailProjection m η k = 0
    simp only [tailProjection_apply, ite_eq_right (not_le.mpr hk)]
  · intro hξ
    refine ⟨ξ, ?_⟩
    ext k
    change tailProjection m ξ k = ξ k
    rw [tailProjection_apply]
    split_ifs with hk
    · rfl
    · exact (hξ k (lt_of_not_ge hk)).symm

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldTailProjection_ae (m : ℤ) (ξ : Lp Hilbert 2 μ) :
    fieldTailProjection (μ := μ) m ξ =ᵐ[μ] fun x => tailProjection m (ξ x) :=
  constantField_ae (tailProjection m) ξ

theorem fieldTailProjection_coordinates_ae (m : ℤ) (ξ : Lp Hilbert 2 μ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      fieldTailProjection (μ := μ) m ξ x k = if m ≤ k then ξ x k else 0 := by
  filter_upwards [fieldTailProjection_ae m ξ] with x hx k
  rw [hx, tailProjection_apply]

theorem fieldTailProjection_isStarProjection (m : ℤ) :
    IsStarProjection (fieldTailProjection (μ := μ) m) :=
  isStarProjection_fieldTailProjection m

theorem fieldTailSubspace_isClosed (m : ℤ) :
    IsClosed (fieldTailSubspace μ m : Set (Lp Hilbert 2 μ)) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (fieldTailProjection_isStarProjection (μ := μ) m).isIdempotentElem

theorem mem_fieldTailSubspace_iff (m : ℤ) (ξ : Lp Hilbert 2 μ) :
    ξ ∈ fieldTailSubspace μ m ↔ ∀ᵐ x ∂μ, ∀ k : ℤ, k < m → ξ x k = 0 := by
  constructor
  · rintro ⟨η, rfl⟩
    filter_upwards [fieldTailProjection_coordinates_ae m η] with x hx k hk
    change fieldTailProjection (μ := μ) m η x k = 0
    rw [hx k, ite_eq_right (not_le.mpr hk)]
  · intro hξ
    refine ⟨ξ, ?_⟩
    apply Lp.ext
    filter_upwards [fieldTailProjection_coordinates_ae m ξ, hξ] with x hx hz
    apply lp.ext
    funext k
    change fieldTailProjection (μ := μ) m ξ x k = ξ x k
    rw [hx k]
    split_ifs with hk
    · rfl
    · exact (hz k (lt_of_not_ge hk)).symm

theorem mem_fieldTailSubspace_iff_closedSpan (m : ℤ) (ξ : Lp Hilbert 2 μ) :
    ξ ∈ fieldTailSubspace μ m ↔ ∀ᵐ x ∂μ,
      ξ x ∈ (Submodule.span ℂ
        ((fun k : ℤ => (lp.single 2 k (1 : ℂ) : Hilbert)) '' Set.Ici m)).topologicalClosure := by
  rw [mem_fieldTailSubspace_iff]
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall (fun x => by
    rw [← tailProjection_range_eq_closedSpan, mem_range_tailProjection_iff])

theorem fieldTailSubspace_invariant
    (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) (m : ℤ) :
    fieldTailSubspace μ m ∈ Module.End.invtSubmodule
      ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
        fieldDiagonal a C hC ha hm) := by
  apply (ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule_iff
    (fieldTailProjection_isStarProjection (μ := μ) m).isIdempotentElem).mpr
  have h := fieldTailProjection_invariant a C hC ha hm m
  rw [sub_mul, one_mul, sub_mul] at h
  exact (sub_eq_zero.mp h).symm

section Probability
variable [IsProbabilityMeasure μ]

theorem fieldTailProjection_const (m : ℤ) (ξ : Hilbert) :
    fieldTailProjection (μ := μ) m (Lp.const 2 μ ξ) =
      Lp.const 2 μ (tailProjection m ξ) := by
  apply Lp.ext
  filter_upwards [fieldTailProjection_ae m (Lp.const 2 μ ξ),
    Lp.coeFn_const (p := (2 : ENNReal)) (μ := μ) (c := ξ),
    Lp.coeFn_const (p := (2 : ENNReal)) (μ := μ) (c := tailProjection m ξ)]
    with x hP hξ htail
  rw [hP, hξ, htail]
  rfl

theorem const_single_ne_zero (k : ℤ) :
    (Lp.const 2 μ (lp.single 2 k (1 : ℂ)) : Lp Hilbert 2 μ) ≠ 0 := by
  intro h
  have hn : ‖(Lp.const 2 μ (lp.single 2 k (1 : ℂ)) : Lp Hilbert 2 μ)‖ = 1 := by
    rw [Lp.norm_const' 2 μ _ (by norm_num) (by norm_num)]
    simp [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem fieldTailSubspace_ne_bot (m : ℤ) : fieldTailSubspace μ m ≠ ⊥ := by
  intro h
  apply fieldTailProjection_ne_zero (μ := μ) m
  apply ContinuousLinearMap.ext
  intro ξ
  have hm : fieldTailProjection (μ := μ) m ξ ∈ fieldTailSubspace μ m := ⟨ξ, rfl⟩
  rw [h] at hm
  exact hm

theorem fieldTailSubspace_ne_top (m : ℤ) : fieldTailSubspace μ m ≠ ⊤ := by
  intro h
  apply fieldTailProjection_ne_one (μ := μ) m
  apply ContinuousLinearMap.ext
  intro ξ
  have hm : ξ ∈ fieldTailSubspace μ m := by rw [h]; trivial
  rcases hm with ⟨η, rfl⟩
  exact congrArg (fun A : Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ => A η)
    (fieldTailProjection_isStarProjection (μ := μ) m).isIdempotentElem.eq

end Probability

end Invariant233.WeightedShift

namespace Invariant233.Rotation

theorem ordinary_tail_subspace (θ : ℝ) (f : C(Circle, ℝ)) (m : ℤ) :
    IsClosed (WeightedShift.fieldTailSubspace circleMeasure m : Set Hilbert) ∧
      WeightedShift.fieldTailSubspace circleMeasure m ≠ ⊥ ∧
      WeightedShift.fieldTailSubspace circleMeasure m ≠ ⊤ ∧
      WeightedShift.fieldTailSubspace circleMeasure m ∈
        Module.End.invtSubmodule (weightedReal θ f) :=
  ⟨WeightedShift.fieldTailSubspace_isClosed m,
    WeightedShift.fieldTailSubspace_ne_bot m,
    WeightedShift.fieldTailSubspace_ne_top m,
    WeightedShift.fieldTailSubspace_invariant _ _ _ _ _ m⟩

end Invariant233.Rotation

namespace Invariant233.ProductModel

theorem ordinary_tail_subspace (θ c : ℕ → ℝ) (m : ℤ) :
    IsClosed (WeightedShift.fieldTailSubspace baseMeasure m : Set Hilbert) ∧
      WeightedShift.fieldTailSubspace baseMeasure m ≠ ⊥ ∧
      WeightedShift.fieldTailSubspace baseMeasure m ≠ ⊤ ∧
      WeightedShift.fieldTailSubspace baseMeasure m ∈
        Module.End.invtSubmodule (weightedOperator θ c) :=
  ⟨WeightedShift.fieldTailSubspace_isClosed m,
    WeightedShift.fieldTailSubspace_ne_bot m,
    WeightedShift.fieldTailSubspace_ne_top m,
    WeightedShift.fieldTailSubspace_invariant _ _ _ _ _ m⟩

end Invariant233.ProductModel

end

end OAI
