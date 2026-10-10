import OAI.Analysis.IrrationalRotation.Rotation.FieldWeightedShiftPowers
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftHalfline

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem constantField_ae (A : Hilbert →L[ℂ] Hilbert) (f : Lp Hilbert 2 μ) :
    A.compLpL 2 μ f =ᵐ[μ] fun x => A (f x) := A.coeFn_compLp f

theorem constantField_mul (A B : Hilbert →L[ℂ] Hilbert) :
    (A * B).compLpL 2 μ = A.compLpL 2 μ * B.compLpL 2 μ := by
  ext f
  filter_upwards [constantField_ae (A*B) f, constantField_ae A (B.compLpL 2 μ f),
    constantField_ae B f] with x hab ha hb
  change ((A*B).compLpL 2 μ f) x = (A.compLpL 2 μ (B.compLpL 2 μ f)) x
  rw [hab, ha, hb]
  rfl

theorem constantField_one : (1 : Hilbert →L[ℂ] Hilbert).compLpL 2 μ = 1 := by
  ext f
  filter_upwards [constantField_ae (1 : Hilbert →L[ℂ] Hilbert) f] with x hx
  exact hx

theorem constantField_zero : (0 : Hilbert →L[ℂ] Hilbert).compLpL 2 μ = 0 := by
  ext f
  filter_upwards [constantField_ae (0 : Hilbert →L[ℂ] Hilbert) f,
    Lp.coeFn_zero Hilbert 2 μ] with x hx hz
  exact hx.trans hz.symm

theorem constantField_star (A : Hilbert →L[ℂ] Hilbert) :
    (star A).compLpL 2 μ = star (A.compLpL 2 μ) := by
  rw [ContinuousLinearMap.star_eq_adjoint (A.compLpL 2 μ)]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [constantField_ae (star A) f, constantField_ae A g] with x hf hg
  rw [hf, hg, ContinuousLinearMap.star_eq_adjoint]
  exact A.adjoint_inner_left (g x) (f x)

theorem constantField_injective [IsFiniteMeasure μ] [NeZero μ] :
    Function.Injective (fun A : Hilbert →L[ℂ] Hilbert => A.compLpL 2 μ) := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro ξ
  let f : Lp Hilbert 2 μ := Lp.const 2 μ ξ
  have he : ∀ᵐ x ∂μ, A ξ = B ξ := by
    filter_upwards [constantField_ae A f, constantField_ae B f, Lp.coeFn_const 2 μ ξ]
      with x ha hb hc
    change f x = ξ at hc
    have hab := congrArg (fun T : Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ => T f x) h
    rw [ha, hb, hc] at hab
    exact hab
  exact he.exists.choose_spec

theorem isStarProjection_fieldTailProjection (m : ℤ) :
    IsStarProjection (fieldTailProjection (μ := μ) m) := by
  constructor
  · change (tailProjection m).compLpL 2 μ * (tailProjection m).compLpL 2 μ = _
    rw [← constantField_mul, tailProjection_mul_self]
    rfl
  · change star ((tailProjection m).compLpL 2 μ) = _
    rw [← constantField_star, tailProjection_star]
    rfl

theorem fieldTailProjection_invariant
    (a : X → Weight) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) (m : ℤ) :
    (1 - fieldTailProjection m) * fieldOperator a C hC ha hm *
      fieldTailProjection m = 0 := by
  have hp : fieldTailProjection m * fieldOperator a C hC ha hm * fieldTailProjection m =
      fieldOperator a C hC ha hm * fieldTailProjection m := by
    ext f
    filter_upwards [constantField_ae (tailProjection m)
        (fieldOperator a C hC ha hm (fieldTailProjection m f)),
      fieldOperator_ae a C hC ha hm (fieldTailProjection m f),
      constantField_ae (tailProjection m) f] with x hp ht hq
    change (fieldTailProjection m (fieldOperator a C hC ha hm (fieldTailProjection m f))) x =
      (fieldOperator a C hC ha hm (fieldTailProjection m f)) x
    simp only [fieldTailProjection] at hp ht hq ⊢
    rw [hp, ht, hq]
    have h := tailProjection_invariant (a x) m
    rw [sub_mul, one_mul, sub_mul] at h
    exact congrArg (fun T : Hilbert →L[ℂ] Hilbert => T (f x)) (sub_eq_zero.mp h).symm
  rw [sub_mul, one_mul, sub_mul, hp, sub_self]

theorem fieldTailProjection_ne_zero [IsFiniteMeasure μ] [NeZero μ] (m : ℤ) :
    fieldTailProjection (μ := μ) m ≠ 0 := by
  intro h
  apply tailProjection_ne_zero m
  apply constantField_injective (μ := μ)
  simpa [fieldTailProjection, constantField_zero] using h

theorem fieldTailProjection_ne_one [IsFiniteMeasure μ] [NeZero μ] (m : ℤ) :
    fieldTailProjection (μ := μ) m ≠ 1 := by
  intro h
  apply tailProjection_ne_one m
  apply constantField_injective (μ := μ)
  simpa [fieldTailProjection, constantField_one] using h

theorem fieldTailProjection_not_covariant [IsFiniteMeasure μ] [NeZero μ] (m : ℤ) :
    (shift (-1)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
      fieldTailProjection m * (shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ≠
        fieldTailProjection m := by
  intro h
  apply tailProjection_not_covariant m
  apply constantField_injective (μ := μ)
  simpa only [constantField_mul, fieldTailProjection] using h

theorem exists_ordinary_invariant_projection [IsFiniteMeasure μ] [NeZero μ]
    (a : X → Weight) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    ∃ p : Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ,
      IsStarProjection p ∧ p ≠ 0 ∧ p ≠ 1 ∧
      (1-p) * fieldOperator a C hC ha hm * p = 0 ∧
      (shift (-1)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ * p *
        (shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ≠ p :=
  ⟨fieldTailProjection 0, isStarProjection_fieldTailProjection 0,
    fieldTailProjection_ne_zero 0, fieldTailProjection_ne_one 0,
    fieldTailProjection_invariant a C hC ha hm 0,
    fieldTailProjection_not_covariant 0⟩

end Invariant233.WeightedShift

end

end OAI
