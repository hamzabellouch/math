import OAI.Analysis.KadisonSimilarity.Representation.DiagonalFieldAction

namespace OAI

/-! # Algebraic laws for fields of diagonal-commuting operators

The fields are constructed from the actual operators. Their algebraic laws
hold almost everywhere, by the pointwise action on all L² vectors and a
countable dense family of constant columns.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Extending by the zero operator outside the conull reconstruction set
produces a field on the original measure space. -/
theorem exists_global_diagonal_field
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) :
    ∃ field : Ω → H →L[ℂ] H, (∀ a, ‖field a‖ ≤ ‖T‖) ∧
      ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = field a (f a) := by
  classical
  obtain ⟨s, hsm, hsnull, R, hnorm, haction⟩ :=
    exists_conull_diagonal_field_action μ T hT
  let field : Ω → H →L[ℂ] H := fun a => if ha : a ∈ s then R ⟨a, ha⟩ else 0
  refine ⟨field, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ s
    · simpa only [field, dite_eq_left ha] using hnorm ⟨a, ha⟩
    · simpa only [field, dite_eq_right ha, norm_zero] using norm_nonneg T
  · intro f
    have hr : ∀ᵐ a ∂μ.restrict s, T f a = field a (f a) := by
      apply (ae_restrict_iff_subtype hsm).mpr
      filter_upwards [haction f] with a ha
      simpa only [field, dite_eq_left a.property] using ha
    have hs : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hsnull
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha

/-- A chosen genuine field for an operator in the diagonal commutant. -/
def diagonalField
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) : Ω → H →L[ℂ] H :=
  Classical.choose (exists_global_diagonal_field μ T hT)

theorem diagonalField_norm
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) (a : Ω) :
    ‖diagonalField μ T hT a‖ ≤ ‖T‖ :=
  (Classical.choose_spec (exists_global_diagonal_field μ T hT)).1 a

theorem diagonalField_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) (f : Lp H 2 μ) :
    ∀ᵐ a ∂μ, T f a = diagonalField μ T hT a (f a) :=
  (Classical.choose_spec (exists_global_diagonal_field μ T hT)).2 f

omit [IsFiniteMeasure μ] [CompleteSpace H] in
/-- Countably many dense test vectors suffice for equality of operator
fields almost everywhere. -/
theorem ae_operator_eq_of_forall_vectors
    (R S : Ω → H →L[ℂ] H)
    (h : ∀ x : H, ∀ᵐ a ∂μ, R a x = S a x) : ∀ᵐ a ∂μ, R a = S a := by
  have hall : ∀ᵐ a ∂μ, ∀ n : ℕ,
      R a (TopologicalSpace.denseSeq H n) = S a (TopologicalSpace.denseSeq H n) :=
    eventually_countable_forall.mpr fun n => h (TopologicalSpace.denseSeq H n)
  filter_upwards [hall] with a ha
  apply DFunLike.coe_injective
  exact (TopologicalSpace.denseRange_denseSeq H).equalizer
    (R a).continuous (S a).continuous (funext ha)

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- The all-vector action supplies the constant-column formula. -/
theorem pointwise_action_column
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a)) (x : H) :
    ∀ᵐ a ∂μ, T (Lp.const 2 μ x) a = R a x := by
  filter_upwards [hR (Lp.const 2 μ x), Lp.coeFn_const 2 μ x] with a ha hc
  simpa only [hc, Function.const_apply] using ha

omit [CompleteSpace H] in
/-- Zero is preserved by any field realizing its pointwise action. -/
theorem pointwise_field_zero (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (0 : Lp H 2 μ →L[ℂ] Lp H 2 μ) f a = R a (f a)) :
    ∀ᵐ a ∂μ, R a = 0 := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ 0 R hR x, Lp.coeFn_zero H 2 μ] with a ha hz
  simpa only [zero_apply, hz, Pi.zero_apply] using ha.symm

omit [CompleteSpace H] in
/-- The identity is preserved almost everywhere. -/
theorem pointwise_field_one (R : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (1 : Lp H 2 μ →L[ℂ] Lp H 2 μ) f a = R a (f a)) :
    ∀ᵐ a ∂μ, R a = 1 := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ 1 R hR x, Lp.coeFn_const 2 μ x] with a ha hc
  simpa only [one_apply_eq_self, hc, Function.const_apply] using ha.symm

omit [CompleteSpace H] in
/-- Addition of L² operators becomes addition of their fields. -/
theorem pointwise_field_add
    (T S : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R Q U : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hQ : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hU : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (T + S) f a = U a (f a)) :
    ∀ᵐ a ∂μ, U a = R a + Q a := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ T R hR x,
    pointwise_action_column μ S Q hQ x, pointwise_action_column μ (T + S) U hU x,
    Lp.coeFn_add (T (Lp.const 2 μ x)) (S (Lp.const 2 μ x))] with a hr hq hu hadd
  simpa only [add_apply, hadd, Pi.add_apply, hr, hq] using hu.symm

omit [CompleteSpace H] in
/-- Composition uses the all-L² action on the inner operator's column. -/
theorem pointwise_field_mul
    (T S : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R Q U : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hQ : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, S f a = Q a (f a))
    (hU : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (T * S) f a = U a (f a)) :
    ∀ᵐ a ∂μ, U a = R a * Q a := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [hR (S (Lp.const 2 μ x)), pointwise_action_column μ S Q hQ x,
    pointwise_action_column μ (T * S) U hU x] with a hr hq hu
  simpa only [mul_apply_eq_comp, hr, hq] using hu.symm

omit [CompleteSpace H] in
/-- Complex scalar multiplication, in particular multiplication by `i`,
is inherited from the actual L² operators. -/
theorem pointwise_field_smul
    (c : ℂ) (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (R U : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hU : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (c • T) f a = U a (f a)) :
    ∀ᵐ a ∂μ, U a = c • R a := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  filter_upwards [pointwise_action_column μ T R hR x,
    pointwise_action_column μ (c • T) U hU x,
    Lp.coeFn_smul c (T (Lp.const 2 μ x))] with a hr hu hsmul
  simpa only [smul_apply, hsmul, Pi.smul_apply, hr] using hu.symm

end KadisonSimilarity

end

end OAI
