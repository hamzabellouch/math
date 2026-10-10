import OAI.Analysis.KadisonSimilarity.Representation.DiagonalFieldAlgebra
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

/-! # Adjoint compatibility of the actual diagonal field

Localized inner products recover the adjoint identity almost everywhere.
Together with the algebraic laws, this supplies the raw AE relations needed
for the conull fiber-representation construction.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A measurable localization is symmetric for the L² inner product. -/
theorem l2Localization_inner (s : Set Ω) (hs : MeasurableSet s)
    (f g : Lp H 2 μ) :
    inner ℂ (l2Localization μ s hs f) g = inner ℂ f (l2Localization μ s hs g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Localization_ae μ s hs f, l2Localization_ae μ s hs g]
    with a hf hg
  rw [hf, hg]
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
  · simp only [Set.indicator_of_notMem ha, inner_zero_left, inner_zero_right]

omit [CompleteSpace H] in
/-- The right-indicator version of the standard L² set-integral formula. -/
theorem inner_indicatorConstLp_right (f : Lp H 2 μ)
    (s : Set Ω) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (y : H) :
    inner ℂ f (indicatorConstLp 2 hs hμs y) = ∫ a in s, inner ℂ (f a) y ∂μ := by
  rw [L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := y)]
    with a ha
  rw [ha]
  by_cases h : a ∈ s
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h, inner_zero_right]

variable [IsFiniteMeasure μ]

/-- Equality of all localized inner products identifies adjoint constant
columns almost everywhere. -/
theorem diagonal_adjoint_columns
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) (x y : H) :
    ∀ᵐ a ∂μ, inner ℂ x (T (Lp.const 2 μ y) a) =
      inner ℂ ((star T) (Lp.const 2 μ x) a) y := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact (integrableOn_Lp_of_measure_ne_top (T (Lp.const 2 μ y))
      fact_one_le_two_ennreal.elim hμs.ne).const_inner x
  · intro s _ hμs
    exact (integrableOn_Lp_of_measure_ne_top ((star T) (Lp.const 2 μ x))
      fact_one_le_two_ennreal.elim hμs.ne).inner_const y
  · intro s hs hμs
    have hcomm := congrArg (fun A : Lp H 2 μ →L[ℂ] Lp H 2 μ => A (Lp.const 2 μ y))
      (hT s hs)
    change T (l2Localization μ s hs (Lp.const 2 μ y)) =
      l2Localization μ s hs (T (Lp.const 2 μ y)) at hcomm
    calc
      (∫ a in s, inner ℂ x (T (Lp.const 2 μ y) a) ∂μ) =
          inner ℂ (indicatorConstLp 2 hs hμs.ne x) (T (Lp.const 2 μ y)) :=
        (L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ _ hs x hμs.ne).symm
      _ = inner ℂ (l2Localization μ s hs (Lp.const 2 μ x)) (T (Lp.const 2 μ y)) := by
        rw [l2Localization_const]
      _ = inner ℂ (Lp.const 2 μ x) (l2Localization μ s hs (T (Lp.const 2 μ y))) :=
        l2Localization_inner μ s hs _ _
      _ = inner ℂ (Lp.const 2 μ x) (T (l2Localization μ s hs (Lp.const 2 μ y))) := by
        rw [hcomm]
      _ = inner ℂ ((star T) (Lp.const 2 μ x)) (l2Localization μ s hs (Lp.const 2 μ y)) :=
        (ContinuousLinearMap.adjoint_inner_left T _ _).symm
      _ = inner ℂ ((star T) (Lp.const 2 μ x)) (indicatorConstLp 2 hs hμs.ne y) := by
        rw [l2Localization_const]
      _ = ∫ a in s, inner ℂ ((star T) (Lp.const 2 μ x) a) y ∂μ :=
        inner_indicatorConstLp_right μ _ s hs hμs.ne y

variable [TopologicalSpace.SeparableSpace H]

/-- Adjoint compatibility follows from the original operator's localized
inner products, rather than being postulated as a field relation. -/
theorem pointwise_field_star
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T)
    (R Q : Ω → H →L[ℂ] H)
    (hR : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a))
    (hQ : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, (star T) f a = Q a (f a)) :
    ∀ᵐ a ∂μ, Q a = star (R a) := by
  apply ae_operator_eq_of_forall_vectors
  intro x
  have hpair (y : H) : ∀ᵐ a ∂μ, inner ℂ (Q a x) y = inner ℂ x (R a y) := by
    filter_upwards [diagonal_adjoint_columns μ T hT x y,
      pointwise_action_column μ T R hR y,
      pointwise_action_column μ (star T) Q hQ x] with a ha hr hq
    rw [hr, hq] at ha
    exact ha.symm
  have hall : ∀ᵐ a ∂μ, ∀ n : ℕ,
      inner ℂ (Q a x) (TopologicalSpace.denseSeq H n) =
        inner ℂ x (R a (TopologicalSpace.denseSeq H n)) :=
    eventually_countable_forall.mpr fun n => hpair (TopologicalSpace.denseSeq H n)
  filter_upwards [hall] with a ha
  apply ext_inner_right ℂ
  intro y
  have heq : (fun z => inner ℂ (Q a x) z) = (fun z => inner ℂ x (R a z)) :=
    (TopologicalSpace.denseRange_denseSeq H).equalizer
      (by fun_prop) (by fun_prop) (funext ha)
  rw [congrFun heq y]
  exact (ContinuousLinearMap.adjoint_inner_left (R a) y x).symm

/-- A star subalgebra of the diagonal commutant has actual bounded fields
whose raw algebraic relations all hold almost everywhere. Each fixed
operator also has its full pointwise L²-action formula. -/
theorem exists_diagonal_subalgebra_fields
    (P : StarSubalgebra ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hP : ∀ (T : P) (r : Set Ω) (hr : MeasurableSet r),
      (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) * l2Localization μ r hr =
        l2Localization μ r hr * (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)) :
    ∃ field : P → Ω → H →L[ℂ] H,
      (∀ T a, ‖field T a‖ ≤ ‖T‖) ∧
      (∀ (T : P) (f : Lp H 2 μ), ∀ᵐ a ∂μ, T.val f a = field T a (f a)) ∧
      (∀ᵐ a ∂μ, field 0 a = 0) ∧
      (∀ᵐ a ∂μ, field 1 a = 1) ∧
      (∀ T S : P, ∀ᵐ a ∂μ, field (T + S) a = field T a + field S a) ∧
      (∀ T S : P, ∀ᵐ a ∂μ, field (T * S) a = field T a * field S a) ∧
      (∀ (c : ℂ) (T : P), ∀ᵐ a ∂μ, field (c • T) a = c • field T a) ∧
      (∀ T : P, ∀ᵐ a ∂μ, field (star T) a = star (field T a)) := by
  let field : P → Ω → H →L[ℂ] H := fun T => diagonalField μ T.val (hP T)
  have hnorm (T : P) (a : Ω) : ‖field T a‖ ≤ ‖T‖ := diagonalField_norm μ _ (hP T) a
  have hact (T : P) (f : Lp H 2 μ) : ∀ᵐ a ∂μ, T.val f a = field T a (f a) :=
    diagonalField_action μ _ (hP T) f
  refine ⟨field, hnorm, hact, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pointwise_field_zero μ _ (hact 0)
  · exact pointwise_field_one μ _ (hact 1)
  · intro T S
    exact pointwise_field_add μ T.val S.val _ _ _ (hact T) (hact S) (hact (T + S))
  · intro T S
    exact pointwise_field_mul μ T.val S.val _ _ _ (hact T) (hact S) (hact (T * S))
  · intro c T
    exact pointwise_field_smul μ c T.val _ _ (hact T) (hact (c • T))
  · intro T
    exact pointwise_field_star μ T.val (hP T) _ _ (hact T) (hact (star T))

end KadisonSimilarity

end

end OAI
