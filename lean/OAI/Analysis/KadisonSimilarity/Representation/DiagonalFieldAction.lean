import OAI.Analysis.KadisonSimilarity.Representation.DiagonalOperatorField
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! # Pointwise action on all L² vectors

The field reconstructed from constant columns acts pointwise on arbitrary
L² vectors. Indicator constants give a dense class; two successive AE
subsequences prove that the pointwise-action identity is norm closed.
-/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [IsFiniteMeasure μ] [CompleteSpace H] in
/-- Pointwise action by any family of continuous operators is a closed
condition on L² vectors for a fixed bounded operator. -/
theorem isClosed_pointwise_operator_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (field : Ω → H →L[ℂ] H) :
    IsClosed {f : Lp H 2 μ | ∀ᵐ a ∂μ, T f a = field a (f a)} := by
  apply IsSeqClosed.isClosed
  intro f g hf hlim
  obtain ⟨s, hs, hsae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have ht : Tendsto (fun n => T (f (s n))) atTop (𝓝 (T g)) :=
    (T.continuous.tendsto g).comp (hlim.comp hs.tendsto_atTop)
  obtain ⟨t, htmono, htae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have heq : ∀ᵐ a ∂μ, ∀ n : ℕ,
      T (f (s (t n))) a = field a (f (s (t n)) a) :=
    eventually_countable_forall.mpr (fun n => hf (s (t n)))
  filter_upwards [hsae, htae, heq] with a ha hta he
  have hr := ((field a).continuous.tendsto (g a)).comp (ha.comp htmono.tendsto_atTop)
  have hefun : (fun n => T (f (s (t n))) a) =
      (fun n => field a (f (s (t n)) a)) := funext he
  rw [hefun] at hta
  exact tendsto_nhds_unique hta hr

omit [IsFiniteMeasure μ] [CompleteSpace H] in
/-- Measurability of the field acting on a section follows from its actual
L² operator action, so it is not an extra input to the construction. -/
theorem aestronglyMeasurable_of_pointwise_operator_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (field : Ω → H →L[ℂ] H) (f : Lp H 2 μ)
    (h : ∀ᵐ a ∂μ, T f a = field a (f a)) :
    AEStronglyMeasurable (fun a => field a (f a)) μ :=
  (Lp.aestronglyMeasurable (T f)).congr h

omit [CompleteSpace H] in
/-- Commutation with diagonal localizations extends the constant-column
formula to every L² vector. -/
theorem diagonal_operator_action_of_columns
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T)
    (field : Ω → H →L[ℂ] H)
    (hcolumns : ∀ x : H, ∀ᵐ a ∂μ, T (Lp.const 2 μ x) a = field a x)
    (f : Lp H 2 μ) : ∀ᵐ a ∂μ, T f a = field a (f a) := by
  apply Lp.induction (by simp : (2 : ℝ≥0∞) ≠ ∞)
    (motive := fun f => ∀ᵐ a ∂μ, T f a = field a (f a))
    ?_ ?_ (isClosed_pointwise_operator_action μ T field) f
  · intro c r hr hμr
    change ∀ᵐ a ∂μ, T (indicatorConstLp 2 hr hμr.ne c) a =
      field a (indicatorConstLp 2 hr hμr.ne c a)
    have heq := congrArg (fun S : Lp H 2 μ →L[ℂ] Lp H 2 μ => S (Lp.const 2 μ c))
      (hT r hr)
    change T (l2Localization μ r hr (Lp.const 2 μ c)) =
      l2Localization μ r hr (T (Lp.const 2 μ c)) at heq
    rw [l2Localization_const] at heq
    filter_upwards [hcolumns c, l2Localization_ae μ r hr (T (Lp.const 2 μ c)),
      indicatorConstLp_coeFn (p := 2) (hs := hr) (hμs := hμr.ne) (c := c)]
      with a hc hl hi
    rw [heq, hl, hi]
    by_cases ha : a ∈ r
    · simpa only [Set.indicator_of_mem ha] using hc
    · simp only [Set.indicator_of_notMem ha, map_zero]
  · intro f g hf hg _ hfa hga
    filter_upwards [hfa, hga, Lp.coeFn_add (hf.toLp f) (hg.toLp g),
      Lp.coeFn_add (T (hf.toLp f)) (T (hg.toLp g))] with a hfa hga hfg hout
    rw [map_add, hout, hfg, Pi.add_apply, Pi.add_apply, map_add, hfa, hga]

variable [TopologicalSpace.SeparableSpace H]

/-- The actual field of a diagonal-commuting operator, with the complete
pointwise-action formula on all L² vectors. -/
theorem exists_conull_diagonal_field_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ field : ∀ _a : s, H →L[ℂ] H,
        (∀ a, ‖field a‖ ≤ ‖T‖) ∧
        ∀ f : Lp H 2 μ, ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
          T f a = field a (f a) := by
  classical
  obtain ⟨s, hsm, hsnull, field, hnorm, hcols⟩ :=
    exists_conull_diagonal_operator_field μ T hT
  let R : Ω → H →L[ℂ] H := fun a => if ha : a ∈ s then field ⟨a, ha⟩ else 0
  have hs : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hsnull
  have hc (x : H) : ∀ᵐ a ∂μ, T (Lp.const 2 μ x) a = R a x := by
    have hr : ∀ᵐ a ∂μ.restrict s, T (Lp.const 2 μ x) a = R a x := by
      apply (ae_restrict_iff_subtype hsm).mpr
      filter_upwards [hcols x] with a ha
      simpa only [R, dite_eq_left a.property] using ha.symm
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha
  refine ⟨s, hsm, hsnull, field, hnorm, ?_⟩
  intro f
  have hf := diagonal_operator_action_of_columns μ T hT R hc f
  have hr := (ae_restrict_iff_subtype hsm).mp (ae_restrict_of_ae hf)
  filter_upwards [hr] with a ha
  simpa only [R, dite_eq_left a.property] using ha

omit [IsFiniteMeasure μ] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- An AE norm bound on a conull pointwise field bounds the original L²
operator. This proves the converse direction of the essential-norm formula. -/
theorem norm_le_of_conull_pointwise_action
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (s : Set Ω) (hsm : MeasurableSet s) (hsnull : μ sᶜ = 0)
    (field : ∀ _a : s, H →L[ℂ] H)
    (haction : ∀ f : Lp H 2 μ, ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
      T f a = field a (f a))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖field a‖ ≤ C) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have hs : ∀ᵐ a ∂μ, a ∈ s := mem_ae_iff.mpr hsnull
  have hsub : ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖T f a‖ ≤ C * ‖f a‖ := by
    filter_upwards [haction f, hbound] with a he hb
    rw [he]
    exact ((field a).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hglobal : ∀ᵐ a ∂μ, ‖T f a‖ ≤ C * ‖f a‖ := by
    have hr : ∀ᵐ a ∂μ.restrict s, ‖T f a‖ ≤ C * ‖f a‖ :=
      (ae_restrict_iff_subtype (μ := μ)
        (p := fun a : Ω => ‖T f a‖ ≤ C * ‖f a‖) hsm).mpr hsub
    filter_upwards [hs, (ae_restrict_iff' hsm).mp hr] with a ha h
    exact h ha
  calc
    ‖T f‖ ≤ ‖(C : ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hglobal, Lp.coeFn_smul (C : ℂ) f] with a ha he
      rw [he, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC]
      exact ha
    _ = C * ‖f‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

/-- A diagonal-commuting operator has a genuine field with both the
pointwise-action identity and the exact scalar norm-bound equivalence. -/
theorem exists_diagonal_field_with_norm_iff
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ (r : Set Ω) (hr : MeasurableSet r),
      T * l2Localization μ r hr = l2Localization μ r hr * T) :
    ∃ s : Set Ω, MeasurableSet s ∧ μ sᶜ = 0 ∧
      ∃ field : ∀ _a : s, H →L[ℂ] H,
        (∀ f : Lp H 2 μ, ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ,
          T f a = field a (f a)) ∧
        ∀ C : ℝ, 0 ≤ C →
          (‖T‖ ≤ C ↔ ∀ᵐ (a : s) ∂Measure.comap ((↑) : s → Ω) μ, ‖field a‖ ≤ C) := by
  obtain ⟨s, hsm, hsnull, field, hnorm, haction⟩ :=
    exists_conull_diagonal_field_action μ T hT
  refine ⟨s, hsm, hsnull, field, haction, ?_⟩
  intro C hC
  constructor
  · intro h
    exact Filter.Eventually.of_forall fun a => (hnorm a).trans h
  · exact norm_le_of_conull_pointwise_action μ T s hsm hsnull field haction C hC

end KadisonSimilarity

end

end OAI
