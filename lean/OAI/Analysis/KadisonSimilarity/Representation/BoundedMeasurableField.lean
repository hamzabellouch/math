import OAI.Analysis.KadisonSimilarity.Derivation.DiagonalMatrixNorm

namespace OAI

/-! # Bounded measurable operator fields on L²

Strong measurability of each constant column suffices to apply a field to
an arbitrary L² vector. An almost-everywhere uniform bound then constructs
the actual bounded L² operator, with its pointwise action and localization
commutation proved directly. No norm measurability of the operator field
is required.
-/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Measurability of constant columns extends to simple-vector sections. -/
theorem aestronglyMeasurable_field_simple
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (f : SimpleFunc Ω H) : AEStronglyMeasurable (fun a => R a (f a)) μ := by
  classical
  induction f using SimpleFunc.induction' with
  | const x => simpa only [SimpleFunc.const_apply] using hR x
  | @pcw f g s hs hf hg =>
    have heq : (fun a => R a (f.piecewise s hs g a)) =
        s.piecewise (fun a => R a (f a)) (fun a => R a (g a)) := by
      funext a
      by_cases ha : a ∈ s <;> simp [SimpleFunc.piecewise_apply, ha]
    rw [heq]
    exact hf.restrict.piecewise hs hg.restrict

/-- Only the strong operator measurability of the field is needed for
applying it to a measurable vector section. -/
theorem aestronglyMeasurable_field_apply
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    {f : Ω → H} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a => R a (f a)) μ := by
  let g := hf.mk f
  have hg : StronglyMeasurable g := hf.stronglyMeasurable_mk
  have hlim : AEStronglyMeasurable (fun a => R a (g a)) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => aestronglyMeasurable_field_simple μ R hR (hg.approx n))
    exact Eventually.of_forall fun a =>
      ((R a).continuous.tendsto (g a)).comp (hg.tendsto_approx a)
  apply hlim.congr
  filter_upwards [hf.ae_eq_mk] with a ha
  exact congrArg (R a) ha.symm

/-- An essentially bounded field sends L² sections to L² sections. -/
theorem boundedField_memLp
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    MemLp (fun a => R a (f a)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := C)
    (aestronglyMeasurable_field_apply μ R hR (Lp.aestronglyMeasurable f))
  filter_upwards [hbound] with a ha
  exact ((R a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))

/-- The L² section obtained by applying an essentially bounded field. -/
def boundedFieldVector
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) : Lp H 2 μ :=
  (boundedField_memLp μ R hR C hbound f).toLp (fun a => R a (f a))

theorem boundedFieldVector_ae
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    boundedFieldVector μ R hR C hbound f =ᵐ[μ] fun a => R a (f a) :=
  MemLp.coeFn_toLp _

def boundedFieldLinear
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := boundedFieldVector μ R hR C hbound
  map_add' f g := by
    apply Lp.ext
    filter_upwards [boundedFieldVector_ae μ R hR C hbound (f + g),
      boundedFieldVector_ae μ R hR C hbound f, boundedFieldVector_ae μ R hR C hbound g,
      Lp.coeFn_add f g, Lp.coeFn_add (boundedFieldVector μ R hR C hbound f)
        (boundedFieldVector μ R hR C hbound g)] with a hfg hf hg hin hout
    rw [hfg, hout, hin]
    simp only [Pi.add_apply, map_add, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [boundedFieldVector_ae μ R hR C hbound (c • f),
      boundedFieldVector_ae μ R hR C hbound f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (boundedFieldVector μ R hR C hbound f)] with a hcf hf hin hout
    change boundedFieldVector μ R hR C hbound (c • f) a =
      (c • boundedFieldVector μ R hR C hbound f) a
    rw [hcf, hout, hin]
    simp only [Pi.smul_apply, map_smul, hf]

theorem boundedFieldVector_norm_le
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    ‖boundedFieldVector μ R hR C hbound f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedFieldVector_ae μ R hR C hbound f, hbound] with a ha hb
  rw [ha]
  exact ((R a).le_opNorm (f a)).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

/-- The bounded L² operator associated to an essentially bounded strongly
operator measurable field. -/
def boundedFieldOperator
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (boundedFieldLinear μ R hR C hbound).mkContinuous C
    (boundedFieldVector_norm_le μ R hR C hbound)

theorem boundedFieldOperator_action
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (f : Lp H 2 μ) :
    ∀ᵐ a ∂μ, boundedFieldOperator μ R hR C hbound f a = R a (f a) :=
  boundedFieldVector_ae μ R hR C hbound f

theorem boundedFieldOperator_norm_le
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) :
    ‖boundedFieldOperator μ R hR C hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- This construction is the reverse direction of diagonal reconstruction. -/
theorem boundedFieldOperator_eq_of_action
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a)) :
    boundedFieldOperator μ R hR C hbound = T := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [boundedFieldOperator_action μ R hR C hbound f, hT f] with a ha ht
  exact ha.trans ht.symm

/-- Every bounded measurable field commutes with all scalar localizations. -/
theorem boundedFieldOperator_commutes_localization
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (s : Set Ω) (hs : MeasurableSet s) :
    boundedFieldOperator μ R hR C hbound * l2Localization μ s hs =
      l2Localization μ s hs * boundedFieldOperator μ R hR C hbound :=
  pointwise_action_commutes_localization μ _ R
    (boundedFieldOperator_action μ R hR C hbound) s hs

/-- Pointwise commutation with an already reconstructed operator gives
actual commutation of the L² operators. -/
theorem boundedFieldOperator_commutes_of_ae
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) (S : Ω → H →L[ℂ] H)
    (hT : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = S a (f a))
    (hcomm : ∀ᵐ a ∂μ, R a * S a = S a * R a) :
    boundedFieldOperator μ R hR C hbound * T =
      T * boundedFieldOperator μ R hR C hbound := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [boundedFieldOperator_action μ R hR C hbound (T f),
    boundedFieldOperator_action μ R hR C hbound f,
    hT (boundedFieldOperator μ R hR C hbound f), hT f, hcomm]
    with a hRT hRf hTR hTf ha
  change boundedFieldOperator μ R hR C hbound (T f) a =
    T (boundedFieldOperator μ R hR C hbound f) a
  rw [hRT, hTR, hRf, hTf]
  exact congrArg (fun X : H →L[ℂ] H => X (f a)) ha

/-- A measurable field supported on a projection gives a genuinely
left-supported L² operator. -/
theorem boundedFieldOperator_left_support
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (P : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hsupport : ∀ᵐ a ∂μ, p a * R a = R a) :
    P * boundedFieldOperator μ R hR C hbound = boundedFieldOperator μ R hR C hbound := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP (boundedFieldOperator μ R hR C hbound f),
    boundedFieldOperator_action μ R hR C hbound f, hsupport] with a hpf hrf ha
  change P (boundedFieldOperator μ R hR C hbound f) a =
    boundedFieldOperator μ R hR C hbound f a
  rw [hpf, hrf]
  exact congrArg (fun X : H →L[ℂ] H => X (f a)) ha

/-- Right support is also recovered from the corresponding pointwise
identity, with no simultaneous null-set assumption. -/
theorem boundedFieldOperator_right_support
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C)
    (P : Lp H 2 μ →L[ℂ] Lp H 2 μ) (p : Ω → H →L[ℂ] H)
    (hP : ∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, P f a = p a (f a))
    (hsupport : ∀ᵐ a ∂μ, R a * p a = R a) :
    boundedFieldOperator μ R hR C hbound * P = boundedFieldOperator μ R hR C hbound := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [hP f, boundedFieldOperator_action μ R hR C hbound (P f),
    boundedFieldOperator_action μ R hR C hbound f, hsupport] with a hpf hrpf hrf ha
  change boundedFieldOperator μ R hR C hbound (P f) a =
    boundedFieldOperator μ R hR C hbound f a
  rw [hrpf, hpf, hrf]
  exact congrArg (fun X : H →L[ℂ] H => X (f a)) ha

/-- A bounded measurable field yields the actual localization-commuting
operator required for measurable fiber selectors. -/
theorem exists_bounded_operator_of_measurable_field
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) :
    ∃ T : Lp H 2 μ →L[ℂ] Lp H 2 μ, ‖T‖ ≤ C ∧
      (∀ f : Lp H 2 μ, ∀ᵐ a ∂μ, T f a = R a (f a)) ∧
      ∀ (s : Set Ω) (hs : MeasurableSet s),
        T * l2Localization μ s hs = l2Localization μ s hs * T :=
  ⟨boundedFieldOperator μ R hR C hbound, boundedFieldOperator_norm_le μ R hR C hC hbound,
    boundedFieldOperator_action μ R hR C hbound,
    boundedFieldOperator_commutes_localization μ R hR C hbound⟩

variable [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

/-- The constructed operator has exactly the essential uniform norm
bounds of its pointwise field. -/
theorem boundedFieldOperator_norm_iff
    (R : Ω → H →L[ℂ] H)
    (hR : ∀ x : H, AEStronglyMeasurable (fun a => R a x) μ)
    (C : ℝ) (hbound : ∀ᵐ a ∂μ, ‖R a‖ ≤ C) (c : ℝ) (hc : 0 ≤ c) :
    ‖boundedFieldOperator μ R hR C hbound‖ ≤ c ↔ ∀ᵐ a ∂μ, ‖R a‖ ≤ c :=
  pointwise_field_norm_iff μ _ R (boundedFieldOperator_action μ R hR C hbound) c hc

end KadisonSimilarity

end

end OAI
