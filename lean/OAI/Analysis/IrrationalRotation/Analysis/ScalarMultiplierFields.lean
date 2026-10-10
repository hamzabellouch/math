import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplier
import OAI.Analysis.IrrationalRotation.Operators.ColumnOperator
import OAI.Analysis.IrrationalRotation.Operators.LpOperatorExt
import OAI.Analysis.IrrationalRotation.Model.FieldOperator
import OAI.Analysis.IrrationalRotation.Operators.FieldProjections

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sq_eq_integral_hilbert (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  let := InnerProductSpace.rclikeToReal ℂ E
  rw [norm_sq_eq_re_inner (𝕜 := ℝ), L2.inner_def]
  simp only [RCLike.re_to_real, real_inner_self_eq_norm_sq]

variable [IsFiniteMeasure μ]

theorem norm_indicator_sq_hilbert (s : Set X) (hs : MeasurableSet s) (v : E) :
    ‖indicatorConstLp 2 hs (measure_ne_top μ s) v‖ ^ 2 = ‖v‖ ^ 2 * μ.real s := by
  rw [norm_sq_eq_integral_hilbert]
  calc
    (∫ x, ‖indicatorConstLp 2 hs (measure_ne_top μ s) v x‖ ^ 2 ∂μ) =
        ∫ x, s.indicator (fun _ => ‖v‖ ^ 2) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs)
        (hμs := measure_ne_top μ s) (c := v)] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]
    _ = ‖v‖ ^ 2 * μ.real s := by rw [integral_indicator hs]; simp [mul_comm]

theorem norm_multiplier_indicator_sq_hilbert (s : Set X) (hs : MeasurableSet s)
    (f : Lp E 2 μ) :
    ‖multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ)) f‖ ^ 2 =
      ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_integral_hilbert, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [multiplier_indicator_coe s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [Set.indicator, hxs]

theorem ae_norm_apply_const_le
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) (v : E) :
    ∀ᵐ x ∂μ, ‖A (Lp.const 2 μ v) x‖ ≤ ‖A‖ * ‖v‖ := by
  apply Fields.ae_norm_le_of_local_square_integral (mul_nonneg (norm_nonneg A) (norm_nonneg v))
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
  intro s hs
  have hcomm := congrArg (fun B : Lp E 2 μ →L[ℂ] Lp E 2 μ => B (Lp.const 2 μ v))
    (hA (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))).eq
  have hid : A (indicatorConstLp 2 hs (measure_ne_top μ s) v) =
      multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))
        (A (Lp.const 2 μ v)) := by
    simpa only [mul_apply_eq_comp, multiplier_indicator_const] using hcomm
  rw [← norm_multiplier_indicator_sq_hilbert s hs, ← hid]
  calc
    ‖A (indicatorConstLp 2 hs (measure_ne_top μ s) v)‖ ^ 2 ≤
        (‖A‖ * ‖indicatorConstLp 2 hs (measure_ne_top μ s) v‖) ^ 2 := by
      gcongr
      exact A.le_opNorm _
    _ = (‖A‖ * ‖v‖) ^ 2 * μ.real s := by
      rw [mul_pow, norm_indicator_sq_hilbert]
      ring

theorem apply_const_finsetSum_coe {ι : Type*}
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (s : Finset ι) (z : ι → ℂ) (v : ι → E) :
    A (Lp.const 2 μ (∑ i ∈ s, z i • v i)) =ᵐ[μ]
      fun x => ∑ i ∈ s, z i • A (Lp.const 2 μ (v i)) x := by
  have heq : A (Lp.const 2 μ (∑ i ∈ s, z i • v i)) =
      ∑ i ∈ s, z i • A (Lp.const 2 μ (v i)) := by
    change (A.comp (Lp.constL 2 μ ℂ)) (∑ i ∈ s, z i • v i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact map_smul _ _ _
  rw [heq]
  have hsmul : ∀ᵐ x ∂μ, ∀ i ∈ s,
      (z i • A (Lp.const 2 μ (v i))) x = z i • A (Lp.const 2 μ (v i)) x := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    exact Lp.coeFn_smul _ _
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => z i • A (Lp.const 2 μ (v i))), hsmul]
    with x hx hxs
  rw [hx]
  exact Finset.sum_congr rfl hxs

theorem apply_indicator_coe_of_commutes
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g))
    (s : Set X) (hs : MeasurableSet s) (v : E) :
    A (indicatorConstLp 2 hs (measure_ne_top μ s) v) =ᵐ[μ]
      s.indicator (A (Lp.const 2 μ v)) := by
  have hcomm := congrArg (fun B : Lp E 2 μ →L[ℂ] Lp E 2 μ => B (Lp.const 2 μ v))
    (hA (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))).eq
  have hid : A (indicatorConstLp 2 hs (measure_ne_top μ s) v) =
      multiplier (indicatorConstLp ∞ hs (measure_ne_top μ s) (1 : ℂ))
        (A (Lp.const 2 μ v)) := by
    simpa only [mul_apply_eq_comp, multiplier_indicator_const] using hcomm
  rw [hid]
  exact multiplier_indicator_coe s hs _

variable {ι : Type*} [Countable ι] [CompleteSpace E]

omit [IsFiniteMeasure μ] in

theorem exists_stronglyMeasurable_field_of_rational_tests
    (b : HilbertBasis ι ℂ E) (c : X → ι → E) {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ, ∀ᵐ x ∂μ,
      ‖∑ i : s, Fields.rationalComplex (q i) • c x i‖ ≤
        C * ‖∑ i : s, Fields.rationalComplex (q i) • b i‖)
    (hc : ∀ i, AEStronglyMeasurable (fun x => c x i) μ) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ C) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ᵐ x ∂μ, ∀ i, F x (b i) = c x i) := by
  classical
  let d : X → ι → E := fun x i => (hc i).mk (fun x => c x i) x
  have hd : ∀ i, StronglyMeasurable fun x => d x i :=
    fun i => (hc i).stronglyMeasurable_mk
  have hdc : ∀ᵐ x ∂μ, ∀ i, d x i = c x i :=
    ae_all_iff.mpr (fun i => (hc i).ae_eq_mk.symm)
  have hdtest : ∀ s : Finset ι, ∀ q : s → ℚ × ℚ, ∀ᵐ x ∂μ,
      ‖∑ i : s, Fields.rationalComplex (q i) • d x i‖ ≤
        C * ‖∑ i : s, Fields.rationalComplex (q i) • b i‖ := by
    intro s q
    filter_upwards [hbound s q, hdc] with x hx hdx
    simpa only [hdx] using hx
  have hdbound := Fields.ae_finite_combination_bound_of_rational b d hdtest
  obtain ⟨s, hsae, hsm, hsb⟩ := hdbound.exists_measurable_mem
  let e : X → ι → E := fun x i => s.indicator (fun x => d x i) x
  have he : ∀ i, StronglyMeasurable fun x => e x i :=
    fun i => (hd i).indicator hsm
  have hebound : ∀ x, ∀ z : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ (e x) z‖ ≤
        C * ‖Finsupp.linearCombination ℂ b z‖ := by
    intro x z
    by_cases hx : x ∈ s
    · simpa only [e, Set.indicator_of_mem hx] using hsb x hx z
    · simp only [e, Set.indicator_of_notMem hx]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_zero, Finset.sum_const_zero,
        norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
  refine ⟨fun x => Fields.columnOperator b (e x), ?_, ?_, ?_⟩
  · intro x
    exact Fields.norm_columnOperator_le b (e x) hC (hebound x)
  · intro v
    exact Fields.stronglyMeasurable_columnOperator_apply b e hebound he stronglyMeasurable_const
  · filter_upwards [hsae, hdc] with x hx hdx
    intro i
    rw [Fields.columnOperator_apply_basis b (e x) (hebound x)]
    simpa only [e, Set.indicator_of_mem hx] using hdx i

theorem exists_field_columns_of_commutes
    (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ᵐ x ∂μ, ∀ i, F x (b i) = A (Lp.const 2 μ (b i)) x) := by
  apply exists_stronglyMeasurable_field_of_rational_tests b
    (fun x i => A (Lp.const 2 μ (b i)) x) (norm_nonneg A)
  · intro s q
    filter_upwards [ae_norm_apply_const_le A hA
      (∑ i : s, Fields.rationalComplex (q i) • b i),
      apply_const_finsetSum_coe A Finset.univ
        (fun i : s => Fields.rationalComplex (q i)) (fun i : s => b i)] with x hx hcomb
    rw [hcomb] at hx
    exact hx
  · intro i
    exact Lp.aestronglyMeasurable _

omit [CompleteSpace E] in

theorem field_unique_of_representation (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F G : X → E →L[ℂ] E)
    (hF : ∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x))
    (hG : ∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => G x (f x)) : F =ᵐ[μ] G := by
  apply Fields.ae_eq_of_countable_columns
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  intro i
  filter_upwards [hF (Lp.const 2 μ (b i)), hG (Lp.const 2 μ (b i)),
    Lp.coeFn_const 2 μ (b i)] with x hx hy hc
  simpa only [hc, Function.const_apply] using hx.symm.trans hy

omit [Countable ι] [CompleteSpace E] in

theorem represented_eq_of_basis_columns (b : HilbertBasis ι ℂ E)
    (A T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F : X → E →L[ℂ] E)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g))
    (hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => F x (f x))
    (hcol : ∀ᵐ x ∂μ, ∀ i, F x (b i) = A (Lp.const 2 μ (b i)) x) : A = T := by
  apply Fields.lp_operator_ext_basis_indicator b (by simp) A T
  intro i s hs hμs
  apply Lp.ext
  filter_upwards [apply_indicator_coe_of_commutes A hA s hs (b i),
    hT (indicatorConstLp 2 hs hμs (b i)),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs) (hμs := hμs) (c := b i),
    hcol] with x hx ht hi hc
  rw [hx, ht, hi]
  by_cases hxs : x ∈ s
  · simpa only [Set.indicator_of_mem hxs] using (hc i).symm
  · simp only [Set.indicator_of_notMem hxs, map_zero]

theorem exists_field_of_commutes (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x)) := by
  obtain ⟨F, hnorm, hmeas, hcol⟩ := exists_field_columns_of_commutes b A hA
  let T : Lp E 2 μ →L[ℂ] Lp E 2 μ := DirectIntegral.fieldOperator F ‖A‖ hnorm
    (fun v => (hmeas v).aestronglyMeasurable)
  have hT : ∀ f : Lp E 2 μ, T f =ᵐ[μ] fun x => F x (f x) := by
    intro f
    exact DirectIntegral.fieldOperatorVec_ae F ‖A‖ hnorm
      (fun v => (hmeas v).aestronglyMeasurable) f
  have hAT : A = T := represented_eq_of_basis_columns b A T F hA hT hcol
  refine ⟨F, hnorm, hmeas, ?_⟩
  intro f
  rw [hAT]
  exact hT f

theorem exists_unique_field_of_commutes (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x)) ∧
      (∀ G : X → E →L[ℂ] E,
        (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => G x (f x)) → F =ᵐ[μ] G) := by
  obtain ⟨F, hnorm, hmeas, hrep⟩ := exists_field_of_commutes b A hA
  exact ⟨F, hnorm, hmeas, hrep, fun G hG => field_unique_of_representation b A F G hrep hG⟩

omit [IsFiniteMeasure μ] [CompleteSpace E] in

theorem separableSpace_of_countable_hilbertBasis (b : HilbertBasis ι ℂ E) :
    TopologicalSpace.SeparableSpace E := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have hs := ((Set.countable_range b).isSeparable.span (R := ℂ)).closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span] at hs
  exact hs

theorem scalar_multiplier_fields_complete (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x)) ∧
      (∀ G : X → E →L[ℂ] E,
        (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => G x (f x)) → F =ᵐ[μ] G) ∧
      (∀ f : Lp E 2 μ, A.adjoint f =ᵐ[μ] fun x => (F x).adjoint (f x)) ∧
      (∀ (B : Lp E 2 μ →L[ℂ] Lp E 2 μ) (G : X → E →L[ℂ] E),
        (∀ f : Lp E 2 μ, B f =ᵐ[μ] fun x => G x (f x)) →
        ∀ f : Lp E 2 μ, (A * B) f =ᵐ[μ] fun x => (F x * G x) (f x)) ∧
      (IsStarProjection A → ∀ᵐ x ∂μ, IsStarProjection (F x)) := by
  let := separableSpace_of_countable_hilbertBasis b
  obtain ⟨F, hnorm, hmeas, hrep, huniq⟩ := exists_unique_field_of_commutes b A hA
  have hAT : A = DirectIntegral.fieldOperator F ‖A‖ hnorm
      (fun v => (hmeas v).aestronglyMeasurable) := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hrep f).trans (DirectIntegral.fieldOperatorVec_ae F ‖A‖ hnorm
      (fun v => (hmeas v).aestronglyMeasurable) f).symm
  refine ⟨F, hnorm, hmeas, hrep, huniq, ?_, ?_, ?_⟩
  · have hnormAdj : ∀ x, ‖(F x).adjoint‖ ≤ ‖A‖ := by
      intro x
      simpa only [LinearIsometryEquiv.norm_map] using hnorm x
    have hmeasAdj : ∀ v, AEStronglyMeasurable (fun x => (F x).adjoint v) μ := by
      intro v
      exact (StrongField.stronglyMeasurable_adjoint_apply_of_columns b F
        (fun i => hmeas (b i)) v).aestronglyMeasurable
    have hAdj : DirectIntegral.fieldOperator (fun x => (F x).adjoint) ‖A‖ hnormAdj hmeasAdj =
        A.adjoint := by
      calc
        _ = (DirectIntegral.fieldOperator F ‖A‖ hnorm
            (fun v => (hmeas v).aestronglyMeasurable)).adjoint :=
          DirectIntegral.fieldOperator_adjoint_of_ae_eq
            (Filter.Eventually.of_forall fun x => rfl)
        _ = A.adjoint := congrArg ContinuousLinearMap.adjoint hAT.symm
    intro f
    rw [← hAdj]
    exact DirectIntegral.fieldOperator_ae _ _ _ _ f
  · intro B G hG f
    filter_upwards [hrep (B f), hG f] with x hx hy
    change A (B f) x = (F x) (G x (f x))
    rw [hx, hy]
  · intro hP
    have hPT : IsStarProjection (DirectIntegral.fieldOperator (μ := μ) F ‖A‖ hnorm
        (fun v => (hmeas v).aestronglyMeasurable)) := by
      rw [← hAT]
      exact hP
    exact DirectIntegral.ae_isStarProjection_of_fieldOperator b (norm_nonneg A) hmeas hPT

end Invariant233.L2Multiplication

end OAI
