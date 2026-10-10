import OAI.Analysis.IrrationalRotation.Analysis.BlockedSourceEvent
import OAI.Analysis.IrrationalRotation.Product.ProductScaleCocycleWindow
import OAI.Analysis.IrrationalRotation.Rotation.ProjectionCocycleWindow
import OAI.Analysis.IrrationalRotation.Analysis.FiniteWindowIntegralLower

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ComplexConjugate lp

namespace Invariant233.BlockedProductCoupling

theorem measurable_sourceEvent (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) {r : ProductModel.Base → ℝ}
    (hr : Measurable r) (j : ℕ) : MeasurableSet (sourceEvent p e r j) := by
  have hx : Measurable (circleLeftEndpoint e) := by
    unfold circleLeftEndpoint toCircle leftEndpoint flatten OrderedProductCoupling.leftEndpoint
    fun_prop
  have hy : Measurable (circleRightEndpoint e) := by
    unfold circleRightEndpoint toCircle rightEndpoint flatten OrderedProductCoupling.rightEndpoint
    fun_prop
  have hc : MeasurableSet (currentEvent p.m j) := by
    change MeasurableSet ({z : Sample p.m | ∃ i, (z j i).1 = some (4 : Fin 5)} ∩
      {z | ∀ i, (z j i).2.1 < 1 - 2 / (p.m j : ℝ) ∧
        2 / (p.m j : ℝ) < (z j i).2.2})
    apply MeasurableSet.inter
    · simp only [ofPred_exists]
      exact MeasurableSet.iUnion fun i => (by fun_prop :
        Measurable (fun z : Sample p.m => (z j i).1)) (measurableSet_singleton _)
    · simp only [ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      have hxi : Measurable (fun z : Sample p.m => (z j i).2.1) := by fun_prop
      have hyi : Measurable (fun z : Sample p.m => (z j i).2.2) := by fun_prop
      exact (measurableSet_lt hxi measurable_const).inter
        (measurableSet_lt measurable_const hyi)
  have hf : MeasurableSet (futureBad p.m (fun s => (p.K s : ℝ)) j) := by
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro i
    have hxi : Measurable (fun z : Sample p.m => (z (j + 1 + n) i).2.1) := by fun_prop
    have hyi : Measurable (fun z : Sample p.m => (z (j + 1 + n) i).2.2) := by fun_prop
    exact (measurableSet_le measurable_const hxi).union
      (measurableSet_le hyi measurable_const)
  exact hc.diff (hf.union
    ((measurableSet_lt (hr.comp hx) measurable_const).union
      (measurableSet_lt (measurable_const.sub (hr.comp hy)) measurable_const)))

theorem ae_sourceEvent_coefficient_properties {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hphase : ∀ i, θ i ∈ Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (P : ProjectionField) (hP : ∀ᵐ x ∂ProductModel.baseMeasure, IsStarProjection (P x)) (j : ℕ) :
    ∀ᵐ z ∂sourceLaw p j,
      z ∈ sourceEvent p e (projectionDiagonal P) j →
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖sourceCoefficientA p e θ P z v‖ ≤ p.coefficientBound j) ∧
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖sourceCoefficientB p e θ P z v‖ ≤ p.coefficientBound j) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ ‖sourceCoefficientA p e θ P z 0‖ ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤ ‖sourceCoefficientB p e θ P z 0‖ := by
  have hrep := ae_circle_representatives hp.m_ge_100 source_kappa_nonneg source_kappa_le
    (fun s _ => (hp.a_bounds s).1) (fun s _ => (hp.a_bounds s).2)
    (fun s _ => (hp.b_bounds s).1) (fun s _ => (hp.b_bounds s).2) e j
  filter_upwards [hrep, (sourceLaw_quasiMeasurePreserving_left hp e j).ae hP,
    (sourceLaw_quasiMeasurePreserving_right hp e j).ae hP] with z hz hPx hPy
  intro he
  obtain ⟨_, hcurrent, hfuture, hdiagx, hdiagy⟩ := mem_sourceRetainedEvent_iff.mp he
  have hcur : ∀ i, (e i).1 = j →
      ProductCocycle.representative (circleLeftEndpoint e z i) < 1 - 2 / (p.m j : ℝ) ∧
      2 / (p.m j : ℝ) < ProductCocycle.representative (circleRightEndpoint e z i) := by
    intro i hi
    change circleRepresentative _ < _ ∧ _ < circleRepresentative _
    rw [(hz i).1, (hz i).2]
    change (z (e i).1 (e i).2).2.1 < _ ∧ _ < (z (e i).1 (e i).2).2.2
    subst j
    exact hcurrent (e i).2
  have hfut : ∀ i, j < (e i).1 →
      ProductCocycle.representative (circleLeftEndpoint e z i) <
        1 - 2 * (p.K j : ℝ) / p.N (e i).1 ∧
      2 * (p.K j : ℝ) / p.N (e i).1 <
        ProductCocycle.representative (circleRightEndpoint e z i) := by
    intro i hi
    change circleRepresentative _ < _ ∧ _ < circleRepresentative _
    rw [(hz i).1, (hz i).2]
    exact hfuture (e i).1 hi (e i).2
  obtain ⟨hA, hB⟩ := hp.product_finite_window_coefficients e θ hphase j
    (circleLeftEndpoint e z) (circleRightEndpoint e z) hcur hfut
    (P (circleLeftEndpoint e z) sourceBasisZero)
    ((1 - P (circleRightEndpoint e z)) sourceBasisZero)
    (ProjectionCocycleWindow.projection_vector_norm_le _ hPx)
    (ProjectionCocycleWindow.complement_vector_norm_le _ hPy)
  obtain ⟨hA0, hB0⟩ := ProjectionCocycleWindow.central_lower_bounds
    (P (circleLeftEndpoint e z)) (P (circleRightEndpoint e z))
    (1 / ((j + 1 : ℕ) : ℝ)) hdiagx (by
      change 1 / ((j + 1 : ℕ) : ℝ) ≤
        1 - ((P (circleRightEndpoint e z) ProjectionCocycleWindow.basisZero) 0).re at hdiagy
      linarith)
  exact ⟨hA, hB,
    by simpa [sourceCoefficientA, sourceBasisZero, ProjectionCocycleWindow.basisZero] using hA0,
    by simpa [sourceCoefficientB, sourceBasisZero, ProjectionCocycleWindow.basisZero] using hB0⟩

theorem measurable_sourceCoefficientA (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ) (P : ProjectionField)
    (hPm : ∀ v, Measurable (fun x => (P x sourceBasisZero) v)) (v : ℤ) :
    Measurable (fun z => sourceCoefficientA p e θ P z v) := by
  have hx : Measurable (circleLeftEndpoint e) := by
    unfold circleLeftEndpoint toCircle leftEndpoint flatten OrderedProductCoupling.leftEndpoint
    fun_prop
  exact ((hPm v).comp hx).div (Complex.measurable_ofReal.comp
    ((ProductCocycle.measurable_cocycleVersion θ (fun i => p.C (e i).1) v).comp hx))

theorem measurable_sourceCoefficientB (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ) (P : ProjectionField)
    (hPm : ∀ v, Measurable (fun x => (P x sourceBasisZero) v)) (v : ℤ) :
    Measurable (fun z => sourceCoefficientB p e θ P z v) := by
  have hy : Measurable (circleRightEndpoint e) := by
    unfold circleRightEndpoint toCircle rightEndpoint flatten OrderedProductCoupling.rightEndpoint
    fun_prop
  have hvec : Measurable (fun z : Sample p.m =>
      sourceBasisZero (-v) - (P (circleRightEndpoint e z) sourceBasisZero) (-v)) :=
    measurable_const.sub ((hPm (-v)).comp hy)
  have hvec' : Measurable (fun z : Sample p.m =>
      ((1 - P (circleRightEndpoint e z)) sourceBasisZero) (-v)) := by
    simpa only [sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply] using hvec
  exact (Complex.measurable_ofReal.comp
    ((ProductCocycle.measurable_cocycleVersion θ (fun i => p.C (e i).1) (-v)).comp hy)).mul
      (Complex.continuous_conj.measurable.comp hvec')

theorem source_polynomial_sum_lower {p : ProductScaleData} (hp : ProductScaleLaws p)
    (j : ℕ) (A B : ℤ → ℂ)
    (hA : ∀ v, |v| ≤ (p.K j : ℤ) → ‖A v‖ ≤ p.coefficientBound j)
    (hB : ∀ v, |v| ≤ (p.K j : ℤ) → ‖B v‖ ≤ p.coefficientBound j)
    (hA0 : 1 / ((j + 1 : ℕ) : ℝ) ≤ ‖A 0‖)
    (hB0 : 1 / ((j + 1 : ℕ) : ℝ) ≤ ‖B 0‖) :
    p.ε j ≤ ∑ n ∈ Finset.range (2 * p.K j + 1),
      ‖FiniteWindow.convolution (p.K j) A B n‖ := by
  obtain ⟨n, hn, hε⟩ := hp.polynomial_lower j A B hA hB hA0 hB0
  exact hε.trans (Finset.single_le_sum (fun k _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega)))

theorem sourceEvent_integral_lower {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hphase : ∀ i, θ i ∈ Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (P : ProjectionField) (hP : ∀ᵐ x ∂ProductModel.baseMeasure, IsStarProjection (P x))
    (hPm : ∀ v, Measurable (fun x => (P x sourceBasisZero) v)) (j : ℕ) :
    p.ε j * (sourceLaw p j).real (sourceEvent p e (projectionDiagonal P) j) ≤
      ∫ z in sourceEvent p e (projectionDiagonal P) j,
        ∑ n ∈ Finset.range (2 * p.K j + 1),
          ‖FiniteWindow.convolution (p.K j)
            (sourceCoefficientA p e θ P z) (sourceCoefficientB p e θ P z) n‖
        ∂sourceLaw p j := by
  have := sourceLaw_isProbabilityMeasure hp j
  have hr : Measurable (projectionDiagonal P) := Complex.measurable_re.comp (hPm 0)
  apply FiniteWindow.integral_lower_of_sum_bound (sourceLaw p j)
    (p.K j) (p.coefficientBound j) (1 / ((j + 1 : ℕ) : ℝ)) (p.ε j)
    (source_polynomial_sum_lower hp j)
    (sourceEvent p e (projectionDiagonal P) j)
    (sourceCoefficientA p e θ P) (sourceCoefficientB p e θ P)
    (measurable_sourceCoefficientA p e θ P hPm)
    (measurable_sourceCoefficientB p e θ P hPm)
  filter_upwards [ae_restrict_of_ae (ae_sourceEvent_coefficient_properties hp e θ hphase P hP j),
    ae_restrict_mem (measurable_sourceEvent p e hr j)] with z hz he
  exact hz he

theorem eventually_sourceEvent_and_integral_lower {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hphase : ∀ i, θ i ∈ Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (P : ProjectionField) (hP : ∀ᵐ x ∂ProductModel.baseMeasure, IsStarProjection (P x))
    (hPm : ∀ v, Measurable (fun x => (P x sourceBasisZero) v))
    (hi : ∀ᵐ x ∂ProductModel.baseMeasure,
      0 < projectionDiagonal P x ∧ projectionDiagonal P x < 1) :
    ∀ᶠ j in atTop,
      Real.exp (-82) / 2 ≤ (sourceLaw p j).real (sourceEvent p e (projectionDiagonal P) j) ∧
      (Real.exp (-82) / 2) * p.ε j ≤
        ∫ z in sourceEvent p e (projectionDiagonal P) j,
          ∑ n ∈ Finset.range (2 * p.K j + 1),
            ‖FiniteWindow.convolution (p.K j)
              (sourceCoefficientA p e θ P z) (sourceCoefficientB p e θ P z) n‖
          ∂sourceLaw p j := by
  have hr : Measurable (projectionDiagonal P) := Complex.measurable_re.comp (hPm 0)
  filter_upwards [eventually_sourceEvent_mass hp e hr hi] with j hj
  refine ⟨hj, ?_⟩
  calc
    (Real.exp (-82) / 2) * p.ε j ≤
        p.ε j * (sourceLaw p j).real (sourceEvent p e (projectionDiagonal P) j) := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hj (hp.epsilon_pos j).le
    _ ≤ _ := sourceEvent_integral_lower hp e θ hphase P hP hPm j

end Invariant233.BlockedProductCoupling

end

end OAI
