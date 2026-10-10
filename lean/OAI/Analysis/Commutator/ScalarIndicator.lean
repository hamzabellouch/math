import Mathlib
import OAI.Analysis.Commutator.DecomposableNorm

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma indicator_measurable (s : Set Ω) (hs : MeasurableSet s) (ξ : H) :
    AEStronglyMeasurable (fun a => (s.indicator (fun _ => (1:H →L[ℂ] H)) a) ξ) μ := by
  classical
  convert (aestronglyMeasurable_const (b:=ξ)).indicator hs using 1
  ext a
  by_cases ha : a∈s <;> simp [ha]

lemma indicator_bound (s : Set Ω) :
    ∀ᵐ a ∂μ,‖s.indicator (fun _ => (1:H →L[ℂ] H)) a‖≤1 := by
  classical
  apply Eventually.of_forall
  intro a
  by_cases ha : a∈s
  · simp only [Set.indicator_of_mem ha]
    exact ContinuousLinearMap.norm_id_le
  · simp [ha]

def indicatorOperator (s : Set Ω) (hs : MeasurableSet s) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  operator μ (s.indicator (fun _ => (1:H →L[ℂ] H)))
    (indicator_measurable μ s hs) (indicator_bound μ s)

lemma indicatorOperator_ae (s : Set Ω) (hs : MeasurableSet s) (f : Lp H 2 μ) :
    indicatorOperator μ s hs f =ᵐ[μ] s.indicator f := by
  classical
  filter_upwards [operator_ae μ _ (indicator_measurable μ s hs) (indicator_bound μ s) f] with a ha
  change indicatorOperator μ s hs f a=_ at ha ⊢
  rw [ha]
  by_cases hx : a∈s <;> simp [hx]

lemma indicatorOperator_norm_sq (s : Set Ω) (hs : MeasurableSet s) (f : Lp H 2 μ) :
    ‖indicatorOperator μ s hs f‖^2=∫ a in s,‖f a‖^2 ∂μ := by
  classical
  rw [l2_norm_sq,←integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorOperator_ae μ s hs f] with a ha
  rw [ha]
  by_cases hx : a∈s <;> simp [hx]

variable [IsFiniteMeasure μ]

lemma indicatorOperator_const (s : Set Ω) (hs : MeasurableSet s) (ξ : H) :
    indicatorOperator μ s hs (Lp.const 2 μ ξ)=indicatorConstLp 2 hs (measure_ne_top μ s) ξ := by
  classical
  apply Lp.ext
  filter_upwards [indicatorOperator_ae μ s hs (Lp.const 2 μ ξ),Lp.coeFn_const (p:=2) (μ:=μ) (c:=ξ),
    indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=measure_ne_top μ s) (c:=ξ)] with a ha hc hi
  rw [ha,hi]
  by_cases hx : a∈s
  · simp only [Set.indicator_of_mem hx]
    exact hc
  · simp [hx]

theorem local_constant_ae_bound (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hcomm : ∀ (s : Set Ω) (hs : MeasurableSet s),Commute Y (indicatorOperator μ s hs))
    (ξ : H) : ∀ᵐ a ∂μ,‖Y (Lp.const 2 μ ξ) a‖≤‖Y‖*‖ξ‖ := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (Y (Lp.const 2 μ ξ)))).mp
    (Lp.memLp (Y (Lp.const 2 μ ξ)))
  have hh : (fun a => ‖Y (Lp.const 2 μ ξ) a‖^2) ≤ᵐ[μ] (fun _ => (‖Y‖*‖ξ‖)^2) := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const _)
    intro s hs hμs
    have he : indicatorOperator μ s hs (Y (Lp.const 2 μ ξ))=
        Y (indicatorConstLp 2 hs (measure_ne_top μ s) ξ) := by
      rw [←indicatorOperator_const μ s hs ξ]
      exact congrArg (fun A : Lp H 2 μ →L[ℂ] Lp H 2 μ => A (Lp.const 2 μ ξ)) (hcomm s hs).eq.symm
    calc
      (∫ a in s,‖Y (Lp.const 2 μ ξ) a‖^2 ∂μ)=
          ‖indicatorOperator μ s hs (Y (Lp.const 2 μ ξ))‖^2 :=
        (indicatorOperator_norm_sq μ s hs _).symm
      _=‖Y (indicatorConstLp 2 hs (measure_ne_top μ s) ξ)‖^2 := by rw [he]
      _≤(‖Y‖*‖indicatorConstLp 2 hs (measure_ne_top μ s) ξ‖)^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Y) (norm_nonneg _))).mpr (Y.le_opNorm _)
      _=‖Y‖^2*(∫ a in s,‖ξ‖^2 ∂μ) := by rw [mul_pow,indicator_norm_sq μ s hs (measure_ne_top μ s) ξ]
      _=(∫ a in s,(‖Y‖*‖ξ‖)^2 ∂μ) := by simp only [mul_pow,integral_const_mul]
  filter_upwards [hh] with a ha
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg Y) (norm_nonneg ξ))).mp ha

end Kadison.Decomposable

end

end
end

end OAI
