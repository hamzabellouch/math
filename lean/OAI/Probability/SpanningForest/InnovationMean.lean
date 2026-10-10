import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem336.InnovationMean

theorem integrable_of_mem_Icc {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1) :
    Integrable X P := by
  apply (integrable_const (1 : ℝ)).mono' hX.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1]
    exact (hbound ω).2

theorem posterior_setIntegral {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X Y : Ω → ℝ} (hX : Integrable X P)
    {A : Set Ω} (hA : MeasurableSet[m] A)
    (hpost : Y =ᵐ[P] P[X | m]) :
    ∫ ω in A, Y ω ∂P = ∫ ω in A, X ω ∂P := by
  calc
    ∫ ω in A, Y ω ∂P = ∫ ω in A, (P[X | m]) ω ∂P :=
      integral_congr_ae (ae_restrict_of_ae hpost)
    _ = ∫ ω in A, X ω ∂P := setIntegral_condExp hm hX hA

theorem setIntegral_intervalIntegral_posterior_sub_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P]
    {m : ℝ → MeasurableSpace Ω} (hm : ∀ t, m t ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable X)
    (hXbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1)
    {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hbbound : ∀ t ω, b t ω ∈ Icc (0 : ℝ) 1)
    {u v : ℝ} (huv : u ≤ v) {A : Set Ω}
    (hA : ∀ t ∈ Icc u v, MeasurableSet[m t] A)
    (hpost : ∀ t ∈ Icc u v, b t =ᵐ[P] P[X | m t]) :
    ∫ ω in A, (∫ t in u..v, (X ω - b t ω)) ∂P = 0 := by
  have hXi : Integrable X P := integrable_of_mem_Icc hX hXbound
  have hbi (t : ℝ) : Integrable (b t) P :=
    integrable_of_mem_Icc hb.of_uncurry_left (hbbound t)
  have : IsFiniteMeasure (volume.restrict (uIoc u v)) := ⟨by simp⟩
  have hint : Integrable
      (Function.uncurry fun t ω => X ω - b t ω)
      ((volume.restrict (uIoc u v)).prod (P.restrict A)) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((hX.comp measurable_snd).sub hb).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖X p.2 - b p.1 p.2‖ ≤ 1
      rw [Real.norm_eq_abs, abs_le]
      have hx := hXbound p.2
      have hbt := hbbound p.1 p.2
      constructor <;> linarith [hx.1, hx.2, hbt.1, hbt.2]
  rw [← intervalIntegral_integral_swap hint]
  apply intervalIntegral.integral_zero_ae
  exact Filter.Eventually.of_forall fun t ht => by
    have ht' : t ∈ Icc u v := by
      rw [uIoc_of_le huv] at ht
      exact ⟨ht.1.le, ht.2⟩
    rw [integral_sub hXi.restrict (hbi t).restrict]
    rw [posterior_setIntegral (hm t) hXi (hA t ht') (hpost t ht')]
    exact sub_self _

theorem integrable_correction_prod
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    {ν : Measure T} [IsFiniteMeasure ν]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : Measurable X)
    {b : T → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hXbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1)
    (hbbound : ∀ t ω, b t ω ∈ Icc (0 : ℝ) 1) :
    Integrable (Function.uncurry fun t ω => X ω - b t ω) (ν.prod P) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((hX.comp measurable_snd).sub hb).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖X p.2 - b p.1 p.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_le]
    have hx := hXbound p.2
    have hbt := hbbound p.1 p.2
    constructor <;> linarith [hx.1, hx.2, hbt.1, hbt.2]

theorem integrable_intervalCorrection
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : Measurable X)
    {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hXbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1)
    (hbbound : ∀ t ω, b t ω ∈ Icc (0 : ℝ) 1)
    {u v : ℝ} (huv : u ≤ v) :
    Integrable (fun ω => ∫ t in u..v, (X ω - b t ω)) P := by
  have hint := integrable_correction_prod (ν := volume.restrict (Ioc u v))
    (P := P) hX hb hXbound hbbound
  simpa only [intervalIntegral.integral_of_le huv, Function.uncurry_apply_pair]
    using hint.integral_prod_right

theorem condExp_intervalCorrection_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P]
    {m : ℝ → MeasurableSpace Ω} (hm : ∀ t, m t ≤ mΩ)
    (hmono : Monotone m)
    {X : Ω → ℝ} (hX : Measurable X)
    (hXbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1)
    {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hbbound : ∀ t ω, b t ω ∈ Icc (0 : ℝ) 1)
    {u v : ℝ} (huv : u ≤ v)
    (hpost : ∀ t ∈ Icc u v, b t =ᵐ[P] P[X | m t]) :
    P[(fun ω => ∫ t in u..v, (X ω - b t ω)) | m u] =ᵐ[P] 0 := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq (hm u)
    (integrable_intervalCorrection hX hb hXbound hbbound huv)
    (g := (0 : Ω → ℝ)) ?_ ?_ ?_).symm
  · intro A _ _
    exact integrable_zero _ _ _
  · intro A hA _
    simp only [Pi.zero_apply, integral_zero]
    symm
    exact setIntegral_intervalIntegral_posterior_sub_eq_zero hm hX hXbound hb hbbound huv
      (fun t ht => hmono ht.1 A hA) hpost
  · exact stronglyMeasurable_zero.aestronglyMeasurable

theorem condExp_noise_add_intervalCorrection_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P]
    {m : ℝ → MeasurableSpace Ω} (hm : ∀ t, m t ≤ mΩ)
    (hmono : Monotone m)
    {X : Ω → ℝ} (hX : Measurable X)
    (hXbound : ∀ ω, X ω ∈ Icc (0 : ℝ) 1)
    {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hbbound : ∀ t ω, b t ω ∈ Icc (0 : ℝ) 1)
    {u v : ℝ} (huv : u ≤ v)
    (hpost : ∀ t ∈ Icc u v, b t =ᵐ[P] P[X | m t])
    {N : Ω → ℝ} (hNi : Integrable N P)
    (hN : P[N | m u] =ᵐ[P] 0) :
    P[(fun ω => N ω + ∫ t in u..v, (X ω - b t ω)) | m u] =ᵐ[P] 0 := by
  have hc := condExp_intervalCorrection_eq_zero hm hmono hX hXbound hb hbbound huv hpost
  have hci := integrable_intervalCorrection (P := P) hX hb hXbound hbbound huv
  have hadd := condExp_add hNi hci (m u)
  have heq : (fun ω => N ω + ∫ t in u..v, (X ω - b t ω)) =
      N + (fun ω => ∫ t in u..v, (X ω - b t ω)) := by
    funext ω
    rfl
  rw [heq]
  filter_upwards [hadd, hN, hc] with ω ha hn hcω
  exact ha.trans (by simp only [Pi.add_apply, Pi.zero_apply, hn, hcω, zero_add])

end Problem336.InnovationMean

end

end OAI
