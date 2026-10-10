import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaLimit
import OAI.NumberTheory.PrimePackets.DisintegrationEntropy

namespace OAI

/-! # Integrable pointwise information of finite observations -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

def observationInformation {Y α : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (P : Y → α) (y : Y) : ℝ :=
  -Real.log (ν.real {z | P z=P y})

theorem observationInformation_integrable {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (ν : Measure Y) [IsFiniteMeasure ν] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) : Integrable (observationInformation ν P) ν :=
  integrable_finite_values ν P hP (fun a => -Real.log (ν.real {z | P z=a}))

theorem integral_observationInformation {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (ν : Measure Y) [IsFiniteMeasure ν] (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y=a}) :
    ∫ y, observationInformation ν P y ∂ν = observationEntropy ν P := by
  calc
    _ = ∑ a, ν.real {y | P y=a} * -Real.log (ν.real {z | P z=a}) :=
      integral_finite_values ν P hP (fun a => -Real.log (ν.real {z | P z=a}))
    _ = _ := by
      unfold observationEntropy finiteShannon
      apply Finset.sum_congr rfl
      intro a _
      simp only [Real.negMulLog_def,neg_mul,mul_neg]

lemma observationInformation_nonneg {Y α : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (P : Y → α) (y : Y) :
    0 ≤ observationInformation ν P y := by
  exact neg_nonneg.mpr (Real.log_nonpos measureReal_nonneg measureReal_le_one)

lemma measurable_kernel_observationInformation {S T α : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [Fintype α]
    (κ : Kernel S T) [IsMarkovKernel κ] (P : S × T → α)
    (hP : ∀ a, MeasurableSet {z | P z=a}) :
    Measurable (fun z : S × T => observationInformation (κ z.1) (fun t => P (z.1,t)) z.2) := by
  classical
  have he (z : S × T) :
      observationInformation (κ z.1) (fun t => P (z.1,t)) z.2 =
        ∑ a, {z | P z=a}.indicator
          (fun z => -Real.log ((κ z.1).real {t | P (z.1,t)=a})) z := by
    rw [Finset.sum_eq_single (P z)]
    · simp [observationInformation]
    · intro a _ ha
      exact indicator_of_notMem (show z ∉ {z | P z=a} from Ne.symm ha) _
    · simp
  simp_rw [he]
  apply Finset.measurable_sum
  intro a _
  have hm := (Kernel.measurable_kernel_prodMk_left (κ := κ) (hP a)).ennreal_toReal
  exact (hm.log.neg.comp measurable_fst).indicator (hP a)

theorem integrable_kernel_observationInformation {S T α : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [Fintype α]
    (σ : Measure S) [IsFiniteMeasure σ] (κ : Kernel S T) [IsMarkovKernel κ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z=a}) :
    Integrable (fun z : S × T => observationInformation (κ z.1) (fun t => P (z.1,t)) z.2)
      (σ ⊗ₘ κ) := by
  apply (Measure.integrable_compProd_iff
    (measurable_kernel_observationInformation κ P hP).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun s => observationInformation_integrable (κ s) _
      (fun a => (hP a).preimage measurable_prodMk_left)
  · have he (s : S) :
        (∫ t, ‖observationInformation (κ s) (fun t => P (s,t)) t‖ ∂κ s) =
          observationEntropy (κ s) (fun t => P (s,t)) := by
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (observationInformation_nonneg (κ s) _ _)]
      exact integral_observationInformation (κ s) _
        (fun a => (hP a).preimage measurable_prodMk_left)
    simp_rw [he]
    apply (integrable_const (Fintype.card α : ℝ)).mono'
      (measurable_fiber_observationEntropy κ P hP).aestronglyMeasurable
    exact ae_of_all _ fun s => finiteShannon_norm_le_card_of_unit_bounds _
      (fun _ => ⟨measureReal_nonneg,measureReal_le_one⟩)

theorem conditionalEntropy_fst_information {S T α : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T] [Fintype α]
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    (P : S × T → α) (hP : ∀ a, MeasurableSet {z | P z=a}) :
    conditionalSigmaEntropy ρ P
        (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S)) =
      ∫ z, observationInformation (ρ.condKernel z.1) (fun t => P (z.1,t)) z.2 ∂ρ := by
  rw [conditionalSigmaEntropy_fst ρ P hP]
  have H := Measure.integral_compProd
    (integrable_kernel_observationInformation ρ.fst ρ.condKernel P hP)
  rw [Measure.disintegrate] at H
  refine (integral_congr_ae (ae_of_all _ fun s => ?_)).trans H.symm
  exact (integral_observationInformation (ρ.condKernel s) _
    (fun a => (hP a).preimage measurable_prodMk_left)).symm

end DukePrimeDegree

end

end OAI
