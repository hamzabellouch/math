import OAI.NumberTheory.DukePrimeDegree.Entropy.ObservationInformation

namespace OAI

/-! # Conditional entropy as the mean pointwise information

The finite observed variable has a regular conditional distribution even
when the conditioning sigma algebra is arbitrary. Lifting its underlying
space keeps the ambient and conditioning measurable structures distinct.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

def conditionalInformation {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (P : Y → α) (m : MeasurableSpace Y) (y : Y) : ℝ :=
  -Real.log ((μ[({z | P z=P y}.indicator (fun _ => (1:ℝ))) | m]) y)

theorem conditionalInformation_integrable_integral {Y : Type*} (m : MeasurableSpace Y)
    [mY : MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {N : ℕ} [NeZero N]
    (P : Y → Fin N) (hP : Measurable P) (hm : m ≤ mY) :
    Integrable (conditionalInformation μ P m) μ ∧
      (∫ y, conditionalInformation μ P m y ∂μ) = conditionalSigmaEntropy μ P m := by
  let : MeasurableSpace (ULift.{0} Y) := m.comap ULift.down
  let X : Y → ULift.{0} Y := ULift.up
  have hmX : MeasurableSpace.comap X (inferInstance : MeasurableSpace (ULift.{0} Y)) = m := by
    change (m.comap ULift.down).comap ULift.up = m
    rw [MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_id
  have hX : Measurable X := by
    apply Measurable.of_comap_le
    simpa only [hmX] using hm
  let σ := μ.map (fun y => (X y,P y))
  let κ := σ.condKernel
  have hκ : condDistrib P X μ = κ := by rw [condDistrib]
  have heq (a : Fin N) :
      μ[({z | P z=a}.indicator (fun _ => (1:ℝ))) | m] =ᵐ[μ]
        fun y => (κ (X y)).real {a} := by
    have H := condExp_ae_eq_integral_condDistrib (μ := μ) (X := X) (Y := P)
      hX hP.aemeasurable
      ((stronglyMeasurable_const.indicator (measurableSet_singleton a)) :
        StronglyMeasurable (({a} : Set (Fin N)).indicator (fun _ : Fin N => (1:ℝ))))
      ((integrable_const (1:ℝ)).indicator (hP (measurableSet_singleton a)))
    rw [hκ,hmX] at H
    have hleft : (fun y => ({a} : Set (Fin N)).indicator (fun _ => (1:ℝ)) (P y)) =
        {z | P z=a}.indicator (fun _ => (1:ℝ)) := by
      funext y
      simp only [Set.indicator_apply,Set.mem_singleton_iff,Set.mem_ofPred_eq]
    simpa only [hleft,integral_indicator_const (1:ℝ) (measurableSet_singleton a),
      smul_eq_mul,mul_one] using H
  let I : ULift.{0} Y × Fin N → ℝ :=
    fun z => observationInformation (κ z.1) (id : Fin N → Fin N) z.2
  have hI : Measurable I := measurable_kernel_observationInformation κ Prod.snd
    (fun a => measurable_snd (measurableSet_singleton a))
  have hIp : conditionalInformation μ P m =ᵐ[μ] fun y => I (X y,P y) := by
    filter_upwards [ae_all_iff.mpr heq] with y hy
    unfold conditionalInformation I observationInformation
    rw [hy (P y)]
    rfl
  have hIint : Integrable I σ := by
    have H := integrable_kernel_observationInformation σ.fst κ Prod.snd
      (fun a => measurable_snd (measurableSet_singleton a))
    change Integrable I (σ.fst ⊗ₘ σ.condKernel) at H
    rwa [Measure.disintegrate] at H
  have hIf : Integrable (fun y => I (X y,P y)) μ :=
    hIint.comp_measurable (hX.prodMk hP)
  refine ⟨hIf.congr hIp.symm,?_⟩
  rw [integral_congr_ae hIp]
  have HI := conditionalEntropy_fst_information σ Prod.snd
    (fun a => measurable_snd (measurableSet_singleton a))
  rw [conditionalSigmaEntropy_fst σ Prod.snd
    (fun a => measurable_snd (measurableSet_singleton a))] at HI
  have HE : conditionalSigmaEntropy μ P m =
      ∫ y, observationEntropy (κ (X y)) (id : Fin N → Fin N) ∂μ := by
    unfold conditionalSigmaEntropy observationEntropy
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr heq] with y hy
    congr 1
    funext a
    simpa only [id_eq,Set.ofPred_eq_eq_singleton] using hy a
  rw [HE]
  calc
    _ = ∫ z, I z ∂σ :=
      (integral_map (hX.prodMk hP).aemeasurable hI.aestronglyMeasurable).symm
    _ = ∫ s, observationEntropy (κ s) (id : Fin N → Fin N) ∂σ.fst := HI.symm
    _ = ∫ z, observationEntropy (κ z.1) (id : Fin N → Fin N) ∂σ :=
      integral_map measurable_fst.aemeasurable
        (measurable_fiber_observationEntropy κ Prod.snd
          (fun a => measurable_snd (measurableSet_singleton a))).aestronglyMeasurable
    _ = _ := integral_map (hX.prodMk hP).aemeasurable
      ((measurable_fiber_observationEntropy κ Prod.snd
        (fun a => measurable_snd (measurableSet_singleton a))).comp measurable_fst).aestronglyMeasurable

end DukePrimeDegree

end

end OAI
