import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditioningFiniteLabels
import OAI.NumberTheory.PrimePackets.DisintegrationEntropy

namespace OAI

/-! # Conditional entropy after recording a transverse coordinate and label -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [StandardBorelSpace T] [Nonempty T]

lemma condExp_transverse_label_probability {M N : ℕ}
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {P : S × T → Fin M} (hP : Measurable P)
    {Q : S × T → Fin N} (hQ : Measurable Q) (a : Fin M) :
    ρ[({z | P z=a}.indicator (fun _ => (1:ℝ))) |
        MeasurableSpace.comap (fun z => (z.1,Q z))
          (inferInstance : MeasurableSpace (S × Fin N))] =ᵐ[ρ]
      fun z => ((ρ.map (finiteLabelLift Q)).condKernel (z.1,Q z)).real
        {t | P (z.1,t)=a} := by
  let f : (S × Fin N) × T → ℝ :=
    {z | P (z.1.1,z.2)=a}.indicator (fun _ => 1)
  have hf : Integrable f (ρ.map (finiteLabelLift Q)) := by
    apply (integrable_const (1:ℝ)).indicator
    exact measurableSet_eq_fun (hP.comp (measurable_fst.fst.prodMk measurable_snd)) measurable_const
  have H := condExp_prod_ae_eq_integral_condDistrib'
    (μ := ρ) (X := fun z : S × T => (z.1,Q z)) (Y := Prod.snd)
    (measurable_fst.prodMk hQ) measurable_snd.aemeasurable hf
  have hκ : condDistrib (Prod.snd : S × T → T) (fun z => (z.1,Q z)) ρ =
      (ρ.map (finiteLabelLift Q)).condKernel := by
    rw [condDistrib]
    rfl
  rw [hκ] at H
  have hI (s : S × Fin N) : (∫ t, f (s,t) ∂(ρ.map (finiteLabelLift Q)).condKernel s) =
      ((ρ.map (finiteLabelLift Q)).condKernel s).real {t | P (s.1,t)=a} := by
    change (∫ t, {t | P (s.1,t)=a}.indicator (fun _ => (1:ℝ)) t
      ∂(ρ.map (finiteLabelLift Q)).condKernel s) = _
    have hs : MeasurableSet {t : T | P (s.1,t)=a} :=
      (hP (measurableSet_singleton a)).preimage measurable_prodMk_left
    rw [integral_indicator_const (1:ℝ) hs]
    simp only [smul_eq_mul,mul_one]
  have heq : (fun z : S × T => f ((z.1,Q z),z.2)) =
      {z | P z=a}.indicator (fun _ => (1:ℝ)) := by
    funext z
    rfl
  simpa only [heq,hI] using H

theorem conditionalEntropy_transverse_label {M N : ℕ}
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {P : S × T → Fin M} (hP : Measurable P)
    {Q : S × T → Fin N} (hQ : Measurable Q) :
    conditionalSigmaEntropy ρ P
        (MeasurableSpace.comap (fun z => (z.1,Q z))
          (inferInstance : MeasurableSpace (S × Fin N))) =
      ∫ z, observationEntropy
        ((ρ.map (finiteLabelLift Q)).condKernel (z.1,Q z)) (fun t => P (z.1,t)) ∂ρ := by
  unfold conditionalSigmaEntropy
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun a => condExp_transverse_label_probability ρ hP hQ a)]
    with z hz
  unfold observationEntropy
  congr 1
  exact funext hz

/-- The entropy is computed from the actual leaf kernel, restricted to
the observed fiber, with its measured normalization. -/
theorem conditionalEntropy_transverse_label_restriction {M N : ℕ}
    (ρ : Measure (S × T)) [IsFiniteMeasure ρ]
    {P : S × T → Fin M} (hP : Measurable P)
    {Q : S × T → Fin N} (hQ : Measurable Q) :
    conditionalSigmaEntropy ρ P
        (MeasurableSpace.comap (fun z => (z.1,Q z))
          (inferInstance : MeasurableSpace (S × Fin N))) =
      ∫ z, observationEntropy
        ((anchorNormalize (ρ.condKernel z.1) {t | Q (z.1,t)=Q z}).restrict
          {t | Q (z.1,t)=Q z}) (fun t => P (z.1,t)) ∂ρ := by
  rw [conditionalEntropy_transverse_label ρ hP hQ]
  apply integral_congr_ae
  filter_upwards [finiteLabelLift_condKernel ρ hQ] with z hz
  rw [hz.2]

end DukePrimeDegree

end

end OAI
