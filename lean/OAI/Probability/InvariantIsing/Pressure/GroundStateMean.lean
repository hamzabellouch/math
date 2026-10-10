import OAI.Probability.InvariantIsing.Pressure.GroundStateFinite

namespace OAI

/-! Integrable physical energies and the expected soft-maximum inequality. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators

namespace InvariantIsing

lemma integrable_physicalPressure {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → Orthogonal N) (hU : Measurable U) (eig c : Fin N → ℝ) :
    Integrable (fun ω => rotatedPressure eig (matrixRotation (U ω)⁻¹) c) P := by
  let K := ∑ i, |eig i|
  have he i : |eig i| ≤ K := Finset.single_le_sum (f := fun i => |eig i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  apply (integrable_const (K/2+|noninteractingPressure c|)).mono'
    ((measurable_physicalPressure hN eig c).comp hU).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  have hb := abs_pressure_sub_noninteracting_le hN eig c (matrixRotation (U ω)⁻¹) K he
  have ha := abs_add_le (rotatedPressure eig (matrixRotation (U ω)⁻¹) c-noninteractingPressure c)
    (noninteractingPressure c)
  rw [sub_add_cancel] at ha
  exact ha.trans (add_le_add hb le_rfl)

lemma integrable_physicalGroundState {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → Orthogonal N) (hU : Measurable U) (eig : Fin N → ℝ) :
    Integrable (fun ω => groundStateEnergy eig (matrixRotation (U ω)⁻¹)) P := by
  let K := ∑ i, |eig i|
  have he i : |eig i| ≤ K := Finset.single_le_sum (f := fun i => |eig i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  exact (integrable_const (K/2)).mono'
    ((measurable_physical_groundStateEnergy hN eig).comp hU).aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using
      abs_groundStateEnergy_le hN eig (matrixRotation (U ω)⁻¹) K he)

lemma mean_groundState_squeeze {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → Orthogonal N) (hU : Measurable U) (eig : Fin N → ℝ)
    (β : ℝ) (hβ : 0 < β) :
    (∫ ω, rotatedPressure (fun i => β*eig i) (matrixRotation (U ω)⁻¹) (fun _ => 0) ∂P)/β ≤
      (∫ ω, groundStateEnergy eig (matrixRotation (U ω)⁻¹) ∂P) ∧
    (∫ ω, groundStateEnergy eig (matrixRotation (U ω)⁻¹) ∂P) ≤
      (∫ ω, rotatedPressure (fun i => β*eig i) (matrixRotation (U ω)⁻¹) (fun _ => 0) ∂P)/β+
        Real.log 2/β := by
  have hp := integrable_physicalPressure hN P U hU (fun i => β*eig i) (fun _ => 0)
  have hg := integrable_physicalGroundState hN P U hU eig
  have hl := integral_mono (hp.div_const β) hg (fun ω =>
    (groundStateEnergy_squeeze hN eig (matrixRotation (U ω)⁻¹) β hβ).1)
  have hu := integral_mono hg ((hp.div_const β).add (integrable_const (Real.log 2/β))) (fun ω =>
    (groundStateEnergy_squeeze hN eig (matrixRotation (U ω)⁻¹) β hβ).2)
  rw [integral_div] at hl
  simp only [Pi.add_apply] at hu
  rw [integral_add (hp.div_const β) (integrable_const _),integral_div,integral_const,
    probReal_univ,one_smul] at hu
  exact ⟨hl,hu⟩

end InvariantIsing

end

end OAI
