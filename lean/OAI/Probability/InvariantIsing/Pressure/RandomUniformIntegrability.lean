import OAI.Probability.InvariantIsing.Pressure.RandomPressureProbability
import Mathlib.MeasureTheory.Function.UniformIntegrable

namespace OAI

/-! The uniform-integrability conclusion of Proposition gen:random. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace InvariantIsing

lemma uniformIntegrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Z : ℕ → Ω → ℝ) (hX : ∀ n, AEStronglyMeasurable (X n) P)
    (hZ : UniformIntegrable Z 1 P) (hXZ : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ |Z n ω|) :
    UniformIntegrable X 1 P := by
  have hd n : (fun ω => ‖X n ω‖ₑ) ≤ᵐ[P] (fun ω => ‖Z n ω‖ₑ) :=
    (hXZ n).mono fun ω hω => by
      simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hω
  refine ⟨hZ.1.ae_mono hX hd,?_⟩
  obtain ⟨C,hC⟩ := hZ.2
  exact ⟨C,fun n => (eLpNorm_mono_enorm_ae (hX n) (hd n)).trans (hC n)⟩

lemma pressure_L1_of_probability_and_uniformIntegrability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (L : ℝ) (hUI : UniformIntegrable X 1 P)
    (hprob : TendstoInMeasure P X atTop (fun _ => L)) :
    Tendsto (fun n => eLpNorm (fun ω => X n ω-L) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 L) := by
  have hL := tendsto_Lp_finite_of_tendstoInMeasure (p := 1) le_rfl (by simp)
    hUI.aestronglyMeasurable (memLp_const L) hUI.1 hprob
  refine ⟨hL,?_⟩
  have hh := tendsto_integral_of_L1' (fun _ : Ω => L)
    (Filter.Eventually.of_forall fun n => (memLp_one_iff_integrable.mp (hUI.memLp n))) hL
  simpa only [integral_const,probReal_univ,one_smul] using hh

end InvariantIsing

end

end OAI
