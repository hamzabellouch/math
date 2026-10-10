import OAI.Probability.FreeIsing.Gaussian.BinaryRegression

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

theorem condExp_condExp_eq_of_separator
    {Ω Z W : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mZ : MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [mW : MeasurableSpace W]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω → Z} {T : Ω → W} {g : Ω → ℝ}
    (hS : Measurable S) (hT : Measurable T)
    (hg : Measurable g) (hgi : Integrable g μ)
    (hind : CondIndepFun (mW.comap T) hT.comap_le S g μ) :
    μ[μ[g | mW.comap T] | mZ.comap S] =ᵐ[μ] μ[g | mZ.comap S] := by
  have hremove : μ[g | mZ.comap S ⊔ mW.comap T] =ᵐ[μ] μ[g | mW.comap T] := by
    simpa only [sup_comm] using condExp_sup_eq_of_condIndepFun hT hS hg hgi hind
  exact (condExp_congr_ae (m := mZ.comap S) hremove).symm.trans
    (condExp_condExp_of_le le_sup_left (sup_le hS.comap_le hT.comap_le))

theorem integral_mul_eq_endpoint_condExp_of_two_separators
    {Ω Z W : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mZ : MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    [mW : MeasurableSpace W]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Ω → Z} {T : Ω → W} {f g : Ω → ℝ}
    (hS : Measurable S) (hT : Measurable T)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hleft : CondIndepFun (mZ.comap S) hS.comap_le f g μ)
    (hright : CondIndepFun (mW.comap T) hT.comap_le S g μ) :
    (∫ ω, f ω * g ω ∂μ) =
      ∫ ω, μ[f | mZ.comap S] ω * μ[g | mW.comap T] ω ∂μ := by
  have hfi := hf2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hgi := hg2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hreg := condExp_condExp_eq_of_separator hS hT hg hgi hright
  have hfs : MemLp (μ[f | mZ.comap S]) 2 μ := hf2.condExp (by norm_num)
  have hgt : MemLp (μ[g | mW.comap T]) 2 μ := hg2.condExp (by norm_num)
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (μ := μ) (m := mZ.comap S)
    (f := μ[f | mZ.comap S]) (g := μ[g | mW.comap T])
    stronglyMeasurable_condExp (hfs.integrable_mul hgt) integrable_condExp
  have hint := integral_congr_ae hpull
  rw [integral_condExp hS.comap_le] at hint
  calc
    (∫ ω, f ω * g ω ∂μ) =
        ∫ ω, μ[f | mZ.comap S] ω * μ[g | mZ.comap S] ω ∂μ :=
      integral_mul_eq_integral_condExp_mul_of_condIndepFun hS.comap_le hleft hf hg
        hfi hgi (hf2.integrable_mul hg2)
    _ = ∫ ω, μ[f | mZ.comap S] ω * μ[μ[g | mW.comap T] | mZ.comap S] ω ∂μ :=
      integral_congr_ae (Filter.EventuallyEq.rfl.mul hreg.symm)
    _ = _ := hint.symm

theorem BinaryRegression.abs_correlation_le_of_two_separators
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S T : Ω → IsingSpin}
    (hS : Measurable S) (hT : Measurable T)
    (hSfair : ∀ s : IsingSpin, μ {ω | S ω = s} = ENNReal.ofReal (1/2 : ℝ))
    (hTfair : ∀ s : IsingSpin, μ {ω | T ω = s} = ENNReal.ofReal (1/2 : ℝ))
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfzero : ∫ ω, f ω ∂μ = 0) (hgzero : ∫ ω, g ω ∂μ = 0)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hleft : CondIndepFun (isingSpinMeasurable.comap S) hS.comap_le f g μ)
    (hright : CondIndepFun (isingSpinMeasurable.comap T) hT.comap_le S g μ) :
    |∫ ω, f ω * g ω ∂μ| ≤
      Real.sqrt (∫ ω, (f ω)^2 ∂μ) * Real.sqrt (∫ ω, (g ω)^2 ∂μ) *
        |∫ ω, spinSign (S ω) * spinSign (T ω) ∂μ| := by
  let : Nonempty IsingSpin := ⟨IsingSpin.neg⟩
  exact abs_correlation_le_of_binary_condExp hS hT hSfair hTfair hfzero hgzero
    hf2.integrable_sq hg2.integrable_sq
    (integral_mul_eq_endpoint_condExp_of_two_separators hS hT hf hg hf2 hg2 hleft hright)

end Problem367

end

end OAI
