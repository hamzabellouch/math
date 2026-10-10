import OAI.InformationTheory.Entanglement.DensityChange
import OAI.InformationTheory.Entanglement.MatrixFamilyDensity

namespace OAI

noncomputable section
open MeasureTheory Matrix Filter
open scoped MeasureTheory BigOperators ComplexOrder MatrixOrder Kronecker
namespace SecretKey
open ChannelCompletion
variable {Ω : Type*} [MeasurableSpace Ω] {n : Type} [Fintype n]
namespace PositiveMatrixMeasure
lemma density_unique (W : PositiveMatrixMeasure Ω n) {μ : Measure Ω} [IsFiniteMeasure μ]
    (hW : W.traceMeasure≪μ) (D : Ω → Mat n)
    (hDi : ∀ a b, Integrable (fun t => D t a b) μ)
    (hDs : ∀ s, MeasurableSet s → ∀ a b, (∫ t in s, D t a b ∂μ)=W.value s a b) :
    D =ᵐ[μ] W.positiveDensity μ := by
  have he (a b : n) : (fun t => D t a b)=ᵐ[μ](fun t => W.positiveDensity μ t a b) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (hDi a b) (W.positiveDensity_integrable hW a b)
    intro s hs _
    rw [hDs s hs,W.positiveDensity_setIntegral hW hs]
  filter_upwards [ae_all_iff.mpr fun a => ae_all_iff.mpr fun b => he a b] with t ht
  ext a b
  exact ht a b
lemma positiveDensity_change (W : PositiveMatrixMeasure Ω n) {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hW : W.traceMeasure≪μ) (hμν : μ≪ν) :
    (fun t => (densityWeight μ ν t : ℂ) • W.positiveDensity μ t)=ᵐ[ν] W.positiveDensity ν := by
  apply W.density_unique (hW.trans hμν)
  · intro a b
    simpa only [Matrix.smul_apply,smul_eq_mul,Complex.real_smul] using
      densityWeight_integrable μ ν hμν (W.positiveDensity_integrable hW a b)
  · intro s hs a b
    change (∫ t in s, (densityWeight μ ν t : ℂ)*W.positiveDensity μ t a b ∂ν)=_
    simpa only [Complex.real_smul] using
      (densityWeight_setIntegral μ ν hμν (fun t => W.positiveDensity μ t a b) hs).trans
        (W.positiveDensity_setIntegral hW hs a b)
end PositiveMatrixMeasure
lemma bitDistance_congr_ae {μ : Measure Ω}
    {A B : Fin 2 → Fin 2 → Ω → Mat n} {σ θ : Ω → Mat n}
    (hAB : ∀ i j, A i j=ᵐ[μ]B i j) (hστ : σ=ᵐ[μ]θ) :
    bitDistance A σ μ=bitDistance B θ μ := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [hAB i j,hστ] with t ht hs
  simp only [ht,idealDensity,hs]
variable [DecidableEq n]
lemma bitDistance_weight {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ≪ν) (A : Fin 2 → Fin 2 → Ω → Mat n) (σ : Ω → Mat n) :
    bitDistance (fun i j t => (densityWeight μ ν t : ℂ) • A i j t)
      (fun t => (densityWeight μ ν t : ℂ) • σ t) ν=bitDistance A σ μ := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he (t : Ω) : idealDensity (fun t => (densityWeight μ ν t : ℂ) • σ t) i j t=
      (densityWeight μ ν t : ℂ) • idealDensity σ i j t := by
    unfold idealDensity halfDensity
    split_ifs <;> simp only [smul_zero,smul_smul,mul_comm]
  simp only [he,← smul_sub]
  exact densityWeight_traceNorm_integral μ ν hμν (fun t => A i j t-idealDensity σ i j t)

theorem bitLawDistance_change (A : Fin 2 → Fin 2 → PositiveMatrixMeasure Ω n)
    (σ : PositiveMatrixMeasure Ω n) {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hA : ∀ i j, (A i j).traceMeasure≪μ) (hσ : σ.traceMeasure≪μ) (hμν : μ≪ν) :
    bitDistance (fun i j => (A i j).positiveDensity ν) (σ.positiveDensity ν) ν=
      bitDistance (fun i j => (A i j).positiveDensity μ) (σ.positiveDensity μ) μ := by
  rw [← bitDistance_weight hμν]
  exact bitDistance_congr_ae (fun i j => ((A i j).positiveDensity_change (hA i j) hμν).symm)
    (σ.positiveDensity_change hσ hμν).symm

end SecretKey

end

end OAI
