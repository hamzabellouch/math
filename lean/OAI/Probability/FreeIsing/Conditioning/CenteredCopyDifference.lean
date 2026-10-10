import OAI.Probability.FreeIsing.Conditioning.CopyDifference
import OAI.Probability.FreeIsing.Spectral.KoopmanInvolutions
import OAI.Probability.FreeIsing.Spectral.SpectralClosure

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367.CopyDifference

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ]
variable {p q : B → A}

lemma inner_const_one_self :
    inner ℝ (Lp.const 2 μ (1 : ℝ)) (Lp.const 2 μ (1 : ℝ)) = 1 := by
  rw [inner_const_one_eq_integral]
  calc
    (∫ x, Lp.const 2 μ (1 : ℝ) x ∂μ) = ∫ _ : A, (1 : ℝ) ∂μ :=
      integral_congr_ae (Lp.coeFn_const 2 μ (1 : ℝ))
    _ = 1 := by simp

lemma centered_source_cover
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ) :
    ∀ f : Lp ℝ 2 μ, ∃ z ∈ centeredL2 μ, operator hp hq z = operator hp hq f := by
  apply SpectralClosure.source_cover_of_kills_direction (operator hp hq)
    (innerSL ℝ (Lp.const 2 μ (1 : ℝ))) (Lp.const 2 μ (1 : ℝ))
  · exact inner_const_one_self
  · exact operator_eq_zero_of_ae_const hp hq _ 1 (Lp.coeFn_const 2 μ (1 : ℝ))

lemma rangeClosure_centered_eq
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ) :
    rangeClosure ((operator hp hq).domRestrict (centeredL2 μ)) =
      rangeClosure (operator hp hq) := by
  exact SpectralClosure.rangeClosure_domRestrict_eq (operator hp hq) (centeredL2 μ)
    (centered_source_cover hp hq)

lemma norm_restrict_le_of_centered_source
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (S : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hS : ∀ f ∈ centeredL2 μ, S f ∈ centeredL2 μ)
    (hT : IsSelfAdjoint T)
    (hcomm : ∀ f, T (operator hp hq f) = operator hp hq (S f))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hbound : ‖S.restrict hS‖ ≤ ρ) :
    ‖restrictToRangeClosure (operator hp hq) S T hcomm‖ ≤ ρ := by
  exact SpectralClosure.norm_restrict_le_of_source_subspace S T (operator hp hq)
    (centeredL2 μ) hS hT hcomm (centered_source_cover hp hq) hρ hbound

section Averaging

variable {ι : Type*} [Fintype ι]

omit [IsProbabilityMeasure μ] in

lemma average_intertwines_apply
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (τ : ι → A → A) (σ : ι → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q)
    (f : Lp ℝ 2 μ) :
    koopmanAverage σ hσ (operator hp hq f) = operator hp hq (koopmanAverage τ hτ f) := by
  simp only [koopmanAverage, smul_apply, sum_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν => L f)
    (intertwines hp hq (hτ i) (hσ i) (hpc i) (hqc i))

def averageOnDifferences
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (τ : ι → A → A) (σ : ι → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q) :
    rangeClosure (operator hp hq) →L[ℝ] rangeClosure (operator hp hq) :=
  restrictToRangeClosure (operator hp hq) (koopmanAverage τ hτ) (koopmanAverage σ hσ)
    (average_intertwines_apply hp hq τ σ hτ hσ hpc hqc)

omit [IsProbabilityMeasure μ] in
lemma averageOnDifferences_isSelfAdjoint
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (τ : ι → A → A) (σ : ι → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hσinv : ∀ i, Function.Involutive (σ i))
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q) :
    IsSelfAdjoint (averageOnDifferences hp hq τ σ hτ hσ hpc hqc) :=
  isSelfAdjoint_restrictToRangeClosure _ _ _
    (average_intertwines_apply hp hq τ σ hτ hσ hpc hqc)
    (koopmanAverage_selfAdjoint σ hσ hσinv)

lemma norm_averageOnDifferences_le
    (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
    (τ : ι → A → A) (σ : ι → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hτinv : ∀ i, Function.Involutive (τ i))
    (hσinv : ∀ i, Function.Involutive (σ i))
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hbound : ‖centeredKoopmanAverage τ hτ hτinv‖ ≤ ρ) :
    ‖averageOnDifferences hp hq τ σ hτ hσ hpc hqc‖ ≤ ρ := by
  exact norm_restrict_le_of_centered_source hp hq (koopmanAverage τ hτ)
    (koopmanAverage σ hσ) (koopmanAverage_preserves_centered τ hτ hτinv)
    (koopmanAverage_selfAdjoint σ hσ hσinv)
    (average_intertwines_apply hp hq τ σ hτ hσ hpc hqc) hρ hbound

end Averaging

end Problem367.CopyDifference

end

end OAI
