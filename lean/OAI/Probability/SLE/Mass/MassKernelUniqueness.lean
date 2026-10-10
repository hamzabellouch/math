import OAI.Probability.SLE.Mass.MassMartingaleUniqueness

namespace OAI

/-! Equal terminal remainder kernels yield a martingale difference; continuity
and increasing integrable masses then imply uniqueness. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

namespace SLEExactGauge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma mass_difference_martingale_of_terminal_mean
    (A B : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ) (hZ : Integrable Z P)
    (hAm : StronglyAdapted ℱ A) (hBm : StronglyAdapted ℱ B)
    (hAI : ∀ t, Integrable (A t) P) (hBI : ∀ t, Integrable (B t) P)
    (hmean : ∀ t E, MeasurableSet[ℱ t] E →
      (∫ ω in E, A t ω-B t ω ∂P) = ∫ ω in E, Z ω ∂P) :
    Martingale (fun t ω => A t ω-B t ω) ℱ P := by
  have he (t : ℝ≥0) : (fun ω => A t ω-B t ω) =ᵐ[P] P[Z | ℱ t] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le t) hZ
      (fun E _ _ => ((hAI t).sub (hBI t)).integrableOn)
      (fun E hE _ => hmean t E hE)
    exact ((hAm t).sub (hBm t)).aestronglyMeasurable
  exact (martingale_condExp Z ℱ P).congr (hAm.sub hBm)
    (fun t => (he t).symm)

theorem increasing_mass_unique_of_terminal_mean
    (A B : ℝ≥0 → Ω → ℝ) (Z : Ω → ℝ) (hZ : Integrable Z P)
    (hAm : StronglyAdapted ℱ A) (hBm : StronglyAdapted ℱ B)
    (hAI : ∀ t, Integrable (A t) P) (hBI : ∀ t, Integrable (B t) P)
    (hmean : ∀ t E, MeasurableSet[ℱ t] E →
      (∫ ω in E, A t ω-B t ω ∂P) = ∫ ω in E, Z ω ∂P)
    (hA : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hB : ∀ᵐ ω ∂P, Monotone (fun t => B t ω))
    (hA0 : A 0 =ᵐ[P] 0) (hB0 : B 0 =ᵐ[P] 0)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => A t ω-B t ω)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = B t ω :=
  increasing_mass_martingale_indistinguishable A B
    (mass_difference_martingale_of_terminal_mean A B Z hZ hAm hBm hAI hBI hmean)
    hA hB hA0 hB0 hAI hBI hcont

end SLEExactGauge

end

end OAI
