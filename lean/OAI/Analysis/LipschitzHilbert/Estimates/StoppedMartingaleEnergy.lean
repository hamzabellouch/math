import OAI.Analysis.LipschitzHilbert.Estimates.MartingaleMaximalL2
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

namespace OAI

/-! Exact quadratic energy for increasing bounded stopping times.
This supplies the jump-count energy in the scalar variation argument. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem conditionalExpectation_square_difference (m' : MeasurableSpace Ω) (hm : m'≤m)
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgm : AEStronglyMeasurable[m'] g μ) (hcond : μ[f|m']=ᵐ[μ] g) :
    (∫ x, (f x-g x)^2 ∂μ)=(∫ x, f x^2 ∂μ)-(∫ x, g x^2 ∂μ) := by
  have hprod : Integrable (g*f) μ := hg.integrable_mul hf
  have hinner : (∫ x, g x*f x ∂μ)=∫ x, g x^2 ∂μ := by
    change (∫ x, (g*f) x ∂μ)=_
    rw [←integral_condExp hm (f:=g*f)]
    apply integral_congr_ae
    filter_upwards [condExp_mul_of_aestronglyMeasurable_left hgm hprod
      (hf.integrable (by norm_num)),hcond] with x hx hcx
    rw [hx]
    change g x*(μ[f|m']) x=g x^2
    rw [hcx]
    ring
  have he (x : Ω) : (f x-g x)^2=(f x^2+g x^2)-2*(g x*f x) := by ring
  simp_rw [he]
  change (∫ x, ((fun x => f x^2)+(fun x => g x^2)) x-2*(g*f) x ∂μ)=_
  rw [integral_sub (hf.integrable_sq.add hg.integrable_sq) (hprod.const_mul 2)]
  simp only [Pi.add_apply,Pi.mul_apply]
  rw [integral_add hf.integrable_sq hg.integrable_sq,integral_const_mul,hinner]
  ring

theorem martingale_square_difference {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}
    (hF : Martingale F ℱ μ) (hF2 : ∀ n, MemLp (F n) 2 μ)
    (i j : ℕ) (hij : i≤j) :
    (∫ x, (F j x-F i x)^2 ∂μ)=(∫ x, F j x^2 ∂μ)-(∫ x, F i x^2 ∂μ) :=
  conditionalExpectation_square_difference (ℱ i) (ℱ.le i) (F j) (F i) (hF2 j) (hF2 i)
    (hF.stronglyMeasurable i).aestronglyMeasurable (hF.condExp_ae_eq hij)

theorem stopped_martingale_square_difference {ℱ : Filtration ℕ m} {F : ℕ → Ω → ℝ}
    (hF : Martingale F ℱ μ) (hF2 : ∀ n, MemLp (F n) 2 μ)
    (σ τ : Ω → WithTop ℕ) (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ≤τ) (N : ℕ) (hτN : ∀ x, τ x≤N) :
    (∫ x, (stoppedValue F τ x-stoppedValue F σ x)^2 ∂μ)=
      (∫ x, (stoppedValue F τ x)^2 ∂μ)-(∫ x, (stoppedValue F σ x)^2 ∂μ) := by
  have hσN (x : Ω) : σ x≤N := (hστ x).trans (hτN x)
  have hσ2 := memLp_stoppedValue hσ hF2 hσN
  have hτ2 := memLp_stoppedValue hτ hF2 hτN
  have hσcond := hF.stoppedValue_ae_eq_condExp_of_le_const hσ hσN
  have hσm : AEStronglyMeasurable[hσ.measurableSpace] (stoppedValue F σ) μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr hσcond.symm
  exact conditionalExpectation_square_difference hσ.measurableSpace hσ.measurableSpace_le
    (stoppedValue F τ) (stoppedValue F σ) hτ2 hσ2 hσm
    (hF.stoppedValue_ae_eq_condExp_of_le hτ hσ hστ hτN).symm

end LipschitzHilbert

end

end OAI
