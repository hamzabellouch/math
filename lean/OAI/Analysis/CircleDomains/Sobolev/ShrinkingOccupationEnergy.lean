import OAI.Analysis.CircleDomains.Probability.LocalizedSquareMass
import OAI.Analysis.CircleDomains.Probability.CodeLawMeasures

namespace OAI

/-! Mean occupation has no mass off the physical domain. Its square density
therefore has vanishing energy on collars shrinking to a dust fibre. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem square_density_null_of_density_null {Y : Type*} [MeasurableSpace Y]
    (σ : Measure Y) (g : Y → ℝ≥0∞) (hg : Measurable g)
    {A : Set Y} (hA : MeasurableSet A) (hz : (σ.withDensity g) A = 0) :
    (σ.withDensity (fun x => g x ^ 2)) A = 0 := by
  rw [withDensity_apply _ hA] at hz ⊢
  have he := (lintegral_eq_zero_iff hg).mp hz
  apply (lintegral_eq_zero_iff (hg.pow_const 2)).mpr
  filter_upwards [he] with x hx
  change g x ^ 2 = 0
  have hx' : g x = 0 := hx
  rw [hx', zero_pow (by decide : (2 : ℕ) ≠ 0)]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem meanCodeOccupation_compl (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (P : ProbabilityMeasure (BasePathCode d)) :
    meanCodeOccupation d P d.physicalDomainᶜ = 0 := by
  rw [meanCodeOccupation_apply d hU P hG.measurableSet.compl]
  have hz (Γ : BasePathCode d) : baseCodeOccupation d Γ d.physicalDomainᶜ = 0 :=
    dyadicPhysicalOccupation_compl d.domainEquiv hG d.basePoint (baseCodePhysicalPath d Γ)
  simp only [hz, lintegral_zero]

theorem tendsto_shrinking_occupation_energy (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (P : ProbabilityMeasure (BasePathCode d)) (σ : Measure Y)
    (g : Y → ℝ≥0∞) (hg : Measurable g)
    (hocc : meanCodeOccupation d P = σ.withDensity g)
    (henergy : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (A : ℕ → Set Y) (hA : ∀ n, MeasurableSet (A n)) (hanti : Antitone A)
    (hshrink : (⋂ n, A n) ⊆ d.physicalDomainᶜ) :
    Tendsto (fun n => ∫⁻ x in A n, g x ^ 2 ∂σ) atTop (𝓝 0) := by
  let ν := σ.withDensity (fun x => g x ^ 2)
  have hfin : IsFiniteMeasure ν := ⟨by
    simpa only [ν, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using henergy⟩
  have hz : ν d.physicalDomainᶜ = 0 :=
    square_density_null_of_density_null σ g hg hG.measurableSet.compl
      (hocc ▸ meanCodeOccupation_compl d hU hG P)
  have hint : ν (⋂ n, A n) = 0 := measure_mono_null hshrink hz
  have ht := tendsto_measure_iInter_atTop (μ := ν)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
  rw [hint] at ht
  simpa only [ν, Function.comp_def, withDensity_apply _ (hA _)] using ht

end CircleDomainRigidity

end

end OAI
