import OAI.Geometry.RCD.Transport.RenyiSemicontinuity

namespace OAI

/-! # Additivity of the Rényi integral on disjoint transport components

Length-localized interior marginals are mutually singular. Their Rényi
integrals can therefore be added without losing the finite dimension.
-/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem rnDeriv_disjoint_ae (μ ν₀ ν₁ : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (hs : ν₀ ⟂ₘ ν₁) :
    ∀ᵐ x ∂μ, ν₀.rnDeriv μ x=0 ∨ ν₁.rnDeriv μ x=0 := by
  obtain ⟨S,hS,h0,h1⟩ := hs
  have hr0 : ν₀.restrict Sᶜ=ν₀ := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply ae_iff.mpr
    simpa [mem_compl_iff] using h0
  have hr1 : ν₁.restrict S=ν₁ := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact ae_iff.mpr h1
  have hd0 := Measure.rnDeriv_restrict ν₀ μ hS.compl
  have hd1 := Measure.rnDeriv_restrict ν₁ μ hS
  rw [hr0] at hd0
  rw [hr1] at hd1
  filter_upwards [hd0,hd1] with x hx0 hx1
  by_cases hx : x∈S
  · left
    simpa only [indicator_of_notMem (show x∉Sᶜ from fun h => h hx)] using hx0
  · right
    simpa only [indicator_of_notMem hx] using hx1

theorem renyiPower_add_mutuallySingular (μ ν₀ ν₁ : Measure X) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (hs : ν₀ ⟂ₘ ν₁)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∫ x, ((ν₀+ν₁).rnDeriv μ x).toReal^q ∂μ) =
      (∫ x, (ν₀.rnDeriv μ x).toReal^q ∂μ)+(∫ x, (ν₁.rnDeriv μ x).toReal^q ∂μ) := by
  have hi0 := integrable_density_power μ _ (ν₀.measurable_rnDeriv μ).ennreal_toReal
    Measure.integrable_toReal_rnDeriv (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hq0.le hq1.le
  have hi1 := integrable_density_power μ _ (ν₁.measurable_rnDeriv μ).ennreal_toReal
    Measure.integrable_toReal_rnDeriv (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hq0.le hq1.le
  have he : (fun x => ((ν₀+ν₁).rnDeriv μ x).toReal^q) =ᵐ[μ]
      fun x => (ν₀.rnDeriv μ x).toReal^q+(ν₁.rnDeriv μ x).toReal^q := by
    filter_upwards [Measure.rnDeriv_add ν₀ ν₁ μ,rnDeriv_disjoint_ae μ ν₀ ν₁ hs] with x hx hd
    rw [hx]
    rcases hd with hd | hd
    · simp only [Pi.add_apply,hd,zero_add,ENNReal.toReal_zero,Real.zero_rpow hq0.ne']
    · simp only [Pi.add_apply,hd,add_zero,ENNReal.toReal_zero,Real.zero_rpow hq0.ne']
  rw [integral_congr_ae he,integral_add hi0 hi1]

end RegularPointCoordinates

end

end OAI
