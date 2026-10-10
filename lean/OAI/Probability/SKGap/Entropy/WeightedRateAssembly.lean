import Mathlib
import OAI.Probability.SKGap.Localization.ScalarEmpirical

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

lemma weighted_four_region_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ≥0∞) (hg : Measurable g) (B F D : Set α)
    (hB : MeasurableSet B) (hF : MeasurableSet F) (hD : MeasurableSet D)
    (hfg : ∀ x, f x ≤ g x) (k : ℝ≥0∞)
    (hgood : ∀ x ∈ B ∩ Fᶜ ∩ Dᶜ, f x ≤ g x*k) :
    (∫⁻ x, f x ∂μ) ≤ (∫⁻ x in Bᶜ,g x ∂μ)+(∫⁻ x in B ∩ F,g x ∂μ)+
      (∫⁻ x in D,g x ∂μ)+(∫⁻ x,g x ∂μ)*k := by
  have bound (E : Set α) : (∫⁻ x in E,f x ∂μ) ≤ (∫⁻ x in E,g x ∂μ) := lintegral_mono hfg
  have sub (E E' : Set α) (h : E ⊆ E') : (∫⁻ x in E,g x ∂μ) ≤ (∫⁻ x in E',g x ∂μ) :=
    lintegral_mono_set h
  have hgood' : (∫⁻ x in B ∩ Fᶜ ∩ Dᶜ,f x ∂μ) ≤ (∫⁻ x,g x ∂μ)*k := by
    calc
      _ ≤ ∫⁻ x in B ∩ Fᶜ ∩ Dᶜ,g x*k ∂μ :=
        lintegral_mono_ae (ae_restrict_of_forall_mem ((hB.inter hF.compl).inter hD.compl) hgood)
      _ = (∫⁻ x in B ∩ Fᶜ ∩ Dᶜ,g x ∂μ)*k := lintegral_mul_const _ hg
      _ ≤ (∫⁻ x,g x ∂μ)*k := mul_le_mul' (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl
  have h3 := (lintegral_split_le μ f (B ∩ Fᶜ) D).trans
    (add_le_add ((bound _).trans (sub _ _ (fun _ h=>h.2))) hgood')
  have h2 := (lintegral_split_le μ f B F).trans (add_le_add (bound _) h3)
  have h1 := (lintegral_split_le μ f univ B).trans (add_le_add
    (by simpa only [univ_inter] using h2) (by simpa only [univ_inter] using bound Bᶜ))
  simpa only [Measure.restrict_univ,add_comm,add_left_comm,add_assoc] using h1

end SKGap
end
end

end OAI
