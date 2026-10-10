import Mathlib
import OAI.Probability.SKRatio.Gaussian.ExponentialEvents

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace SKRatioClock.Regression

lemma ExponentiallyRare.prod_snd {H K : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (K n)]
    {ρ : ∀ n, Measure (H n)} (μ : ∀ n, Measure (K n))
    [∀ n, SFinite (ρ n)] [∀ n, IsProbabilityMeasure (μ n)]
    {A : ∀ n, Set (H n)} (hA : ExponentiallyRare ρ A) :
    ExponentiallyRare (fun n => (μ n).prod (ρ n)) (fun n => Prod.snd ⁻¹' A n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he] with n hn
  have heq : (Prod.snd ⁻¹' A n : Set (K n × H n)) = univ ×ˢ A n := by ext; simp
  rw [heq,Measure.prod_prod,measure_univ,one_mul]
  exact hn

lemma ExponentiallyRare.prod_fst {H K : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (K n)]
    {ρ : ∀ n, Measure (H n)} (μ : ∀ n, Measure (K n))
    [∀ n, IsProbabilityMeasure (μ n)]
    {A : ∀ n, Set (H n)} (hA : ExponentiallyRare ρ A) :
    ExponentiallyRare (fun n => (ρ n).prod (μ n)) (fun n => Prod.fst ⁻¹' A n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he] with n hn
  have heq : (Prod.fst ⁻¹' A n : Set (H n × K n)) = A n ×ˢ univ := by ext; simp
  rw [heq,Measure.prod_prod,measure_univ,mul_one]
  exact hn

lemma ExponentiallyRare.preimage_hasLaw {H K : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)] [∀ n, MeasurableSpace (K n)]
    {ρ : ∀ n, Measure (H n)} {μ : ∀ n, Measure (K n)}
    {A : ∀ n, Set (H n)} (hA : ExponentiallyRare ρ A)
    (f : ∀ n, K n → H n) (hf : ∀ n, HasLaw (f n) (ρ n) (μ n)) :
    ExponentiallyRare μ (fun n => f n ⁻¹' A n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he] with n hn
  exact ((Measure.le_map_apply (hf n).aemeasurable (A n)).trans_eq
    (congrArg (fun m : Measure (H n) => m (A n)) (hf n).map_eq)).trans hn

end SKRatioClock.Regression

end
end

end OAI
