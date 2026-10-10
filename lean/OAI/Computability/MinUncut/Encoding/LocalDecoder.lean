import Mathlib
import OAI.Computability.MinUncut.Estimates.Density
import OAI.Computability.MinUncut.Games.AffineLabels

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Composition
open BinaryFourier hiding F₂
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {V W A B : Type*}
  [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] [Fintype B]

def labelList (f : Forms A → ℝ) (u : ℝ) : Finset A :=
  Finset.univ.filter (fun a => u ≤ |coefficient f (labelFrequency a)|)

@[simp] lemma mem_labelList (f : Forms A → ℝ) (u : ℝ) (a : A) :
    a ∈ labelList f u ↔ u ≤ |coefficient f (labelFrequency a)| := by
  simp [labelList]

lemma labelList_card (f : Forms A → ℝ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0<u)
    (hf : ∀ a, |f a| ≤ M) : ((labelList f u).card : ℝ) ≤ M^2/u^2 := by
  have hsub : (labelList f u).image labelFrequency ⊆ largeSpectrum f u := by
    intro α hα
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hα
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_labelList f u a).mp ha⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ labelFrequency_injective] at hcard
  exact (Nat.cast_le.mpr hcard).trans (largeSpectrum_card f hM hu hf)

lemma coefficient_sq_le_mean (f : Forms A → ℝ) (α : Module.Dual F₂ (Forms A)) :
    coefficient f α ^2 ≤ 𝔼 a, f a ^2 := by
  rw [← parseval]
  exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ α)

theorem local_matching (π : A →ᵃ[F₂] B) (f : Forms A → ℝ) (g : Forms B → ℝ)
    {u θ : ℝ} (hθ : 0<θ) (b : B)
    (hb : b ∈ labelList g θ)
    (hclose : (𝔼 z : Forms B, (g z-f (formPullback π z))^2) < (θ/4)^2)
    (hrem : |coefficient (fun z => remainder f u (formPullback π z))
      (labelFrequency b)| < θ/4) :
    ∃ a ∈ labelList f u, π a=b := by
  have hc := coefficient_sq_le_mean (fun z => g z-f (formPullback π z)) (labelFrequency b)
  rw [coefficient_sub] at hc
  have hcabs : |coefficient g (labelFrequency b)-
      coefficient (fun z => f (formPullback π z)) (labelFrequency b)| < θ/4 := by
    have hs := hc.trans_lt hclose
    nlinarith [sq_abs (coefficient g (labelFrequency b)-
      coefficient (fun z => f (formPullback π z)) (labelFrequency b)),
      abs_nonneg (coefficient g (labelFrequency b)-
      coefficient (fun z => f (formPullback π z)) (labelFrequency b))]
  obtain ⟨α,ha,hα,hodd⟩ := extract_matched_odd f g (formPullback π)
    (AffineMap.const F₂ A 1) (AffineMap.const F₂ B 1) (formPullback_one π)
    (labelFrequency b) hθ (labelFrequency_odd b) ((mem_labelList g θ b).mp hb) hcabs hrem
  obtain ⟨a,rfl⟩ := oddFrequency_exists_label α hodd
  refine ⟨a,(mem_labelList f u a).mpr ha,?_⟩
  exact labelFrequency_injective hα

end MinUncut.Composition

end
end

end OAI
