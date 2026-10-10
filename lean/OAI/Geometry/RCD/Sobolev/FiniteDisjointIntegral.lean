import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Adding the defect on finitely many disjoint balls -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem finite_disjoint_setIntegral_le {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {Ω : Set X} {s : ι → Set X} {f : X → ℝ}
    (hf : IntegrableOn f Ω μ) (hf0 : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x)
    (hs : ∀ i, MeasurableSet (s i)) (hsub : ∀ i, s i ⊆ Ω)
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) :
    (∑ i, ∫ x in s i, f x ∂μ) ≤ ∫ x in Ω, f x ∂μ := by
  have hu : (⋃ i, s i) ⊆ Ω := iUnion_subset hsub
  rw [← integral_iUnion_fintype hs hdisj (fun i => hf.mono_set (hsub i))]
  exact setIntegral_mono_set hf hf0 (Filter.Eventually.of_forall fun _ hx => hu hx)

end RegularPointCoordinates

end

end OAI
