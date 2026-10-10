import Mathlib

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S Ω : Type*} [Fintype S] [MeasurableSpace Ω]

def finiteInformationPMF (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) :
    PMF S :=
  PMF.ofFintype (fun s => ENNReal.ofReal (w s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hw s), hw1]
    simp)

def finiteInformationLaw (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (X : S → Ω) : ProbabilityMeasure Ω :=
  ⟨((finiteInformationPMF w hw hw1).map X).toMeasure, inferInstance⟩

lemma finiteInformationLaw_integral (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hw1 : ∑ s, w s = 1) (X : S → Ω) (f : Ω → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂(finiteInformationLaw w hw hw1 X : Measure Ω)) =
      ∑ s, w s * f (X s) := by
  let : MeasurableSpace S := ⊤
  have hX : Measurable X := measurable_of_countable X
  change (∫ x, f x ∂(((finiteInformationPMF w hw hw1).map X).toMeasure)) = _
  rw [← PMF.toMeasure_map X _ hX, integral_map hX.aemeasurable hf.aestronglyMeasurable,
    PMF.integral_eq_sum]
  simp only [finiteInformationPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw _),
    smul_eq_mul]

lemma finiteInformationLaw_apply (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hw1 : ∑ s, w s = 1) (X : S → Ω) (G : Set Ω) (hG : MeasurableSet G) :
    (finiteInformationLaw w hw hw1 X : Measure Ω) G =
      ENNReal.ofReal (∑ s, if X s ∈ G then w s else 0) := by
  classical
  let : MeasurableSpace S := ⊤
  have hX : Measurable X := measurable_of_countable X
  change (((finiteInformationPMF w hw hw1).map X).toMeasure) G = _
  rw [← PMF.toMeasure_map X _ hX, Measure.map_apply hX hG,
    PMF.toMeasure_apply _ (hX hG), tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg (fun s _ => by split_ifs; exact hw s; exact le_rfl)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Set.indicator_apply, Set.mem_preimage, finiteInformationPMF, PMF.ofFintype_apply]
  split_ifs <;> simp

lemma finiteInformationLaw_integrable (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hw1 : ∑ s, w s = 1) (X : S → Ω) (f : Ω → ℝ) (hf : Measurable f) :
    Integrable f (finiteInformationLaw w hw hw1 X : Measure Ω) := by
  let : MeasurableSpace S := ⊤
  have hX : Measurable X := measurable_of_countable X
  change Integrable f (((finiteInformationPMF w hw hw1).map X).toMeasure)
  rw [← PMF.toMeasure_map X _ hX]
  exact (integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable).mpr
    (Integrable.of_finite)

lemma finiteInformationLaw_ae (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hw1 : ∑ s, w s = 1) (X : S → Ω) (P : Ω → Prop)
    (hP : MeasurableSet {x | P x}) (hs : ∀ s, 0 < w s → P (X s)) :
    ∀ᵐ x ∂(finiteInformationLaw w hw hw1 X : Measure Ω), P x := by
  classical
  apply ae_iff.mpr
  rw [finiteInformationLaw_apply w hw hw1 X {x | ¬P x} (by exact hP.compl)]
  apply ENNReal.ofReal_eq_zero.mpr
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro s _
  by_cases hp : P (X s)
  · simp [hp]
  · have hz : w s = 0 := le_antisymm (le_of_not_gt (fun h => hp (hs s h))) (hw s)
    simp [hz]

end PlanarEndpoint.TransverseInformation
end

end OAI
