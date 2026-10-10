import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceCellProfiles
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! # Positive probe probabilities give actual endpoint volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

/-- Independent uniform sampling on two finite cells is uniform sampling
on their product, with the exact product Haar normalization. -/
theorem cellProbabilityMeasure_prod
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (A : Set X) (B : Set Y) (hA0 : μ A ≠ 0) (hAt : μ A ≠ ⊤)
    (hB0 : ν B ≠ 0) (hBt : ν B ≠ ⊤) :
    (cellProbabilityMeasure μ A hA0 hAt : Measure X).prod
        (cellProbabilityMeasure ν B hB0 hBt : Measure Y) =
      ((μ.prod ν) (A ×ˢ B))⁻¹ • (μ.prod ν).restrict (A ×ˢ B) := by
  change ((μ A)⁻¹ • μ.restrict A).prod ((ν B)⁻¹ • ν.restrict B) = _
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.prod_restrict, Measure.prod_prod, ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt)]

/-- A positive fraction of the original cell becomes a corresponding
amount of actual volume under the section-coordinate embedding. -/
theorem probe_cell_image_volume_lower
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X → Y) (he : MeasurableEmbedding e)
    (A K : Set X) (hA0 : μ A ≠ 0) (hAt : μ A ≠ ⊤)
    (hK : MeasurableSet K) (hKA : K ⊆ A)
    {c : ℝ} (hc : 0 ≤ c)
    (hmass : ENNReal.ofReal c ≤ (cellProbabilityMeasure μ A hA0 hAt : Measure X) K) :
    c * (μ A).toReal ≤ ((Measure.map e μ) (e '' K)).toReal := by
  have hm := ENNReal.toReal_mono (measure_ne_top
    (cellProbabilityMeasure μ A hA0 hAt : Measure X) K) hmass
  rw [ENNReal.toReal_ofReal hc, cellProbabilityMeasure_apply_toReal μ A K hA0 hAt hK,
    inter_eq_left.mpr hKA] at hm
  have hvol := (le_div_iff₀ (ENNReal.toReal_pos hA0 hAt)).mp hm
  simpa only [he.map_apply, preimage_image_eq _ he.injective] using hvol

end PolycyclicRecognition

end

end OAI
