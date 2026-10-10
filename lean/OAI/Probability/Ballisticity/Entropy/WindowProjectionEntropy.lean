import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal Classical
namespace DirectionalTransience.StoppedWindow
variable {Z F D V : Type*} [MeasurableSpace Z] [MeasurableSpace F]
  [MeasurableSpace D] [MeasurableSpace V]

lemma product_map_reference (ζ : Measure Z) [IsFiniteMeasure ζ]
    (π : Measure F) [IsProbabilityMeasure π]
    (data : Z → D) (hd : Measurable data)
    (field : Z → F → V) (hf : Measurable (fun p : Z × F => field p.1 p.2))
    (R : Kernel D V) [IsMarkovKernel R]
    (hR : ∀ z, π.map (field z) = R (data z)) :
    (ζ.prod π).map (fun p => (data p.1,field p.1 p.2)) = (ζ.map data).compProd R := by
  have hout : Measurable (fun p : Z × F => (data p.1,field p.1 p.2)) :=
    (hd.comp measurable_fst).prodMk hf
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hout (hA.prod hB),
    Measure.prod_apply ((hA.prod hB).preimage hout),
    Measure.compProd_apply_prod hA hB, ← lintegral_indicator hA,
    lintegral_map (by exact (R.measurable_coe hB).indicator hA) hd]
  apply lintegral_congr
  intro z
  by_cases hz : data z ∈ A
  · rw [Set.indicator_of_mem hz]
    have he : Prod.mk z ⁻¹' ((fun p : Z × F => (data p.1,field p.1 p.2)) ⁻¹' (A ×ˢ B)) =
        field z ⁻¹' B := by ext v; simp [hz]
    have hfz : Measurable (field z) := hf.comp measurable_prodMk_left
    rw [he, ← Measure.map_apply hfz hB,hR z]
  · have he : Prod.mk z ⁻¹' ((fun p : Z × F => (data p.1,field p.1 p.2)) ⁻¹' (A ×ˢ B)) = ∅ := by
      ext v; simp [hz]
    simp [he,hz]

lemma map_data_field_fst (μ : Measure (Z × F))
    (data : Z → D) (hd : Measurable data)
    (field : Z → F → V) (hf : Measurable (fun p : Z × F => field p.1 p.2)) :
    (μ.map (fun p => (data p.1,field p.1 p.2))).fst = μ.fst.map data := by
  calc
    _ = μ.map (fun p : Z × F => data p.1) :=
      Measure.fst_map_prodMk (hd.comp measurable_fst) hf
    _ = _ := (Measure.map_map hd measurable_fst).symm

theorem own_marginal_projection (μ : Measure (Z × F)) [IsFiniteMeasure μ]
    (π : Measure F) [IsProbabilityMeasure π]
    (data : Z → D) (hd : Measurable data)
    (field : Z → F → V) (hf : Measurable (fun p : Z × F => field p.1 p.2))
    (R : Kernel D V) [IsMarkovKernel R]
    (hR : ∀ z, π.map (field z) = R (data z)) :
    let out := μ.map (fun p => (data p.1,field p.1 p.2))
    klDiv out (out.fst.compProd R) ≤ klDiv μ (μ.fst.prod π) := by
  have hout : Measurable (fun p : Z × F => (data p.1,field p.1 p.2)) :=
    (hd.comp measurable_fst).prodMk hf
  have h := klDiv_map_le μ (μ.fst.prod π) hout
  rw [product_map_reference μ.fst π data hd field hf R hR] at h
  dsimp only
  rw [map_data_field_fst μ data hd field hf]
  exact h

end DirectionalTransience.StoppedWindow

end

end OAI
