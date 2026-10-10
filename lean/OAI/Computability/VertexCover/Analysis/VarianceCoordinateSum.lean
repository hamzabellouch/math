import Mathlib
import OAI.Computability.VertexCover.PCP.SpectralCut
import OAI.Computability.VertexCover.Analysis.IntegralUpdate
import OAI.Computability.VertexCover.Analysis.VariancePi

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Product
open MeasureTheory

theorem update_right_measurePreserving {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι) :
    MeasurePreserving (fun p : (ι → E) × E => Function.update p.1 j p.2)
      ((Measure.pi (fun _ : ι => μ)).prod μ) (Measure.pi (fun _ : ι => μ)) := by
  exact (update_measurePreserving μ j).comp Measure.measurePreserving_swap

theorem update_right_ae {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
    {P : (ι → E) → Prop} (hP : ∀ᵐ s ∂Measure.pi (fun _ : ι => μ), P s) :
    ∀ᵐ s ∂Measure.pi (fun _ : ι => μ), ∀ᵐ x ∂μ, P (Function.update s j x) := by
  exact Measure.ae_ae_of_ae_prod ((update_right_measurePreserving μ j).quasiMeasurePreserving.ae hP)

theorem integral_update_right {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ] (j : ι)
    {f : (ι → E) → ℝ} (hf : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫ s, ∫ x, f (Function.update s j x) ∂μ ∂Measure.pi (fun _ : ι => μ)) =
      ∫ s, f s ∂Measure.pi (fun _ : ι => μ) := by
  have hp := update_right_measurePreserving μ j
  calc
    _ = ∫ p, f (Function.update p.1 j p.2)
        ∂((Measure.pi (fun _ : ι => μ)).prod μ) := by
      simpa only [Function.comp_apply] using
        (integral_prod _ (hp.integrable_comp_of_integrable hf)).symm
    _ = ∫ s, f s ∂Measure.map (fun p : (ι → E) × E => Function.update p.1 j p.2)
        ((Measure.pi (fun _ : ι => μ)).prod μ) := by
      exact (integral_map hp.measurable.aemeasurable
        (by simpa only [hp.map_eq] using hf.aestronglyMeasurable)).symm
    _ = _ := by rw [hp.map_eq]

end VertexCover.Product

namespace VertexCover.Cube
open MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev carrier (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)

theorem measurableSet_carrier (n : ℕ) : MeasurableSet (carrier n) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem ae_carrier (n : ℕ) : ∀ᵐ s ∂law (Fin n), s ∈ carrier n := by
  rw [law_eq_restrict_volume]
  exact (Measure.ae_ennreal_smul_measure_iff (pow_ne_zero _ (by norm_num) :
    (1/2 : ℝ≥0∞) ^ Fintype.card (Fin n) ≠ 0)).mpr
    (ae_restrict_mem (measurableSet_carrier n))

theorem norm_le_one_of_mem_carrier {n : ℕ} {s : Fin n → ℝ} (hs : s ∈ carrier n) :
    ‖s‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro k
  exact (abs_le.mpr (Set.mem_univ_pi.mp hs k))

noncomputable def boundedVersion {n : ℕ} (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  (carrier n).indicator f

theorem boundedVersion_measurable {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) : Measurable (boundedVersion f) :=
  hf.indicator (measurableSet_carrier n)

theorem boundedVersion_ae {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    boundedVersion f =ᵐ[law (Fin n)] f := by
  filter_upwards [ae_carrier n] with s hs
  exact Set.indicator_of_mem hs f

theorem boundedVersion_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith 1 f) (s : Fin n → ℝ) :
    ‖boundedVersion f s‖ ≤ ‖f 0‖ + 1 := by
  by_cases hs : s ∈ carrier n
  · rw [boundedVersion, Set.indicator_of_mem hs]
    have h := hf.dist_le_mul s 0
    simp only [NNReal.coe_one, one_mul, dist_zero_right, Real.dist_eq] at h
    calc
      ‖f s‖ ≤ ‖f s - f 0‖ + ‖f 0‖ := by simpa using norm_add_le (f s - f 0) (f 0)
      _ ≤ 1 + ‖f 0‖ := by simpa only [Real.norm_eq_abs, add_comm] using add_le_add_right (h.trans (norm_le_one_of_mem_carrier hs)) ‖f 0‖
      _ = _ := add_comm _ _
  · rw [boundedVersion, Set.indicator_of_notMem hs]
    simp only [norm_zero]
    positivity

theorem variance_le_coordinate_sum {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith 1 f) :
    variance f (law (Fin n)) ≤
      ∑ j, ∫ s, VertexCover.Product.coordinateVariance intervalLaw f j s ∂law (Fin n) := by
  have he := boundedVersion_ae f
  have hb := VertexCover.Product.variance_pi_le intervalLaw n (boundedVersion f)
    (boundedVersion_measurable hf.continuous.measurable) (boundedVersion_bound hf)
  have hv : variance (boundedVersion f) (law (Fin n)) = variance f (law (Fin n)) :=
    variance_congr he
  change variance (boundedVersion f) (law (Fin n)) ≤ _ at hb
  rw [hv] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [VertexCover.Product.update_right_ae intervalLaw j he] with s hs
  exact (variance_congr hs).symm

end VertexCover.Cube

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
