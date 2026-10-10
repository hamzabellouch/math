import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeights
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingVariation

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

open ScalarSampling

theorem measurable_orbitWeight_pair (D I : Finset ℕ) (h α : ℝ) (n : ℕ) :
    Measurable (fun p : (ℕ → ℝ) × Base => orbitWeight D I h α p.1 n p.2) := by
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_coordinateWeight I h α i).comp
    ((ProductCocycle.measurable_representative.comp
      ((measurable_pi_apply i).comp measurable_snd)).prodMk
      ((measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).fract))

theorem measurable_prefixWeight_pair (D I : Finset ℕ) (h α : ℝ) (n : ℕ) :
    Measurable (fun p : (ℕ → ℝ) × (D → Circle) => prefixWeight D I h α p.1 n p.2) := by
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_coordinateWeight I h α i).comp
    ((ProductCocycle.measurable_representative.comp
      ((measurable_pi_apply i).comp measurable_snd)).prodMk
      ((measurable_const.mul ((measurable_pi_apply (i : ℕ)).comp measurable_fst)).fract))

theorem coordinateWeight_eq_manuscript {I : Finset ℕ} {i m : ℕ}
    (hi : i ∉ I) {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (ht : t ∈ Ico (0 : ℝ) 1) :
    coordinateWeight I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) i s t =
      manuscriptKernel m s t := by
  simp only [coordinateWeight, ite_eq_right hi, manuscriptKernel, circleKernel,
    Int.fract_eq_self.mpr hs, Int.fract_eq_self.mpr ht]

theorem height_manuscript {m : ℕ} (hm : 200 ≤ m) :
    height ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) =
      (m : ℝ)^(13 / 5 : ℝ) := by
  rw [height, manuscript_reciprocal_height hm, max_eq_right]
  exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ m)) (by norm_num)

theorem manuscript_orbitWeight_bound (D I : Finset ℕ) {m : ℕ}
    (hm : 200 ≤ m) (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    orbitWeight D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) θ n x ≤
      ((m : ℝ)^(13 / 5 : ℝ)) ^ D.card := by
  obtain ⟨hh, _, hα, _⟩ := manuscript_parameters hm
  simpa only [height_manuscript hm] using (orbitWeight_bounds D I hh hα θ n x).2

theorem memLp_orbitWeight_pair (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (n : ℕ)
    (ν : Measure (ℕ → ℝ)) [IsFiniteMeasure ν] (p : ℝ≥0∞) :
    MemLp (fun z : (ℕ → ℝ) × Base => orbitWeight D I h α z.1 n z.2)
      p (ν.prod baseMeasure) := by
  apply MemLp.of_bound (measurable_orbitWeight_pair D I h α n).aestronglyMeasurable
    (height h α ^ D.card)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (orbitWeight_bounds D I hh hα z.1 n z.2).1]
  exact (orbitWeight_bounds D I hh hα z.1 n z.2).2

end Invariant233.ProductModel.SamplingWeights

end

end OAI
