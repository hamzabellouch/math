import OAI.Geometry.SurfaceImmersion.Geometry.ScalarFlatHolder

namespace OAI

/-! The image of the flat second-jet stratum of a smooth scalar surface
function is null. No Sard hypothesis is used. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology NNReal ENNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem scalarFlatTwo_image_dimH {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) :
    dimH (f '' scalarFlatTwo f) ≤ (2 : ℝ≥0∞)/3 := by
  have hholder : dimH (f '' scalarFlatTwo f) ≤ dimH (scalarFlatTwo f)/(3 : ℝ≥0∞) := by
    apply dimH_image_le_of_locally_holder_on (by norm_num : (0 : ℝ≥0) < 3)
    intro p hp
    obtain ⟨C,hC⟩ := scalarFlatTwo_local_holder hf p
    refine ⟨C,scalarFlatTwo f ∩ ball p (1/4),?_,hC⟩
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ (by norm_num))
  have hdim : dimH (scalarFlatTwo f) ≤ (2 : ℝ≥0∞) := by
    have h := dimH_mono (subset_univ (scalarFlatTwo f))
    simpa [Base,Real.dimH_univ_pi_fin] using h
  exact hholder.trans (ENNReal.div_le_div_right hdim _)

theorem scalarFlatTwo_image_volume_zero {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) :
    volume (f '' scalarFlatTwo f) = 0 := by
  have hd : dimH (f '' scalarFlatTwo f) < (1 : ℝ≥0∞) :=
    (scalarFlatTwo_image_dimH hf).trans_lt (by
      rw [ENNReal.div_lt_iff (Or.inl (by norm_num : (3 : ℝ≥0∞) ≠ 0)) (Or.inl (by simp))]
      norm_num)
  have hm := hausdorffMeasure_of_dimH_lt (d := (1 : ℝ≥0)) hd
  simpa using hm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
