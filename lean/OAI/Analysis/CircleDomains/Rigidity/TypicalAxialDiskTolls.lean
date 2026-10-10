import OAI.Analysis.CircleDomains.Rigidity.CountableAxialDiskTolls

namespace OAI

/-! The same full-measure set of lines pays every finite segment and
every finite deletion of the matched disk family. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CircleDomainRigidity

 theorem axial_disk_tolls_summable_ae {ι : Type*} [Countable ι]
    (i : Fin 2) (c : ι → ℂ) (r s : ι → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (hr2 : Summable (fun j => r j^2)) (hs2 : Summable (fun j => s j^2)) :
    ∀ᵐ y ∂volume, Summable (fun j =>
      (Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j)).indicator
        (fun _ => 2*s j) y) := by
  apply ae_summable_weighted_band_series volume _ (fun j => 2*s j) (fun j => 2*r j)
    (fun _ => measurableSet_Icc) (fun j => mul_nonneg (by norm_num) (hs j))
    (fun j => mul_nonneg (by norm_num) (hr j))
  · intro j
    rw [Real.volume_Icc]
    apply le_of_eq
    congr 1
    ring
  · simpa only [mul_pow,show (2 : ℝ)^2 = 4 by norm_num] using hs2.mul_left 4
  · simpa only [mul_pow,show (2 : ℝ)^2 = 4 by norm_num] using hr2.mul_left 4

 theorem segment_disk_tolls_summable {ι : Type*} [Countable ι]
    (i : Fin 2) (c : ι → ℂ) (r s : ι → ℝ) (hs : ∀ j, 0 ≤ s j)
    {y : ℝ} (hy : Summable (fun j =>
      (Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j)).indicator
        (fun _ => 2*s j) y)) (a b : ℝ) :
    Summable (fun j => if ∃ x ∈ Icc a b, complexCoordinateLine i y x ∈ closedBall (c j) (r j)
      then 2*s j else 0) := by
  classical
  apply hy.of_nonneg_of_le
  · intro j
    split_ifs
    · exact mul_nonneg (by norm_num) (hs j)
    · exact le_rfl
  · intro j
    split_ifs with hj
    · have hband := (complexCoordinateLine_meets_closedBall i y (c j) (r j)).mp
        ⟨hj.choose,hj.choose_spec.2⟩
      rw [indicator_of_mem hband]
    · exact indicator_nonneg (fun _ _ => mul_nonneg (by norm_num) (hs j)) _

end CircleDomainRigidity

end

end OAI
