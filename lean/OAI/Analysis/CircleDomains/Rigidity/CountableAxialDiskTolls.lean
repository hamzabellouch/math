import OAI.Analysis.CircleDomains.Modulus.BandIncidence
import OAI.Analysis.CircleDomains.Topology.ParallelDiskTolls
import OAI.Analysis.CircleDomains.Sobolev.RealCoordinateLines

namespace OAI

/-! Countable axial disk tolls are integrable with their exact mixed-radius
budget. Point disks are missed outside a countable set of lines. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem complexCoordinateLine_meets_closedBall (i : Fin 2) (y : ℝ) (c : ℂ) (r : ℝ) :
    (∃ x, complexCoordinateLine i y x ∈ closedBall c r) ↔
      y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r) := by
  constructor
  · rintro ⟨x,hx⟩
    have h := (complexCoordinateLine_transverse_le i y x c).trans (by simpa only [mem_closedBall,dist_eq_norm] using hx)
    exact ⟨by linarith [(abs_le.mp h).1],by linarith [(abs_le.mp h).2]⟩
  · intro hy
    fin_cases i
    · simpa [complexCoordinateLine,realCoordinateLine,transverseCoordinate,Complex.equivRealProdCLM_symm_apply,Complex.mk_eq_add_mul_I] using
        (horizontal_line_meets_closedBall c).mpr hy
    · refine ⟨c.im,?_⟩
      have he : dist (complexCoordinateLine 1 y c.im) c = |y-c.re| := by
        rw [dist_eq_norm,← Complex.abs_re_eq_norm.mpr (by simp [complexCoordinateLine,realCoordinateLine])]
        simp [complexCoordinateLine,realCoordinateLine]
      change dist (complexCoordinateLine 1 y c.im) c ≤ r
      rw [he]
      have hyl : c.re-r ≤ y := hy.1
      have hyu : y ≤ c.re+r := hy.2
      exact abs_le.mpr ⟨by linarith,by linarith⟩

 def axialDiskToll {ι : Type*} (i : Fin 2) (c : ι → ℂ) (r s : ι → ℝ) (y : ℝ) : ℝ :=
  ∑' j, (Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j)).indicator
    (fun _ => 2*s j) y

 theorem axialDiskToll_integrable {ι : Type*} [Countable ι]
    (i : Fin 2) (c : ι → ℂ) (r s : ι → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hs : ∀ j, 0 ≤ s j)
    (hr2 : Summable (fun j => r j^2)) (hs2 : Summable (fun j => s j^2)) :
    Integrable (axialDiskToll i c r s) volume ∧
      (∫ y, axialDiskToll i c r s y) ≤ 4*∑' j, r j*s j := by
  have hb (j : ι) : volume (Icc (transverseCoordinate i (c j)-r j)
      (transverseCoordinate i (c j)+r j)) ≤ ENNReal.ofReal (2*r j) := by
    rw [Real.volume_Icc]
    apply le_of_eq
    congr 1
    ring
  have hr' : Summable (fun j => (2*r j)^2) := by simpa only [mul_pow,show (2 : ℝ)^2 = 4 by norm_num] using hr2.mul_left 4
  have hs' : Summable (fun j => (2*s j)^2) := by simpa only [mul_pow,show (2 : ℝ)^2 = 4 by norm_num] using hs2.mul_left 4
  have h := integral_weighted_band_series_le volume
    (fun j => Icc (transverseCoordinate i (c j)-r j) (transverseCoordinate i (c j)+r j))
    (fun j => 2*s j) (fun j => 2*r j) (fun _ => measurableSet_Icc)
    (fun j => mul_nonneg (by norm_num) (hs j)) (fun j => mul_nonneg (by norm_num) (hr j)) hb hs' hr'
  refine ⟨h.1,?_⟩
  apply h.2.trans_eq
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  ring

 theorem axial_point_disk_lines_null {ι : Type*} [Countable ι]
    (i : Fin 2) (c : ι → ℂ) (r : ι → ℝ) :
    volume {y | ∃ j, r j = 0 ∧ ∃ x, complexCoordinateLine i y x ∈ closedBall (c j) (r j)} = 0 := by
  apply measure_mono_null (t := ⋃ j, {transverseCoordinate i (c j)})
  · rintro y ⟨j,hj,hx⟩
    rw [complexCoordinateLine_meets_closedBall,hj,sub_zero,add_zero,Icc_self] at hx
    exact mem_iUnion.mpr ⟨j,hx⟩
  · exact measure_iUnion_null (fun _ => measure_singleton _)

end CircleDomainRigidity

end

end OAI
