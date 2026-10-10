import OAI.Analysis.CircleDomains.Rigidity.MaskedLevelData

namespace OAI

/-! Exact Haar length of a projected interval. A band of width at most
one is measured without loss, so its actual coordinate weight controls
every bounded local real lift of that band. -/

open Set Function MeasureTheory Metric Filter
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem addCircle_image_Icc_eq_closedBall (a b : ℝ) :
    ((↑) : ℝ → UnitAddCircle) '' Icc a b =
      closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) := by
  apply Subset.antisymm (addCircle_image_Icc_subset_closedBall a b)
  intro θ hθ
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hy : y ∈ ((↑) : ℝ → UnitAddCircle) ⁻¹'
      closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) := hθ
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp hy
  rw [mem_closedBall, Real.dist_eq] at hz
  simp only [zsmul_eq_mul, mul_one] at hz
  refine ⟨y - (z : ℝ), ?_, ?_⟩
  · obtain ⟨hl, hu⟩ := abs_le.mp hz
    constructor <;> linarith
  · apply unitAddCircle_eq_iff_exists_int.mpr
    refine ⟨-z, ?_⟩
    push_cast
    ring

 theorem volume_addCircle_image_Icc (a b : ℝ) :
    volume (((↑) : ℝ → UnitAddCircle) '' Icc a b) =
      ENNReal.ofReal (min 1 (b - a)) := by
  rw [addCircle_image_Icc_eq_closedBall, AddCircle.volume_closedBall]
  congr 2
  ring

 theorem band_width_le_of_fiber_subset
    {U : Set Sphere} {f : Sphere → ℝ} {M : ℝ}
    (hf : ∀ y ∈ U, |f y| ≤ M) {x : Sphere} (hx : x ∈ closure U)
    (hwidth : limsup f (𝓝[U] x) - liminf f (𝓝[U] x) ≤ 1)
    {lo hi : ℝ}
    (hsub : {θ : UnitAddCircle | (x, θ) ∈ circleBandGraph U f} ⊆
      ((↑) : ℝ → UnitAddCircle) '' Icc lo hi) :
    ENNReal.ofReal (limsup f (𝓝[U] x) - liminf f (𝓝[U] x)) ≤
      ENNReal.ofReal (hi - lo) := by
  have hvol := measure_mono (μ := (volume : Measure UnitAddCircle)) hsub
  rw [circleBandGraph_fiber_eq_image_realFiber,
    intervalFiberHull_clusterGraph_eq_boundary_band hf hx,
    volume_addCircle_image_Icc, min_eq_right hwidth] at hvol
  exact hvol.trans ((volume_addCircle_image_Icc_le lo hi).trans
    (ENNReal.ofReal_le_ofReal (min_le_right _ _)))

end CircleDomainRigidity

end

end OAI
