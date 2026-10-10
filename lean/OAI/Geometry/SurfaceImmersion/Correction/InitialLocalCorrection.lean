import OAI.Geometry.SurfaceImmersion.Correction.InitialCorrectionStage

namespace OAI

/-! Local finite-accuracy criterion for an actual exact correction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance initialLocalFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance initialLocalFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance initialLocalDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialLocalDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialLocalSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialLocalSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable {g : SmoothMetric M} {F : M → Space} {d : MetricGoodPhaseData g F}
namespace MetricGoodPhaseData
open ExactCorrection

/-- A finite order metric-accuracy criterion, with all constants chosen before
the smoothing scale. The resulting isometric map stays in the prescribed
geometric neighborhood of the reference immersion. -/
theorem local_exact_correction (d : MetricGoodPhaseData g F)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ c : PreparedCorrection d.toCorrectionGeometry, ∃ e ε : ℝ, 0 < e ∧ 0 < ε ∧ ε ≤ 1/32 ∧
    ∀ t : ℝ, 0 < t → t < ε →
      d.A.TensorWeightedBound t 440 ((t^(10 : ℝ))^2*e) (inducedTensor F-g.inner) →
      ∃ G : M → Space, IsSmoothIsometricImmersion M g G ∧
        d.A.WeightedBound 1 2 (c.ρ/4) (G-F) := by
  classical
  obtain ⟨P,hP,hPbound⟩ := d.A.exists_shifted_bound 2 0 hF
  obtain ⟨Q,hQ,hQbound⟩ := d.A.exists_bundle_bound
    d.A.tensorTriv d.A.tensorTriv_domain 0 g.contMDiff
  obtain ⟨C,hC,hCbound⟩ := d.A.exists_shifted_bound 2 440 hF
  obtain ⟨D,hD,hDbound⟩ := d.A.exists_bundle_bound
    d.A.tensorTriv d.A.tensorTriv_domain 440 g.contMDiff
  obtain ⟨c,hlarge⟩ := d.preparedCorrection_large hF (P+Q+1)
  have hPB : P < c.budget/4 := by linarith
  have hQB : Q < c.budget/4 := by linarith
  let e := min (c.a/8) (c.budget/4)
  have he : 0 < e := lt_min (by linarith [c.a_pos]) (by linarith [c.budget_pos])
  obtain ⟨εC,hεC,_,hCs⟩ := positive_power_threshold C 1 (c.budget/4)
    (by norm_num) (by linarith [c.budget_pos])
  obtain ⟨εD,hεD,_,hDs⟩ := positive_power_threshold D 1 (c.budget/4)
    (by norm_num) (by linarith [c.budget_pos])
  obtain ⟨εP,hεP,_,hPs⟩ := positive_power_threshold P 20 (c.ρ/8)
    (by norm_num) (by linarith [c.ρ_pos])
  let ε := min (c.ε 0) (min (1/32) (min εC (min εD εP)))
  have hε : 0 < ε := lt_min (c.ε_pos 0)
    (lt_min (by norm_num) (lt_min hεC (lt_min hεD hεP)))
  refine ⟨c,e,ε,he,hε,(min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro t ht htε herr
  have hε0 : t < c.ε 0 := htε.trans_le (min_le_left _ _)
  have hε1 := htε.trans_le (min_le_right _ _)
  have ht32 : t ≤ 1/32 := hε1.le.trans (min_le_left _ _)
  have hε2 := hε1.trans_le (min_le_right _ _)
  have htc : t < εC := hε2.trans_le (min_le_left _ _)
  have hε3 := hε2.trans_le (min_le_right _ _)
  have htd : t < εD := hε3.trans_le (min_le_left _ _)
  have htp : t < εP := hε3.trans_le (min_le_right _ _)
  have hCt : t*C < c.budget/4 := by
    simpa only [Real.rpow_one,mul_comm] using hCs t ht htc
  have hDt : t*D < c.budget/4 := by
    simpa only [Real.rpow_one,mul_comm] using hDs t ht htd
  have hdelta : (t^(10 : ℝ))^2 = t^(20 : ℝ) := by
    rw [show (20 : ℝ) = 10*2 by norm_num,Real.rpow_mul ht.le]
    norm_num
  have hnear : (t^(10 : ℝ))^2*P ≤ c.ρ/8 := by
    rw [hdelta,mul_comm]
    exact (hPs t ht htp).le
  obtain ⟨seed,_⟩ := c.initial_stage_of_bounds hF ht ht32 hε0 hP hC hD he.le
    hPbound hCbound hQbound hDbound herr
    (by linarith [c.budget_pos]) (by have hh := min_le_right (c.a/8) (c.budget/4); dsimp [e] at *; linarith [c.budget_pos])
    hnear (min_le_left _ _)
  obtain ⟨G,hG,_,hGF⟩ := c.exact_correction_with_control hF ht ht32 seed
  exact ⟨G,hG,hGF⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
