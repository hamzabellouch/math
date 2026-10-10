import OAI.Analysis.KadisonKastler.ScalarNormMinimizer
import OAI.Analysis.KadisonKastler.FiniteInnerComposition

namespace OAI

/-! # From arbitrarily accurate scalar averages to a scalar in the closed orbit hull -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

/-- The scalar values of contractive finite averages stay in a compact disk.
Thus arbitrarily small scalar errors give an actual scalar in the closed hull. -/
theorem exists_scalar_mem_closed_orbit (x : H →L[ℂ] H)
    (havg : ∀ ε : ℝ, 0 < ε → ∃ (A : FiniteInnerAverage M) (z : ℂ),
      ‖A.apply x - z • (1 : H →L[ℂ] H)‖ < ε) :
    ∃ z : ℂ, z • (1 : H →L[ℂ] H) ∈ closure (convexHull ℝ (innerUnitaryOrbit M x)) := by
  let C := closure (convexHull ℝ (innerUnitaryOrbit M x))
  let R := ‖x‖ + 1
  let f : ℂ → ℝ := fun z => Metric.infDist (z • (1 : H →L[ℂ] H)) C
  have hf : Continuous f := (Metric.continuous_infDist_pt C).comp
    (continuous_id.smul continuous_const)
  have h0 : (0 : ℂ) ∈ Metric.closedBall 0 R := by
    simp only [Metric.mem_closedBall, dist_self]
    dsimp [R]
    positivity
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMinOn ⟨0, h0⟩ hf.continuousOn
  have hsmall (ε : ℝ) (hε : 0 < ε) : f z < ε := by
    let δ := min (ε / 2) (1 / 2)
    have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
    obtain ⟨A, w, hw⟩ := havg δ hδ
    have hwR : ‖w‖ ≤ R := by
      have hb := A.norm_apply_le x
      have hs := norm_sub_le_norm_sub_add_norm_sub (w • (1 : H →L[ℂ] H)) (A.apply x) 0
      simp only [sub_zero, norm_smul, norm_one, mul_one] at hs
      rw [norm_sub_rev (w • (1 : H →L[ℂ] H)) (A.apply x)] at hs
      have hd : δ ≤ 1 / 2 := min_le_right _ _
      dsimp [R]
      linarith
    have hwB : w ∈ Metric.closedBall 0 R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hwR
    have hi : f w ≤ ‖A.apply x - w • (1 : H →L[ℂ] H)‖ := by
      have h := Metric.infDist_le_dist_of_mem (x := w • (1 : H →L[ℂ] H))
        (subset_closure (A.apply_mem_orbitHull x))
      simpa only [f, dist_eq_norm, norm_sub_rev] using h
    have he : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    exact (hz hwB).trans_lt (hi.trans_lt (hw.trans he))
  have hzero : f z = 0 := by
    by_contra h
    have hp : 0 < f z := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm h)
    exact (lt_irrefl _ (hsmall _ hp))
  have hC : C.Nonempty := by
    refine ⟨x, subset_closure (subset_convexHull ℝ _ ?_)⟩
    refine ⟨1, ?_⟩
    change (1 : H →L[ℂ] H) * x * star (1 : H →L[ℂ] H) = x
    simp
  have hc : IsClosed C := isClosed_closure
  exact ⟨z, (hc.mem_iff_infDist_zero hC).mpr hzero⟩

end

end KadisonKastler

end OAI
