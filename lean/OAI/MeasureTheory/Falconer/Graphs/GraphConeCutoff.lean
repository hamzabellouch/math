import OAI.MeasureTheory.Falconer.Geometry.InactiveBinGeometry

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

noncomputable def graphConeBump : ContDiffBump (0 : ℝ) :=
  ⟨1/10, 1/5, by norm_num, by norm_num⟩

noncomputable def graphConeCutoff (θ : ℝ) : ℂ := (graphConeBump θ : ℝ)

theorem graphConeCutoff_contDiff : ContDiff ℝ ∞ graphConeCutoff :=
  Complex.ofRealCLM.contDiff.comp graphConeBump.contDiff

theorem graphConeCutoff_support : tsupport graphConeCutoff ⊆ Icc (-1/5 : ℝ) (1/5) := by
  have hb : tsupport (graphConeBump : ℝ → ℝ) = Icc (-1/5 : ℝ) (1/5) := by
    rw [ContDiffBump.tsupport_eq, Real.closedBall_eq_Icc]
    norm_num [graphConeBump]
  exact (tsupport_comp_subset (g := Complex.ofReal) rfl (graphConeBump : ℝ → ℝ)).trans hb.subset

theorem graphConeCutoff_one {θ : ℝ} (hθ : |θ| ≤ 1/10) : graphConeCutoff θ = 1 := by
  have hb : graphConeBump θ = 1 := graphConeBump.one_of_mem_closedBall
    (by simpa [graphConeBump, Real.dist_eq] using hθ)
  simp only [graphConeCutoff, hb, Complex.ofReal_one]

theorem graphConeCutoff_forward {φ : ℝ} (hφ : |φ| ≤ 1/20) :
    ∀ θ ∈ tsupport graphConeCutoff, 0 ≤ Real.cos (θ-φ) := by
  intro θ hθ
  have ht := graphConeCutoff_support hθ
  have hp := abs_le.mp hφ
  have hpi := Real.one_le_pi_div_two
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [ht.1,hp.2]) (by linarith [ht.2,hp.1])

end PlanarFalconer

end OAI
