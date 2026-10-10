import OAI.Geometry.Relativity.CKS.SurfaceVolume

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory CKSReplacementCompleteness
open scoped ContDiff Topology ENNReal
namespace CKSReplacementCompleteness
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
lemma scalar_edist_le_metricEDist (g : Metric I (M := M)) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ,ℝ) 1 f)
    (hdf : ∀ x v, ‖mfderiv I 𝓘(ℝ,ℝ) f x v‖ ≤ tangentNorm I g x v) (x y : M) :
    edist (f x) (f y) ≤ metricEDist I g x y := by
  rw [metricEDist_eq]
  refine le_iInf fun γ => le_iInf fun hγ => ?_
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ,ℝ)),riemannianEDist_def]
  let η : Path (f x) (f y) := γ.map hf.continuous
  have hη : ContMDiff (modelWithCornersEuclideanHalfSpace 1) 𝓘(ℝ,ℝ) 1 η := hf.comp hγ
  apply (iInf_le_of_le η (iInf_le _ hη)).trans
  apply lintegral_mono
  intro t
  change ‖mfderiv (modelWithCornersEuclideanHalfSpace 1) 𝓘(ℝ,ℝ) (f ∘ γ) t 1‖ₑ ≤ _
  rw [mfderiv_comp t (hf.mdifferentiable (by simp) _) (hγ.mdifferentiable (by simp) _)]
  rw [ContinuousLinearMap.comp_apply,← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hdf _ _)

lemma complete_of_proper_scalar {X : Type*} [EMetricSpace X] {f : X → ℝ}
    (hcompact : ∀ c, IsCompact {x | f x ≤ c})
    (hf : ∀ x y, edist (f x) (f y) ≤ edist x y) : CompleteSpace X := by
  apply EMetric.complete_of_cauchySeq_tendsto
  intro s hs
  obtain ⟨N,hN⟩ := EMetric.cauchySeq_iff.mp hs 1 (by norm_num)
  have hbound : ∀ᶠ n in atTop, s n ∈ {x | f x ≤ f (s N)+1} := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hd : edist (f (s n)) (f (s N)) < 1 := (hf _ _).trans_lt (hN n hn N le_rfl)
    have hreal : |f (s n)-f (s N)| < 1 := by
      simpa only [edist_dist,Real.dist_eq,ENNReal.ofReal_lt_one] using hd
    change f (s n) ≤ f (s N)+1
    linarith [(abs_lt.mp hreal).2]
  obtain ⟨x,hx,hlim⟩ := (hcompact (f (s N)+1)).isSeqCompact.exists_tendsto_of_frequently_mem
    hbound.frequently hs
  exact ⟨x,hlim⟩
end CKSReplacementCompleteness

end

end OAI
