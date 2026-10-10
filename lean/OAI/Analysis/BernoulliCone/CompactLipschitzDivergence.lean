import OAI.Analysis.BernoulliCone.FluxSeam

namespace OAI

universe uE uG

section
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff NNReal
namespace Bernoulli.Foliation
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ G] in
lemma locallyLipschitz_compact_lipschitz [NormedSpace ℝ G] {F:E→G} (hl:LocallyLipschitz F)
    (hc:HasCompactSupport F) : ∃K:ℝ≥0,LipschitzWith K F := by
  obtain ⟨R,hR⟩:=hc.isBounded.subset_ball (0:E)
  obtain ⟨K,hK⟩:=hl.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0:E) (R+1))
  obtain ⟨M,hM⟩:=hc.exists_bound_of_continuousOn hl.continuous.continuousOn
  let C:ℝ≥0:=⟨max (K:ℝ) (max M 0),le_max_of_le_right (le_max_right _ _)⟩
  have hKC:(K:ℝ)≤C:=le_max_left _ _
  have hMC:M≤(C:ℝ):=(le_max_left M 0).trans (le_max_right _ _)
  have hbound (x y:E) (hx:x∈tsupport F) (hy:y∉Metric.closedBall (0:E) (R+1)):
      dist (F x) (F y)≤(C:ℝ)*dist x y := by
    have hFx:dist x 0<R:=hR hx
    have hFy:R+1<dist y 0:=by simpa only [Metric.mem_closedBall,not_le] using hy
    have hdy:1≤dist x y:=by have hh:=dist_triangle y x 0; rw [dist_comm y x] at hh; linarith
    have hyS:y∉tsupport F:=by
      intro hys
      have hyR:=hR hys
      change dist y 0<R at hyR
      linarith
    rw [image_eq_zero_of_notMem_tsupport hyS,dist_zero_right]
    exact (hM x hx).trans (hMC.trans (le_mul_of_one_le_right C.2 hdy))
  refine ⟨C,LipschitzWith.of_dist_le_mul fun x y=>?_⟩
  by_cases hx:x∈tsupport F
  · by_cases hy:y∈Metric.closedBall (0:E) (R+1)
    · have hxB:x∈Metric.closedBall (0:E) (R+1):=by
        have hh:=hR hx
        change dist x 0<R at hh
        change dist x 0≤R+1
        linarith
      exact (hK.dist_le_mul x hxB y hy).trans (mul_le_mul_of_nonneg_right hKC dist_nonneg)
    · exact hbound x y hx hy
  · by_cases hy:y∈tsupport F
    · by_cases hxB:x∈Metric.closedBall (0:E) (R+1)
      · have hyB:y∈Metric.closedBall (0:E) (R+1):=by
          have hh:=hR hy
          change dist y 0<R at hh
          change dist y 0≤R+1
          linarith
        exact (hK.dist_le_mul x hxB y hyB).trans (mul_le_mul_of_nonneg_right hKC dist_nonneg)
      · simpa only [dist_comm] using hbound y x hy hxB
    · rw [image_eq_zero_of_notMem_tsupport hx,image_eq_zero_of_notMem_tsupport hy,dist_self]
      positivity

lemma integral_directional_compact {d:ℕ} {f:Space d→ℝ} {K:ℝ≥0}
    (hf:LipschitzWith K f) (hc:HasCompactSupport f) (v:Space d) :
    (∫x,fderiv ℝ f x v)=0 := by
  obtain ⟨φ,hφ,hφc,hφS,hφ1⟩:=LocalExtension.exists_cutoff hc isOpen_univ (subset_univ _)
  have hφT:Test univ φ:=⟨hφ,hφc,hφS⟩
  have hh:=LipschitzSobolev.weakGradient hf univ φ hφT v
  simp only [Measure.restrict_univ,inner_gradient_left] at hh
  have hr:(fun x:Space d=>fderiv ℝ f x v * φ x)=(fun x=>fderiv ℝ f x v):=by
    funext x
    by_cases hx:x∈tsupport f
    · have he:φ x=1:=(show φ =ᶠ[𝓝 x] (fun _=>1) from hφ1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
      rw [he,mul_one]
    · rw [fderiv_of_notMem_tsupport ℝ hx,zero_apply,zero_mul]
  have he:(fun x:Space d=>f x*(fderiv ℝ φ x) v)=0:=by
    funext x
    by_cases hx:x∈tsupport f
    · have heq:φ =ᶠ[𝓝 x] (fun _=>1):=hφ1.filter_mono (nhds_le_nhdsSet hx)
      simp only [heq.fderiv_eq,fderiv_fun_const,zero_apply,mul_zero,Pi.zero_apply]
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
      rfl
  rw [hr,he] at hh
  simpa only [integral_zero,Pi.zero_def,zero_eq_neg] using hh
lemma integrable_directional_compact {d:ℕ} {f:Space d→ℝ} {K:ℝ≥0}
    (hf:LipschitzWith K f) (hc:HasCompactSupport f) (v:Space d) :
    Integrable (fun x=>fderiv ℝ f x v) := by
  have hs:Function.support (fun x=>fderiv ℝ f x v)⊆tsupport f:=
    (subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ v)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply (integrableOn_const (μ:=volume) (C:=((K:ℝ)*‖v‖)) hc.measure_ne_top).mono'
    (((continuous_id.clm_apply continuous_const : Continuous (fun L:Space d→L[ℝ]ℝ=>L v)).measurable.comp (measurable_fderiv ℝ f)).aestronglyMeasurable.restrict)
  filter_upwards [] with x
  exact ((fderiv ℝ f x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))

lemma integrable_divergence_compact {d:ℕ} {F:Space d→Space d} {K:ℝ≥0}
    (hF:LipschitzWith K F) (hc:HasCompactSupport F) : Integrable (divergence F) := by
  let e:=stdOrthonormalBasis ℝ (Space d)
  let f:=fun i x=>inner ℝ (e i) (F x)
  have hf i:LipschitzWith (‖innerSL ℝ (e i)‖₊*K) (f i):=
    (innerSL ℝ (e i)).lipschitzWith.comp hF
  have hfc i:HasCompactSupport (f i):=by
    apply HasCompactSupport.intro hc
    intro x hx
    simp only [f,image_eq_zero_of_notMem_tsupport hx,inner_zero_right]
  have he:divergence F =ᵐ[volume] (fun x=>∑i,fderiv ℝ (f i) x (e i)):=by
    filter_upwards [hF.ae_differentiableAt] with x hx
    unfold divergence
    apply Finset.sum_congr rfl
    intro i hi
    have hd:HasFDerivAt (f i) ((innerSL ℝ (e i)) ∘L fderiv ℝ F x) x:=
      (innerSL ℝ (e i)).hasFDerivAt.comp x hx.hasFDerivAt
    rw [hd.fderiv]
    rfl
  exact (integrable_finsetSum _ (fun i hi=>integrable_directional_compact (hf i) (hfc i) (e i))).congr he.symm

lemma divergence_zero_outside_support {d:ℕ} {F:Space d→Space d} {x:Space d}
    (hx:x∉tsupport F) : divergence F x=0 := by
  unfold divergence
  simp only [fderiv_of_notMem_tsupport ℝ hx,zero_apply,inner_zero_right,
    Finset.sum_const_zero]

/-- The divergence of a genuine compactly supported Lipschitz vector field
has integral zero, with the a.e. derivative justified by Rademacher. -/
theorem integral_divergence_compact {d:ℕ} {F:Space d→Space d} {K:ℝ≥0}
    (hF:LipschitzWith K F) (hc:HasCompactSupport F) :
    (∫x,divergence F x)=0 := by
  let e:=stdOrthonormalBasis ℝ (Space d)
  let f:=fun i x=>inner ℝ (e i) (F x)
  have hf i:LipschitzWith (‖innerSL ℝ (e i)‖₊*K) (f i):=
    (innerSL ℝ (e i)).lipschitzWith.comp hF
  have hfc i:HasCompactSupport (f i):=by
    apply HasCompactSupport.intro hc
    intro x hx
    simp only [f,image_eq_zero_of_notMem_tsupport hx,inner_zero_right]
  have he:divergence F =ᵐ[volume] (fun x=>∑i,fderiv ℝ (f i) x (e i)):=by
    filter_upwards [hF.ae_differentiableAt] with x hx
    unfold divergence
    apply Finset.sum_congr rfl
    intro i hi
    have hd:HasFDerivAt (f i) ((innerSL ℝ (e i)) ∘L fderiv ℝ F x) x:=
      (innerSL ℝ (e i)).hasFDerivAt.comp x hx.hasFDerivAt
    rw [hd.fderiv]
    rfl
  rw [integral_congr_ae he,integral_finsetSum _ (fun i hi=>integrable_directional_compact (hf i) (hfc i) (e i))]
  simp only [integral_directional_compact (hf _) (hfc _),Finset.sum_const_zero]
end Bernoulli.Foliation

end
end

end OAI
