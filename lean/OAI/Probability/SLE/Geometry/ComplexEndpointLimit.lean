import OAI.Probability.SLE.Geometry.ComplexEndpointCluster

namespace OAI

/-! A bounded upper-half-plane path has a real endpoint limit when its
continuous image has a limit and the corresponding boundary fiber has no
interval. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology

namespace SLEExactGauge

lemma real_cluster_in_boundary_fiber {α : Type*} {l : Filter α}
    {f : α → ℂ} {B : ℂ → ℂ} {a : ℝ} {b : ℂ}
    (hB : ContinuousOn B {z : ℂ | 0≤z.im})
    (hmem : ∀ᶠ x in l, 0≤(f x).im)
    (him : Tendsto (fun x => (f x).im) l (𝓝 0))
    (himage : Tendsto (fun x => B (f x)) l (𝓝 b))
    (ha : MapClusterPt a l (fun x => (f x).re)) : B (a:ℂ)=b := by
  have hca := complex_cluster_of_real_cluster him ha
  have hle : 𝓝 (a:ℂ) ⊓ map f l ≤ 𝓝[{z : ℂ | 0≤z.im}] (a:ℂ) :=
    le_inf inf_le_left (inf_le_right.trans (tendsto_principal.mpr hmem))
  have hcont : Tendsto B (𝓝[{z : ℂ | 0≤z.im}] (a:ℂ)) (𝓝 (B (a:ℂ))) := hB _ (by simp)
  have hc := MapClusterPt.tendsto_comp' (hcont.mono_left hle) hca
  exact cluster_value_eq_limit hc himage

theorem exists_complex_endpoint_limit {f : ℝ → ℂ} {B : ℂ → ℂ} {b : ℂ} {D M : ℝ}
    (hD : 0<D) (hf : ContinuousOn f (Ioo 0 D))
    (hbound : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ‖f t‖≤M)
    (hmem : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), 0≤(f t).im)
    (him : Tendsto (fun t => (f t).im) (𝓝[>] (0:ℝ)) (𝓝 0))
    (hB : ContinuousOn B {z : ℂ | 0≤z.im})
    (himage : Tendsto (fun t => B (f t)) (𝓝[>] (0:ℝ)) (𝓝 b))
    (hno : ∀ a d : ℝ, a<d → ¬ ∀ c∈Ioo a d, B (c:ℂ)=b) :
    ∃ a : ℝ, Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (a:ℂ)) ∧ B (a:ℂ)=b := by
  have hrbound : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), (f t).re∈Icc (-M) M := by
    filter_upwards [hbound] with t ht
    exact abs_le.mp ((abs_re_le_norm (f t)).trans ht)
  have hnoCluster : ∀ a d : ℝ, a<d →
      ¬ ∀ c∈Ioo a d, MapClusterPt c (𝓝[>] (0:ℝ)) (fun t => (f t).re) := by
    intro a d had hc
    apply hno a d had
    intro c hcd
    exact real_cluster_in_boundary_fiber hB hmem him himage (hc c hcd)
  obtain ⟨a,_,ha⟩ := exists_endpoint_limit_of_no_cluster_interval hD
    (continuous_re.comp_continuousOn hf) isCompact_Icc hrbound hnoCluster
  have hcomplex : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (a:ℂ)) := by
    have hh := (continuous_ofReal.continuousAt.tendsto.comp ha).add
      ((continuous_ofReal.continuousAt.tendsto.comp him).mul_const I)
    simpa only [Function.comp_apply,ofReal_zero,zero_mul,add_zero,re_add_im] using hh
  refine ⟨a,hcomplex,?_⟩
  exact real_cluster_in_boundary_fiber hB hmem him himage ha.mapClusterPt

end SLEExactGauge

end

end OAI
