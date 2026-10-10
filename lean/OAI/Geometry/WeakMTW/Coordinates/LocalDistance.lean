import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalFlowLength
import OAI.Geometry.WeakMTW.Coordinates.ChartLength

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold

namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
open NormalNeighborhood NormalFlow ChartMetric
variable (x z : M) {y₀ : E}
variable (N : NormalFlow (metric x) (chartAt E x).target y₀)

def normalChart : OpenPartialHomeomorph E M :=
  (N.normalAt (chartAt E x z)).trans (chartAt E x).symm

omit [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
@[simp] theorem normalChart_apply (v : E) : normalChart x z N v =
    (chartAt E x).symm (N.normalAt (chartAt E x z) v) := rfl

omit [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
@[simp] theorem normalChart_source : (normalChart x z N).source = (N.normalAt (chartAt E x z)).source := by
  ext v
  constructor
  · exact fun hv => hv.1
  · exact fun hv => ⟨hv, N.normalAt_mem hv⟩

@[simp] theorem normalChart_zero (hz : z ∈ (chartAt E x).source)
    (hzero : (0 : E) ∈ (N.normalAt (chartAt E x z)).source) : normalChart x z N 0 = z := by
  rw [normalChart_apply, N.normalAt_zero (chartAt E x).open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) hzero]
  exact (chartAt E x).left_inv hz

theorem normalChart_target_center (hz : z ∈ (chartAt E x).source)
    (hzero : (0 : E) ∈ (N.normalAt (chartAt E x z)).source) :
    z ∈ (normalChart x z N).target := by
  have hm := (normalChart x z N).map_source
    (show (0 : E) ∈ (normalChart x z N).source by rw [normalChart_source]; exact hzero)
  simpa only [normalChart_zero x z N hz hzero] using hm

theorem edist_normalChart_le [IsRiemannianManifold 𝓘(ℝ, E) M]
    (hz : z ∈ (chartAt E x).source) {v : E} (hv : v ∈ (normalChart x z N).source) :
    edist z (normalChart x z N v) ≤
      ENNReal.ofReal (N.time * Real.sqrt (metric x (chartAt E x z) v v)) := by
  rw [normalChart_source] at hv
  let c : ℝ → E := fun t => (N.flow (t, (chartAt E x z, v))).1
  have hc : ContDiffOn ℝ 1 c (Icc (0 : ℝ) N.time) :=
    (N.flow_curve_smooth hv).of_le (by simp)
  have hct : ∀ t ∈ Icc (0 : ℝ) N.time, c t ∈ (chartAt E x).target :=
    fun t ht => (N.ode _ (N.source_stays (_, v) hv t ht)).1
  have hmc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ((chartAt E x).symm ∘ c)
      (Icc (0 : ℝ) N.time) :=
    contMDiffOn_chart_symm.comp (contMDiffOn_iff_contDiffOn.mpr hc) hct
  have hfirst : ((chartAt E x).symm ∘ c) 0 = z := by
    simp only [Function.comp_apply, c, N.initial (_, v)
      (N.source_stays (_, v) hv 0 ⟨le_rfl, N.time_pos.le⟩)]
    exact (chartAt E x).left_inv hz
  have hlast : ((chartAt E x).symm ∘ c) N.time = normalChart x z N v := by
    rw [normalChart_apply, N.normalAt_apply]
    rfl
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, E))]
  have h := riemannianEDist_le_pathELength hmc hfirst hlast N.time_pos.le
  rw [← coordinateLength_eq_pathELength x hc hct] at h
  exact h.trans_eq (N.flow_curve_length (chartAt E x).open_target (metric_smooth x)
    (fun z _ => metric_symmetric x z) (fun z hz v hv => metric_positive x hz hv) hv)

theorem radial_path_length {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc a b))
    (ht : ∀ t ∈ Icc a b, γ t ∈ (normalChart x z N).target) :
    ‖N.time * Real.sqrt (metric x (chartAt E x z)
        ((normalChart x z N).symm (γ b)) ((normalChart x z N).symm (γ b))) -
      N.time * Real.sqrt (metric x (chartAt E x z)
        ((normalChart x z N).symm (γ a)) ((normalChart x z N).symm (γ a)))‖ₑ ≤
      pathELength 𝓘(ℝ, E) γ a b := by
  let c : ℝ → E := (chartAt E x) ∘ γ
  have hct : ∀ t ∈ Icc a b, γ t ∈ (chartAt E x).source := fun t ht' => (ht t ht').1
  have hcn : ∀ t ∈ Icc a b, c t ∈ (N.normalAt (chartAt E x z)).target :=
    fun t ht' => (ht t ht').2
  have hc : ContDiffOn ℝ 1 c (Icc a b) :=
    contMDiffOn_iff_contDiffOn.mp (contMDiffOn_chart.comp hγ hct)
  have h := N.radial_length (chartAt E x).open_target (metric_smooth x)
    (fun z _ => metric_symmetric x z) (fun z hz v hv => metric_positive x hz hv) hab hc hcn
  rw [coordinateLength_eq_pathELength x hc
    (fun t ht' => (chartAt E x).map_source (hct t ht'))] at h
  have heq : pathELength 𝓘(ℝ, E) ((chartAt E x).symm ∘ c) a b =
      pathELength 𝓘(ℝ, E) γ a b :=
    pathELength_congr (fun t ht' => (chartAt E x).left_inv (hct t ht'))
  rw [heq] at h
  exact h

theorem normal_distance_of_ball [IsRiemannianManifold 𝓘(ℝ, E) M]
    (hz : z ∈ (chartAt E x).source)
    (hzero : (0 : E) ∈ (N.normalAt (chartAt E x z)).source)
    {r : ℝ} (hr : 0 < r) (hrs : Metric.ball z r ⊆ (normalChart x z N).target)
    {v : E} (hv : v ∈ (normalChart x z N).source)
    (hvr : N.time * Real.sqrt (metric x (chartAt E x z) v v) < r) :
    dist z (normalChart x z N v) = N.time * Real.sqrt (metric x (chartAt E x z) v v) := by
  let R : ℝ := N.time * Real.sqrt (metric x (chartAt E x z) v v)
  have hR : 0 ≤ R := mul_nonneg N.time_pos.le (Real.sqrt_nonneg _)
  have hu : dist z (normalChart x z N v) ≤ R := by
    have h := edist_normalChart_le x z N hz hv
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR] at h
    exact h
  apply le_antisymm hu
  by_contra hn
  have hlt : dist z (normalChart x z N v) < R := lt_of_not_ge hn
  have hRpos : 0 < R := lt_of_le_of_lt dist_nonneg hlt
  have he : riemannianEDist 𝓘(ℝ, E) z (normalChart x z N v) < ENNReal.ofReal R := by
    rw [← IsRiemannianManifold.out, edist_dist, ENNReal.ofReal_lt_ofReal_iff hRpos]
    exact hlt
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt he zero_lt_one
  have ht : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (normalChart x z N).target := by
    intro t ht'
    apply hrs
    rw [Metric.mem_ball, dist_comm]
    have hp := riemannianEDist_le_pathELength (hγ.contMDiffOn :
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc (0 : ℝ) t)) h0 rfl ht'.1
    rw [← IsRiemannianManifold.out] at hp
    have hb := hp.trans (pathELength_mono (I := 𝓘(ℝ, E)) (γ := γ) le_rfl ht'.2)
    have hd : edist z (γ t) < ENNReal.ofReal r :=
      (hb.trans_lt hlen).trans_le (ENNReal.ofReal_le_ofReal hvr.le)
    rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hr] at hd
  have hl := radial_path_length x z N zero_le_one hγ.contMDiffOn ht
  rw [h0, h1, (normalChart x z N).left_inv hv] at hl
  have hi : (normalChart x z N).symm z = 0 := by
    have hm := (normalChart x z N).left_inv
      (show (0 : E) ∈ (normalChart x z N).source by rw [normalChart_source]; exact hzero)
    simpa only [normalChart_zero x z N hz hzero] using hm
  rw [hi] at hl
  simp only [map_zero, Real.sqrt_zero, mul_zero, sub_zero] at hl
  have hnR : ‖R‖ₑ = ENNReal.ofReal R := by rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hR]
  change ‖R‖ₑ ≤ _ at hl
  rw [hnR] at hl
  exact not_lt_of_ge hl hlen

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
