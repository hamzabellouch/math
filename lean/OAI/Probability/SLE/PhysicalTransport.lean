import Mathlib
import OAI.Probability.SLE.DiskHalfPlane
import OAI.Probability.SLE.ChartMeasurability

namespace OAI

/-! Physical Transport for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
def SourceInteriorTraceDensityTarget : Prop :=
  ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
  Continuous U → IsCapacityTwoWitness U γ G F →
  ∀ s t : ℝ≥0, s < t → ∃ u ∈ Ioo s t, 0 < (γ u).im

lemma IsCapacityTwoWitness.survivingDomain_injective
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F) :
    Function.Injective (survivingDomain γ) := by
  intro s t he
  have hz : F s Complex.I ∈ survivingDomain γ s := by
    rcases h with ⟨hγ,h0,hupper,hG,hF,hGm,hFm,hrest⟩
    exact hFm s (by simp [upperHalfPlane])
  have ht : F s Complex.I ∈ survivingDomain γ t := he ▸ hz
  apply live_radius_unique hU h (F s Complex.I) s t hz ht
  exact le_antisymm (h.radius_le_of_domain_subset hU s t he.subset _ hz)
    (h.radius_le_of_domain_subset hU t s he.symm.subset _ ht)

theorem sourceInteriorTraceDensity_proved : SourceInteriorTraceDensityTarget := by
  intro U γ G F hU h s t hst
  by_contra hnone
  obtain ⟨b,hsb,hbt⟩ := exists_between hst
  obtain ⟨a,hsa,hab⟩ := exists_between hsb
  have hbase : upperHalfPlane \ (γ '' Icc 0 a) = upperHalfPlane \ (γ '' Icc 0 b) := by
    apply Subset.antisymm
    · intro z hz
      refine ⟨hz.1,?_⟩
      rintro ⟨u,hu,huz⟩
      by_cases hua : u ≤ a
      · exact hz.2 ⟨u,⟨hu.1,hua⟩,huz⟩
      · apply hnone
        refine ⟨u,⟨hsa.trans (not_le.mp hua),hu.2.trans_lt hbt⟩,?_⟩
        rw [huz]
        exact hz.1
    · intro z hz
      refine ⟨hz.1,?_⟩
      rintro ⟨u,hu,huz⟩
      exact hz.2 ⟨u,⟨hu.1,hu.2.trans hab.le⟩,huz⟩
  have he : survivingDomain γ a = survivingDomain γ b := by
    unfold survivingDomain
    rw [hbase]
  exact hab.ne (h.survivingDomain_injective hU he)

end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge
lemma source_flow_fence {g dg : ℝ → ℂ} {u : ℝ → ℝ} {a b c δ : ℝ}
    (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt g (dg t) (Ici t) t)
    (hu : ∀ t ∈ Ico a b, |u t-c| ≤ δ)
    (heq : ∀ t ∈ Ico a b, ‖dg t‖ ≤ 2 / ‖g t-(u t:ℂ)‖) :
    ‖g b-(c:ℂ)‖^2 ≤ ‖g a-(c:ℂ)‖^2+4*δ^2+9*(b-a) := by
  let f (t : ℝ) := ‖g t-(c:ℂ)‖^2
  let df (t : ℝ) := 2 * inner ℝ (g t-(c:ℂ)) (dg t)
  have hf : ContinuousOn f (Icc a b) := (hg.sub continuousOn_const).norm.pow 2
  have hdf (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt f (df t) (Ici t) t := (hd t ht |>.sub_const (c:ℂ)).norm_sq
  have hn (t : ℝ) (ht : t ∈ Ico a b) (hh : 4*δ^2 < f t) : df t < 9 := by
    have hr : 2*δ < ‖g t-(c:ℂ)‖ := by
      dsimp [f] at hh
      nlinarith [norm_nonneg (g t-(c:ℂ))]
    have htri : ‖g t-(c:ℂ)‖ ≤ ‖g t-(u t:ℂ)‖+δ := by
      calc
        _ ≤ ‖g t-(u t:ℂ)‖+‖(u t:ℂ)-(c:ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by
          have hc : ‖(u t:ℂ)-(c:ℂ)‖ ≤ δ := by simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hu t ht
          linarith
    have hp : 0 < ‖g t-(u t:ℂ)‖ := by nlinarith
    have hb : ‖g t-(c:ℂ)‖ ≤ 2*‖g t-(u t:ℂ)‖ := by linarith
    have hi := real_inner_le_norm (g t-(c:ℂ)) (dg t)
    have hm := mul_le_mul_of_nonneg_left (heq t ht) (norm_nonneg (g t-(c:ℂ)))
    have hx : ‖g t-(c:ℂ)‖ * (2 / ‖g t-(u t:ℂ)‖) ≤ 4 := by
      rw [← mul_div_assoc]
      exact (div_le_iff₀ hp).mpr (by linarith)
    change 2 * inner ℝ (g t-(c:ℂ)) (dg t) < 9
    linarith
  have hbound (ε : ℝ) (hε : 0 < ε) :
      f b ≤ f a+4*δ^2+ε+9*(b-a) := by
    apply image_le_of_deriv_right_lt_deriv_boundary hf hdf
      (B := fun t => f a+4*δ^2+ε+9*(t-a)) (B' := fun _ => 9)
      (by nlinarith [sq_nonneg δ])
      (fun t => by convert (((hasDerivAt_id t).sub_const a).const_mul 9).const_add (f a+4*δ^2+ε) using 1 <;> first | rfl | norm_num)
      (fun t ht he => ?_) ⟨hab,le_rfl⟩
    apply hn t ht
    have : 0 ≤ f a := sq_nonneg _
    rw [he]
    nlinarith [ht.1]
  apply le_of_forall_pos_le_add
  intro ε hε
  simpa only [f] using (hbound ε hε).trans_eq (by ring)
end SLEExactGauge

end

section
namespace SLEExactGauge
lemma IsCapacityTwoWitness.short_flow_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) {s T : ℝ≥0} (hs : s ≤ T)
    {z : ℂ} (hz : z ∈ survivingDomain γ T) {c δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ t ∈ Icc s T, |U t-c| ≤ δ) :
    ‖G T z-(c:ℂ)‖^2 ≤ ‖G s z-(c:ℂ)‖^2+4*δ^2+9*((T:ℝ)-s) := by
  have hsub : Icc (s:ℝ) T ⊆ Icc (0:ℝ) T := Icc_subset_Icc_left s.coe_nonneg
  have hb := source_flow_fence (g := fun u => G u.toNNReal z)
    (dg := fun u => 2/(G u.toNNReal z-(U u.toNNReal:ℂ)))
    (u := fun u => U u.toNNReal) (a := (s:ℝ)) (b := (T:ℝ)) (c := c)
    (NNReal.coe_le_coe.mpr hs) hδ ((h.time_continuousOn T z hz).mono hsub)
    (fun u hu => hasDerivWithinAt_Ici_of_Icc hu ((h.time_derivative T z hz u
      (hsub ⟨hu.1,hu.2.le⟩)).mono hsub))
    (fun u hu => hU u.toNNReal ⟨by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ (s.coe_nonneg.trans hu.1)]
      exact hu.1, Real.toNNReal_le_iff_le_coe.mpr hu.2.le⟩)
    (fun u hu => by simp)
  simpa only [Real.toNNReal_coe] using hb

lemma IsCapacityTwoWitness.short_reverse_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) {s T : ℝ≥0} (hs : s ≤ T)
    {z : ℂ} (hz : z ∈ survivingDomain γ T) {c δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ t ∈ Icc s T, |U t-c| ≤ δ) :
    ‖G s z-(c:ℂ)‖^2 ≤ ‖G T z-(c:ℂ)‖^2+4*δ^2+9*((T:ℝ)-s) := by
  have hm (u : ℝ) (hu : u ∈ Icc (0:ℝ) ((T:ℝ)-s)) :
      (T:ℝ)-u ∈ Icc (s:ℝ) T := by constructor <;> linarith [hu.1,hu.2]
  have hm' (u : ℝ) (hu : u ∈ Icc (0:ℝ) ((T:ℝ)-s)) :
      (T:ℝ)-u ∈ Icc (0:ℝ) T := ⟨s.coe_nonneg.trans (hm u hu).1,(hm u hu).2⟩
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) ((T:ℝ)-s)) :
      HasDerivWithinAt (fun v : ℝ => G ((T:ℝ)-v).toNNReal z)
        (-(2/(G ((T:ℝ)-u).toNNReal z-(U ((T:ℝ)-u).toNNReal:ℂ))))
        (Icc 0 ((T:ℝ)-s)) u := by
    have hi : HasDerivWithinAt (fun v : ℝ => (T:ℝ)-v) (-1)
        (Icc 0 ((T:ℝ)-s)) u := by
      convert ((hasDerivAt_id u).const_sub (T:ℝ)).hasDerivWithinAt using 1
      rfl
    have hh := (h.time_derivative T z hz _ (hm' u hu)).scomp u hi
      (fun v hv => hm' v hv)
    simpa only [neg_smul, one_smul, Function.comp_def] using hh
  have hc : ContinuousOn (fun u : ℝ => G ((T:ℝ)-u).toNNReal z)
      (Icc (0:ℝ) ((T:ℝ)-s)) :=
    (h.time_continuousOn T z hz).comp (continuousOn_const.sub continuousOn_id) hm'
  have hb := source_flow_fence (g := fun u => G ((T:ℝ)-u).toNNReal z)
    (dg := fun u => -(2/(G ((T:ℝ)-u).toNNReal z-(U ((T:ℝ)-u).toNNReal:ℂ))))
    (u := fun u => U ((T:ℝ)-u).toNNReal) (a := 0) (b := (T:ℝ)-s) (c := c)
    (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hs)) hδ hc
    (fun u hu => hasDerivWithinAt_Ici_of_Icc hu (hd u ⟨hu.1,hu.2.le⟩))
    (fun u hu => hU _ (by
      constructor
      · apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ (hm' u ⟨hu.1,hu.2.le⟩).1]
        exact (hm u ⟨hu.1,hu.2.le⟩).1
      · exact Real.toNNReal_le_iff_le_coe.mpr (hm u ⟨hu.1,hu.2.le⟩).2))
    (fun u hu => by simp)
  simpa only [sub_sub_cancel,sub_zero, Real.toNNReal_coe] using hb
end SLEExactGauge

end

section
namespace SLEExactGauge
lemma IsCapacityTwoWitness.earlier_tip_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) {s T : ℝ≥0} (hs : s ≤ T)
    (ha : γ T ∈ survivingDomain γ s) {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ t ∈ Icc s T, |U t-U T| ≤ δ) :
    ‖G s (γ T)-(U T:ℂ)‖^2 ≤ 4*δ^2+9*((T:ℝ)-s) := by
  have htip := h.2.2.2.2.2.2.2.2.2.2.2.2
  have hlim := (h.spatial_differentiableAt s (γ T) ha).continuousAt.tendsto.comp (htip T)
  have hleft := ((hlim.sub (tendsto_const_nhds (x := (U T:ℂ)))).norm).pow 2
  have hright : Tendsto (fun y : ℝ =>
      ‖((U T:ℂ)+(y:ℂ)*Complex.I)-(U T:ℂ)‖^2+4*δ^2+9*((T:ℝ)-s))
      (𝓝[>] 0) (𝓝 (4*δ^2+9*((T:ℝ)-s))) := by
    have hc : Continuous (fun y : ℝ =>
      ‖((U T:ℂ)+(y:ℂ)*Complex.I)-(U T:ℂ)‖^2+4*δ^2+9*((T:ℝ)-s)) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hiy : (U T:ℂ)+(y:ℂ)*Complex.I ∈ upperHalfPlane := by
    simpa [upperHalfPlane] using hy
  have hf := h.2.2.2.2.2.2.1 T hiy
  have hi := h.2.2.2.2.2.2.2.2.1 T _ hiy
  convert h.short_reverse_bound hs hf hδ hU using 1 <;> first | rfl | simp only [hi]
end SLEExactGauge

end

section
namespace SLEExactGauge
lemma IsCapacityTwoWitness.fresh_tip_chart_tendsto
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (hUc : Continuous U)
    {T : ℝ≥0} (hT : 0 < T)
    (ha : ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s) :
    Tendsto (G T) (𝓝[survivingDomain γ T] (γ T)) (𝓝 (U T:ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ρ,hρ,hosc⟩ := Metric.continuousAt_iff.mp (hUc.continuousAt (x := T)) (ε/10) (by positivity)
  let η : ℝ := min ((T:ℝ)/2) (min (ρ/2) (ε^2/100))
  have hη : 0 < η := lt_min (by exact div_pos (NNReal.coe_pos.mpr hT) (by norm_num))
    (lt_min (by positivity) (by positivity))
  have hηT : η ≤ (T:ℝ)/2 := min_le_left _ _
  have hηρ : η ≤ ρ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηε : η ≤ ε^2/100 := (min_le_right _ _).trans (min_le_right _ _)
  let s : ℝ≥0 := ⟨(T:ℝ)-η,by linarith [T.coe_nonneg]⟩
  have hs : s < T := by change (T:ℝ)-η < T; linarith
  have hdiff : (T:ℝ)-s = η := by change (T:ℝ)-((T:ℝ)-η)=η; ring
  have hosc' (t : ℝ≥0) (ht : t ∈ Icc s T) : |U t-U T| ≤ ε/10 := by
    have hdist : dist t T < ρ := by
      rw [NNReal.dist_eq,abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr ht.2))]
      have ht' : (T:ℝ)-η ≤ t := NNReal.coe_le_coe.mpr ht.1
      linarith
    simpa only [Real.dist_eq] using (hosc hdist).le
  have hbound := h.earlier_tip_bound hs.le (ha s hs) (by positivity : 0 ≤ ε/10) hosc'
  rw [hdiff] at hbound
  have hnorm : ‖G s (γ T)-(U T:ℂ)‖ < ε/2 := by
    nlinarith [norm_nonneg (G s (γ T)-(U T:ℂ))]
  have hev : ∀ᶠ w in 𝓝 (γ T), ‖G s w-(U T:ℂ)‖ < ε/2 :=
    ((h.spatial_differentiableAt s (γ T) (ha s hs)).continuousAt.sub continuousAt_const).norm
      |>.eventually (isOpen_Iio.mem_nhds hnorm)
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwt
  have hh := h.short_flow_bound hs.le hwt (by positivity : 0 ≤ ε/10) hosc'
  rw [hdiff] at hh
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (G s w-(U T:ℂ)), norm_nonneg (G T w-(U T:ℂ))]
end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge
 

def SourceFirstHitPhysicalAccessTarget : Prop :=
  ∀ (γ : ℝ≥0 → ℂ), Continuous γ →
  ∀ (s τ : ℝ≥0) (z : ℂ) (r : ℝ), 0 < r →
    Metric.closedBall z r ⊆ survivingDomain γ s → s ≤ τ →
    dist (γ τ) z = r →
    (∀ t ∈ Ico s τ, dist (γ t) z ≠ r) → z ∈ survivingDomain γ τ →
    (∀ t : ℝ≥0, t < τ → γ t ≠ γ τ) ∧
    Metric.ball z r ⊆ survivingDomain γ τ ∧
    (∀ v ∈ Ioc (0:ℝ) 1, (1-v) • γ τ + v • z ∈ survivingDomain γ τ)

lemma disk_distance_gt_before_first_hit (γ : ℝ≥0 → ℂ) (hc : Continuous γ)
    (s τ : ℝ≥0) (z : ℂ) (r : ℝ)
    (hfree : Metric.closedBall z r ⊆ survivingDomain γ s)
    (hfirst : ∀ t ∈ Ico s τ, dist (γ t) z ≠ r)
    (t : ℝ≥0) (ht : t < τ) : r < dist (γ t) z := by
  have hold (u : ℝ≥0) (hu : u ≤ s) : r < dist (γ u) z := by
    by_contra hn
    have hu' : γ u ∈ Metric.closedBall z r := by
      simpa only [Metric.mem_closedBall] using not_lt.mp hn
    have hh := hfree hu'
    exact hh.1.2 ⟨u,⟨zero_le,hu⟩,rfl⟩
  by_cases hts : t ≤ s
  · exact hold t hts
  · by_contra hn
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc' (not_le.mp hts).le
      ((hc.dist continuous_const).continuousOn) (show r ∈ Icc (dist (γ t) z) (dist (γ s) z)
        from ⟨not_lt.mp hn,(hold s le_rfl).le⟩)
    exact hfirst u ⟨hu.1,hu.2.trans_lt ht⟩ he

lemma radialAccess_mem_ball (a z : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : dist a z = r) (v : ℝ) (hv : v ∈ Ioc (0:ℝ) 1) :
    (1-v) • a + v • z ∈ Metric.ball z r := by
  rw [Metric.mem_ball,dist_eq_norm]
  have he : (1-v) • a + v • z-z = (1-v) • (a-z) := by module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hv.2),← dist_eq_norm,ha]
  nlinarith [hv.1]

theorem sourceFirstHitPhysicalAccess : SourceFirstHitPhysicalAccessTarget := by
  intro γ hc s τ z r hr hfree hsτ hhit hfirst hz
  have hprior := disk_distance_gt_before_first_hit γ hc s τ z r hfree hfirst
  have hball : Metric.ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 τ) := by
    intro w hw
    refine ⟨(hfree (Metric.ball_subset_closedBall hw)).1.1,?_⟩
    rintro ⟨t,ht,rfl⟩
    have hlt : dist (γ t) z < r := hw
    rcases lt_or_eq_of_le ht.2 with htτ | rfl
    · exact (not_lt_of_ge (hprior t htτ).le) hlt
    · rw [hhit] at hlt
      exact lt_irrefl _ hlt
  have hcc := (convex_ball z r).isPreconnected.subset_connectedComponentIn
    (Metric.mem_ball_self hr) hball
  have hsurv : Metric.ball z r ⊆ survivingDomain γ τ := by
    intro w hw
    refine ⟨hball hw,?_⟩
    rw [← connectedComponentIn_eq (hcc hw)]
    exact hz.2
  refine ⟨?_,hsurv,?_⟩
  · intro t ht he
    have hh := hprior t ht
    rw [he,hhit] at hh
    exact lt_irrefl _ hh
  · intro v hv
    exact hsurv (radialAccess_mem_ball (γ τ) z r hr hhit v hv)

end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge
 

def SourceFirstHitChartAccessTarget : Prop :=
  ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
    Continuous U → IsCapacityTwoWitness U γ G F →
    ∀ (s τ : ℝ≥0) (z : ℂ) (r : ℝ), 0 < r →
      Metric.closedBall z r ⊆ survivingDomain γ s → s ≤ τ →
      dist (γ τ) z = r → (∀ t ∈ Ico s τ, dist (γ t) z ≠ r) →
      z ∈ survivingDomain γ τ →
      Tendsto (fun v : ℝ => G τ ((1-v) • γ τ + v • z) - (U τ : ℂ))
        (𝓝[>] 0) (𝓝 0)

end SLEExactGauge

end

section
namespace SLEExactGauge
lemma first_hit_tip_survives_earlier (γ : ℝ≥0 → ℂ) (hc : Continuous γ)
    (s τ : ℝ≥0) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hfree : Metric.closedBall z r ⊆ survivingDomain γ s)
    (hhit : dist (γ τ) z = r)
    (hfirst : ∀ t ∈ Ico s τ, dist (γ t) z ≠ r)
    (hz : z ∈ survivingDomain γ τ) :
    ∀ u : ℝ≥0, u < τ → γ τ ∈ survivingDomain γ u := by
  intro u hu
  have hprior := disk_distance_gt_before_first_hit γ hc s τ z r hfree hfirst
  have hclosed : Metric.closedBall z r ⊆ upperHalfPlane \ (γ '' Icc 0 u) := by
    intro w hw
    refine ⟨(hfree hw).1.1,?_⟩
    rintro ⟨t,ht,rfl⟩
    exact (not_le_of_gt (hprior t (ht.2.trans_lt hu))) (Metric.mem_closedBall.mp hw)
  have hcc := (convex_closedBall z r).isPreconnected.subset_connectedComponentIn
    (Metric.mem_closedBall_self hr.le) hclosed
  have hmem : γ τ ∈ Metric.closedBall z r := Metric.mem_closedBall.mpr hhit.le
  refine ⟨hclosed hmem,?_⟩
  rw [← connectedComponentIn_eq (hcc hmem)]
  exact (survivingDomain_antitone γ hu.le hz).2

theorem sourceFirstHitChartAccess_proved : SourceFirstHitChartAccessTarget := by
  intro U γ G F hUc h s τ z r hr hfree hsτ hhit hfirst hz
  have hslt : s < τ := by
    apply lt_of_le_of_ne hsτ
    intro he
    have hm := hfree (Metric.mem_closedBall.mpr hhit.le)
    exact hm.1.2 ⟨τ,⟨zero_le,by rw [he]⟩,rfl⟩
  have hT : 0 < τ := lt_of_le_of_lt (show (0:ℝ≥0) ≤ s from zero_le) hslt
  have ha := first_hit_tip_survives_earlier γ h.1 s τ z r hr hfree hhit hfirst hz
  have hlim := h.fresh_tip_chart_tendsto hUc hT ha
  have hradial := (sourceFirstHitPhysicalAccess γ h.1 s τ z r hr hfree hsτ hhit hfirst hz).2.2
  have hcont : Continuous (fun v : ℝ => (1-v) • γ τ + v • z) := by fun_prop
  have hpath : Tendsto (fun v : ℝ => (1-v) • γ τ + v • z) (𝓝[>] 0)
      (𝓝[survivingDomain γ τ] (γ τ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · have hev : ∀ᶠ v : ℝ in 𝓝[>] 0, v < 1 :=
        (eventually_lt_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin,hev] with v hv hv'
      exact hradial v ⟨hv,hv'.le⟩
  simpa only [Function.comp_def,sub_self] using
    (hlim.comp hpath).sub (tendsto_const_nhds (x := (U τ:ℂ)))
end SLEExactGauge

end
end

end OAI
