import Mathlib
import OAI.Analysis.PathSelection.ContourPolynomials
import OAI.Analysis.PathSelection.FunctionSeries

namespace OAI

/-! Compact analytic profiles and parameter-dependent contour integrals. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace DegeneratingTrees
open Set Metric Filter Topology

 

def radialClip (a : ℝ) (z : ℂ) : ℂ := (a / max a ‖z‖) • z

theorem continuous_radialClip {a : ℝ} (ha : 0 < a) : Continuous (radialClip a) := by
  unfold radialClip
  exact (continuous_const.div (continuous_const.max continuous_norm)
    (fun z => ne_of_gt (ha.trans_le (le_max_left a ‖z‖)))).smul continuous_id

theorem norm_radialClip_le {a : ℝ} (ha : 0 < a) (z : ℂ) : ‖radialClip a z‖ ≤ a := by
  rw [radialClip, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hm : 0 < max a ‖z‖ := ha.trans_le (le_max_left _ _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le

theorem radialClip_eq {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : ‖z‖ ≤ a) :
    radialClip a z = z := by
  simp [radialClip, max_eq_left hz, ne_of_gt ha]

 

theorem localized_profile {A K : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [TopologicalSpace K] [CompactSpace K] (h : C(K, ℂ)) {q₀ : A} {z₀ : ℂ}
    {F : A × ℂ → ℂ} (hF : AnalyticAt ℂ F (q₀,z₀)) :
    ∃ (a : ℝ) (φ : A → C(K, ℂ)), 0 < a ∧ AnalyticAt ℂ φ q₀ ∧
      ∀ᶠ q in 𝓝 q₀, ∀ t : K, ‖h t - z₀‖ < a → φ q t = F (q, h t) := by
  let H : A × ℂ → ℂ := fun v => F ((q₀,z₀) + v)
  have hH : AnalyticAt ℂ H 0 := by
    apply hF.comp_of_eq (analyticAt_const.add analyticAt_id)
    simp
  obtain ⟨p,R,hp⟩ := hH
  obtain ⟨b,hb0,hbR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hb : (0 : ℝ) < b := by exact_mod_cast hb0
  let a : ℝ := b / 2
  have ha : 0 < a := half_pos hb
  let w : C(K, A × ℂ) := ⟨fun t => (0,radialClip a (h t-z₀)),
    continuous_const.prodMk ((continuous_radialClip ha).comp (h.continuous.sub continuous_const))⟩
  let L : A →L[ℂ] C(K, A × ℂ) :=
    (ContinuousLinearMap.const ℂ K).comp (ContinuousLinearMap.inl ℂ A ℂ)
  let v : A → C(K,A × ℂ) := fun q => L (q-q₀) + w
  have hve (q : A) (t : K) : v q t = (q-q₀, radialClip a (h t-z₀)) := by
    simp [v, L, w]
  have hva : AnalyticAt ℂ v q₀ :=
    ((L.analyticAt _).comp (analyticAt_id.sub analyticAt_const)).add analyticAt_const
  have hvb (q : A) (hq : q ∈ ball q₀ a) : v q ∈ ball 0 (b : ℝ) := by
    have hnq : ‖q-q₀‖ < a := by simpa [dist_eq_norm] using hq
    have hnv : ‖v q‖ ≤ a := by
      apply (ContinuousMap.norm_le _ ha.le).2
      intro t
      rw [hve]
      rw [Prod.norm_def]
      exact max_le hnq.le (norm_radialClip_le ha _)
    have : ‖v q‖ < (b : ℝ) := hnv.trans_lt (half_lt_self hb)
    simpa using this
  obtain ⟨Φ,hΦ,hΦe⟩ := analytic_continuousMap_of_series (K := K) hp hbR
  refine ⟨a, fun q => Φ (v q), ha, (hΦ _ (hvb q₀ (mem_ball_self ha))).comp hva, ?_⟩
  filter_upwards [ball_mem_nhds q₀ ha] with q hq
  intro t ht
  rw [hΦe _ (hvb q hq), hve]
  change F ((q₀,z₀)+(q-q₀,radialClip a (h t-z₀))) = F (q,h t)
  rw [radialClip_eq ha ht.le]
  congr 1
  ext <;> simp

 

theorem analytic_compact_profile {A K : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [TopologicalSpace K] [CompactSpace K] [T2Space K] (h : C(K,ℂ)) {q₀ : A}
    {F : A × ℂ → ℂ} (hF : ∀ t : K, AnalyticAt ℂ F (q₀,h t)) :
    ∃ φ : A → C(K,ℂ), AnalyticAt ℂ φ q₀ ∧
      ∀ᶠ q in 𝓝 q₀, ∀ t : K, φ q t = F (q,h t) := by
  classical
  choose a φ ha hφ he using fun t => localized_profile h (hF t)
  let V : K → Set K := fun t => {x | ‖h x-h t‖ < a t}
  have hVo (t : K) : IsOpen (V t) :=
    isOpen_lt ((h.continuous.sub continuous_const).norm) continuous_const
  have hVc : (univ : Set K) ⊆ ⋃ t, V t := by
    intro t _
    exact mem_iUnion.2 ⟨t, by simpa [V] using ha t⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover V hVo hVc
  let I := {t // t ∈ s}
  have hIc : (univ : Set K) ⊆ ⋃ t : I, V t := by
    intro x hx
    obtain ⟨t,ht,hxt⟩ := mem_iUnion₂.1 (hs hx)
    exact mem_iUnion.2 ⟨⟨t,ht⟩,hxt⟩
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun t : I => V t) (fun t => hVo t) hIc
  let χ : I → C(K,ℂ) := fun t => ⟨fun x => (ρ t x : ℂ), Complex.continuous_ofReal.comp (ρ t).continuous⟩
  let ψ : A → C(K,ℂ) := fun q => ∑ t : I, χ t * φ t q
  refine ⟨ψ, ?_, ?_⟩
  · convert (Finset.analyticAt_sum (𝕜 := ℂ)
        (f := fun t : I => fun q => χ t * φ (t : K) q)
        Finset.univ (fun t _ => analyticAt_const.mul (hφ t))) using 1
    ext q t
    simp [ψ]
  · have hev : ∀ᶠ q in 𝓝 q₀, ∀ t : I, ∀ x : K, ‖h x-h t‖ < a t → φ t q x = F (q,h x) :=
      Filter.eventually_all.2 (fun t : I => he t)
    filter_upwards [hev] with q hq
    intro x
    have heq (t : I) : χ t x * φ t q x = (ρ t x : ℂ) * F (q,h x) := by
      by_cases ht : ρ t x = 0
      · simp [χ, ht]
      · have hx : x ∈ V t := hρ t (subset_closure ht)
        rw [hq t x hx]
        rfl
    change (∑ t : I, χ t * φ t q) x = _
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, heq]
    rw [← Finset.sum_mul]
    have hsum : ∑ t : I, (ρ t x : ℂ) = 1 := by
      exact_mod_cast (show ∑ t : I, ρ t x = 1 from by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x))
    rw [hsum, one_mul]

end DegeneratingTrees

namespace DegeneratingTrees
open Set Metric Filter Topology

 

def compactProfile {A K : Type*} [TopologicalSpace K] (h : C(K,ℂ))
    (F : A × ℂ → ℂ) (q : A) : C(K,ℂ) := by
  classical
  exact if hc : Continuous (fun t : K => F (q,h t)) then ⟨_,hc⟩ else 0

theorem compactProfile_apply {A K : Type*} [TopologicalSpace K] (h : C(K,ℂ))
    (F : A × ℂ → ℂ) (q : A) (hc : Continuous (fun t : K => F (q,h t))) (t : K) :
    compactProfile h F q t = F (q,h t) := by
  simp [compactProfile, hc]

theorem analytic_compactProfile {A K : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [TopologicalSpace K] [CompactSpace K] [T2Space K] (h : C(K,ℂ)) {U : Set A}
    (hU : IsOpen U) {F : A × ℂ → ℂ}
    (hF : ∀ q ∈ U, ∀ t : K, AnalyticAt ℂ F (q,h t)) :
    AnalyticOnNhd ℂ (compactProfile h F) U := by
  intro q hq
  obtain ⟨φ,hφ,he⟩ := analytic_compact_profile h (hF q hq)
  apply hφ.congr
  filter_upwards [he,hU.mem_nhds hq] with x hx hxU
  have hc : Continuous (fun t : K => F (x,h t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hF x hxU t).continuousAt.comp (f := fun point : K => (x,h point))
      (continuous_const.prodMk h.continuous).continuousAt
  ext t
  rw [compactProfile_apply h F x hc t]
  exact hx t

theorem analytic_circleIntegral {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {U : Set A} (hU : IsOpen U) {r : ℝ} (hr : 0 ≤ r) {F : A × ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere 0 r)) :
    AnalyticOnNhd ℂ (fun q => ∮ z in C(0,r), F (q,z)) U := by
  let h : C(sphere (0 : ℂ) r,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  have ha : AnalyticOnNhd ℂ (compactProfile h F) U :=
    analytic_compactProfile h hU (fun q hq t => hF _ ⟨hq,t.property⟩)
  have hc (q : A) (hq : q ∈ U) : Continuous (fun t : sphere (0 : ℂ) r => F (q,t)) :=
    hF.continuousOn.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun t => ⟨hq,t.property⟩)
  intro q hq
  apply ((circleFunctional r hr).analyticAt _ |>.comp (ha q hq)).congr
  filter_upwards [hU.mem_nhds hq] with x hx
  exact circleFunctional_eq hr _ _ (compactProfile_apply h F x (hc x hx))

end DegeneratingTrees

namespace DegeneratingTrees
open Set Metric Filter Topology Complex
open scoped BigOperators

 

theorem analytic_contourMoment_general {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    {F : A × ℂ → ℂ} {U : Set A} (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere 0 r))
    (hn : ∀ q ∈ U, ∀ z ∈ sphere (0 : ℂ) r, F (q,z) ≠ 0) (k : ℕ) :
    AnalyticOnNhd ℂ (fun q => contourMoment (fun y => F (q,y)) r k) U := by
  let H : A × ℂ → ℂ := fun x => x.2 ^ k * fderiv ℂ F x (0,1) / F x
  have hH : AnalyticOnNhd ℂ H (U ×ˢ sphere 0 r) := by
    intro x hx
    exact ((analyticAt_snd.pow k).mul
      (((ContinuousLinearMap.apply ℂ ℂ ((0,1) : A × ℂ)).analyticAt _).comp
        (hF x hx).fderiv)).div (hF x hx) (hn x.1 hx.1 x.2 hx.2)
  have ha := analytic_circleIntegral hU hr.le hH
  intro q hq
  apply (analyticAt_const.mul (ha q hq)).congr
  filter_upwards [hU.mem_nhds hq] with x hx
  change (2 * Real.pi * I)⁻¹ * (∮ z in C(0,r), H (x,z)) = _
  unfold contourMoment
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have he := ((hF (x,z) ⟨hx,hz⟩).differentiableAt.hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z x).prodMk (hasDerivAt_id z))).deriv
  dsimp [H]
  rw [← he]
  rfl

end DegeneratingTrees
end

end OAI
