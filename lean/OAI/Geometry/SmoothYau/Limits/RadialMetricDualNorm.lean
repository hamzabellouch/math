import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ActualRadialCorrugationStrictShift
import OAI.Geometry.SmoothYau.Smoothness.GlobalPrepDualNorm

namespace OAI

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance radialMetricDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance radialMetricDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance radialMetricFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance radialMetricFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

lemma pulledGradient_metric (g : SmoothMetric E E) (u : E → ℝ) (x : E) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
      Module.Finite.equiv (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm.toLinearEquiv
    pulledGradient (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).toContinuousLinearMap u x =
      metricGradient g u x := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
    Module.Finite.equiv (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).symm.toLinearEquiv
  apply (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,E) x)).injective
  ext v
  rw [InnerProductSpace.toDual_apply_apply,pulledGradient_pairing]
  change fderiv ℝ u x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x) v) = g.inner x (metricGradient g u x) v
  rw [metricGradient_pairing,mfderiv_eq_fderiv]
  rfl

lemma compact_actual_full_margin (g : SmoothMetric E E) {u : E → ℝ}
    (hu : ContDiff ℝ ∞ u) {K : Set E} (hK : IsCompact K)
    (hfull : ∀ x ∈ K, actualProfileFull g u x) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, ∀ v : TangentSpace 𝓘(ℝ,E) x,
      ‖v‖ = 1 → inner ℝ (metricGradient g u x) v = 0 →
      m ≤ profileTrace (pulledHessian (metricChristoffel g)
        (NormedSpace.fromTangentSpace (𝕜:=ℝ) x).toContinuousLinearMap u x) (metricGradient g u x) v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let q : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)
  obtain ⟨m,hm,hm1,hml⟩ := compact_variableMetric_margin hK (selfMetricFlat g)
    (actualProfileTraceForm g u) q (contDiff_selfMetricFlat g).continuous
    (continuous_actualProfileTraceForm g hu)
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp (hu.continuous_fderiv (by simp))) hfull
  refine ⟨m,hm,hm1,?_⟩
  intro x hx v hv hav
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) x
  have hB : selfMetricFlat g x (j v) (j v) = 1 := by
    rw [selfMetricFlat_metric_norm,hv,one_pow]
  have hq : inner ℝ (q x) (j v) = 0 := by
    rw [InnerProductSpace.toDual_symm_apply]
    have he := metricGradient_pairing g u x v
    rw [mfderiv_eq_fderiv] at he
    exact he.symm.trans hav
  have hh := hml x hx (j v) hB hq
  rw [actualProfileTraceForm_tangent,hv,one_pow,one_mul] at hh
  exact hh

theorem actual_metric_radial_patch (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {K₀ : Set E} (hK₀ : IsCompact K₀)
    {ψ χ : E → ℝ} {y : E → ProfilePlane}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ) (hy : ContDiff ℝ ∞ y)
    (hχs : HasCompactSupport χ) (hχv : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (ha : ∀ x ∈ K₀, coordinateMetricGradient g ψ x ≠ 0)
    (hfull : ∀ x ∈ K₀, actualProfileFull g ψ x)
    (hfirst : ∀ x ∈ K₀, fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0)
    (hup : ∀ x ∈ K₀, ∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v)
    (hlo : ∀ x ∈ K₀, ∀ v, fderiv ℝ ψ x v = 0 →
      selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (hβv : ∀ t, β t ∈ Icc 0 1)
    {b r R δ A c ε ε₀ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
    (hδ : 0 < δ) (hA : 0 < A) (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε < 1) (hε₀ : 0 < ε₀)
    (hAa : ∀ x ∈ K₀, A ≤ 2*actualProfileSpeed g ψ x)
    (haA : ∀ x ∈ K₀, actualProfileSpeed g ψ x/2 ≤ A)
    (Fmax S K : ℝ) (hFmax : 0 < Fmax) (hS : 0 < S) (hK : 0 < K)
    (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
      0 ≤ periodicAngularSecond β R z ∧
      (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
      |periodicRadialSecond β R z| ≤ K)
    (hsmall : 9216*K*S*δ^2 ≤ 1) :
    ∀ᶠ N : ℕ in atTop, let v := radialCorrugation ψ χ y β b δ A N
      ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-ψ x) ∧
      tsupport (fun x => v x-ψ x) ⊆ tsupport χ ∧
      (∀ x, |v x-ψ x| < ε₀) ∧
      ∀ x ∈ K₀, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
        (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x ∧
        (χ x = 1 → c ≤ periodicRadialSpeed β R ((N:ℝ) • y x) →
          (Real.sqrt (1+δ^2*c^2/16)-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let V : K₀ → Type _ := fun x => TangentSpace 𝓘(ℝ,E) (x:E)
  let : ∀ x : K₀, NormedAddCommGroup (V x) := fun x => inferInstanceAs (NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) (x:E)))
  let : ∀ x : K₀, InnerProductSpace ℝ (V x) := fun x => inferInstanceAs (InnerProductSpace ℝ (TangentSpace 𝓘(ℝ,E) (x:E)))
  let j : ∀ x : K₀, V x →L[ℝ] E := fun x => (NormedSpace.fromTangentSpace (𝕜:=ℝ) (x:E)).toContinuousLinearMap
  let : ∀ x : K₀, FiniteDimensional ℝ (V x) := fun x =>
    Module.Finite.equiv (NormedSpace.fromTangentSpace (𝕜:=ℝ) (x:E)).symm.toLinearEquiv
  have hd : ∀ x : K₀, 3 ≤ Module.finrank ℝ (V x) := fun x => by
    rw [(NormedSpace.fromTangentSpace (𝕜:=ℝ) (x:E)).toLinearEquiv.finrank_eq,hdim]
  obtain ⟨J,hJ,hj⟩ := compact_metric_tangent_bound g hK₀
  obtain ⟨α,hα,hαa⟩ := compact_actual_speed_pos g hψ hK₀ ha
  obtain ⟨M,hMa⟩ := hK₀.exists_bound_of_continuousOn (f:=actualProfileSpeed g ψ)
    (continuous_actualProfileSpeed g hψ).continuousOn
  obtain ⟨H,hH⟩ := hK₀.exists_bound_of_continuousOn (f:=actualCoordinateHessian g ψ)
    (continuous_coordinateCovariantSecond _ (contDiff_metricChristoffel g).continuous hψ).continuousOn
  obtain ⟨m,hm,hm1,hmargin⟩ := compact_actual_full_margin g hψ hK₀ hfull
  have hgr (x : K₀) : ‖pulledGradient (j x) ψ x‖ = actualProfileSpeed g ψ x := by
    rw [actualProfileSpeed_eq,pulledGradient_metric]
  have hhh (x : K₀) : ‖pulledHessian (metricChristoffel g) (j x) ψ x‖ ≤ |H| *J^2 := by
    exact (norm_bilinear_pullback_le _ _).trans (mul_le_mul
      ((hH x x.property).trans (le_abs_self H)) (sq_le_sq₀ (norm_nonneg _) hJ.le |>.mpr (hj x x.property))
      (sq_nonneg _) (abs_nonneg _))
  have hf (x : K₀) : fderiv ℝ y x (j x (pulledGradient (j x) ψ x)) = 0 := by
    rw [pulledGradient_metric]
    change fderiv ℝ y x ((NormedSpace.fromTangentSpace (𝕜:=ℝ) (x:E)) (metricGradient g ψ x)) = 0
    rw [←coordinateMetricGradient_eq]
    exact hfirst x x.property
  have hU (x : K₀) (v : V x) :
      Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) ≤ 2*‖v‖ := by
    have hh := hup x x.property (j x v)
    dsimp only [j, ContinuousLinearEquiv.coe_coe] at hh
    rw [selfMetricFlat_metric_norm,twoCoframeForm_apply] at hh
    change (fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2 ≤ 4*‖v‖^2 at hh
    exact (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
  have hL (x : K₀) (v : V x) (hv : inner ℝ (pulledGradient (j x) ψ x) v = 0) :
      ‖v‖/2 ≤ Real.sqrt ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) := by
    have hh := hlo x x.property (j x v) ((pulledGradient_pairing _ _ _ _).symm.trans hv)
    dsimp only [j, ContinuousLinearEquiv.coe_coe] at hh
    rw [selfMetricFlat_metric_norm,twoCoframeForm_apply] at hh
    change ‖v‖^2 ≤ 4*((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2) at hh
    have hs := Real.sq_sqrt (show 0 ≤ (fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2 by positivity)
    nlinarith [Real.sqrt_nonneg ((fderiv ℝ y x (j x v)).1^2+(fderiv ℝ y x (j x v)).2^2),norm_nonneg v]
  have hs := actual_radialCorrugation_strict K₀ hK₀ hd j J hJ.le (fun x => hj x x.property)
    (metricChristoffel g) (contDiff_metricChristoffel g).continuous hψ hχ hy hχs hχv hβ hβ0 hβv
    hr hrR hR hb hz Fmax K S hFmax.le hK.le hS.le
    (fun z => ⟨(hcoef z).1,(hcoef z).2.1,(hcoef z).2.2.2⟩)
    m α (|M|) (|H| *J^2) δ A hm hm1 hα (abs_nonneg _) (by positivity) hδ hA
    hsmall
    (fun x => by rw [hgr]; exact hαa x x.property)
    (fun x => by rw [hgr]; exact (le_abs_self _).trans ((hMa x x.property).trans (le_abs_self M))) hhh
    (fun x => by rw [hgr]; exact hAa x x.property)
    (fun x v hv hav => by rw [pulledGradient_metric] at hav ⊢; exact hmargin x x.property v hv hav)
    hf hU hL
  have hg := actual_radialCorrugation_gain K₀ hK₀ hd j J hJ.le (fun x => hj x x.property)
    hψ hχ hy hβ hβ0 hr hrR hR hb hz α δ A c ε hα hδ.le hc hε hε1
    (fun x => by rw [hgr]; exact hαa x x.property)
    (fun x => by rw [hgr]; exact haA x x.property) hf hU hL
  have h₀ := radialCorrugation_uniform_C0 (ψ:=ψ) (y:=y) hχv hβ hr hrR hR hb hz δ A hε₀
  filter_upwards [hs,hg,h₀] with N hs hg h₀
  let v := radialCorrugation ψ χ y β b δ A N
  have hsup := radialCorrugation_support (ψ:=ψ) (χ:=χ) (y:=y) (β:=β) b δ A (N:ℝ)
  refine ⟨radialCorrugation_smooth hψ hχ hy hβ hr hrR hR hb hz δ A N,?_,hsup,h₀,?_⟩
  · exact hχs.of_isClosed_subset isClosed_closure hsup
  · intro x hx
    let x₀ : K₀ := ⟨x,hx⟩
    have hss := hs x₀
    have hgg := hg x₀
    rw [pulledGradient_metric] at hss hgg
    rw [pulledGradient_metric] at hgg
    refine ⟨?_,(actualProfileStrict_iff_tangent g v x).mpr hss.1,?_,?_⟩
    · rw [coordinateMetricGradient_eq]
      exact fun hh => hss.2 ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).injective (hh.trans (map_zero _).symm))
    · simpa only [actualProfileSpeed_eq] using hgg.2.1
    · simpa only [actualProfileSpeed_eq] using hgg.2.2
end
end YauCounterexamples

end OAI
