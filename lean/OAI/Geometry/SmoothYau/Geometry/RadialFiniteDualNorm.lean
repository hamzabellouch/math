import Mathlib
import OAI.Geometry.SmoothYau.Geometry.FinitePrepDualNorm
import OAI.Geometry.SmoothYau.Limits.RadialMetricDualNorm

namespace OAI

namespace YauCounterexamples
noncomputable section
section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance radialShiftMetricDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance radialShiftMetricDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance radialShiftMetricFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance radialShiftMetricFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

theorem actual_metric_radial_patch_shift (hdim : Module.finrank ℝ E = 3)
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
    ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane, let v := radialCorrugation ψ χ (fun t => y t+d) β b δ A N
      ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-ψ x) ∧
      tsupport (fun x => v x-ψ x) ⊆ tsupport χ ∧
      (∀ x, |v x-ψ x| < ε₀) ∧
      ∀ x ∈ K₀, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
        (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x ∧
        (χ x = 1 → c ≤ periodicRadialSpeed β R ((N:ℝ) • (y x+d)) →
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
  have hs := actual_radialCorrugation_strict_shift K₀ hK₀ hd j J hJ.le (fun x => hj x x.property)
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
  have hg := actual_radialCorrugation_gain_shift K₀ hK₀ hd j J hJ.le (fun x => hj x x.property)
    hψ hχ hy hβ hβ0 hr hrR hR hb hz α δ A c ε hα hδ.le hc hε hε1
    (fun x => by rw [hgr]; exact hαa x x.property)
    (fun x => by rw [hgr]; exact haA x x.property) hf hU hL
  have h₀ := radialCorrugation_uniform_C0_shift (ψ:=ψ) (y:=y) hχv hβ hr hrR hR hb hz δ A hε₀
  filter_upwards [hs,hg,h₀] with N hs hg h₀ d
  let v := radialCorrugation ψ χ (fun t => y t+d) β b δ A N
  have hsup := radialCorrugation_support (ψ:=ψ) (χ:=χ) (y:=fun t => y t+d) (β:=β) b δ A (N:ℝ)
  refine ⟨radialCorrugation_smooth hψ hχ (hy.add contDiff_const) hβ hr hrR hR hb hz δ A N,?_,hsup,h₀ d,?_⟩
  · exact hχs.of_isClosed_subset isClosed_closure hsup
  · intro x hx
    let x₀ : K₀ := ⟨x,hx⟩
    have hss := hs d x₀
    have hgg := hg d x₀
    rw [pulledGradient_metric] at hss hgg
    rw [pulledGradient_metric] at hgg
    refine ⟨?_,(actualProfileStrict_iff_tangent g v x).mpr hss.1,?_,?_⟩
    · rw [coordinateMetricGradient_eq]
      exact fun hh => hss.2 ((NormedSpace.fromTangentSpace (𝕜:=ℝ) x).injective (hh.trans (map_zero _).symm))
    · simpa only [actualProfileSpeed_eq] using hgg.2.1
    · simpa only [actualProfileSpeed_eq] using hgg.2.2
end


section
open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance radialCoframeDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance radialCoframeDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance radialCoframeFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance radialCoframeFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance
theorem exists_transverse_two_coframe (hd : Module.finrank ℝ E = 3)
    {a : E} (ha : a ≠ 0) :
    ∃ D : E →L[ℝ] (ℝ × ℝ), D a = 0 ∧
      (∀ v, Real.sqrt ((D v).1^2+(D v).2^2) ≤ ‖v‖) ∧
      ∀ v, inner ℝ a v = 0 → Real.sqrt ((D v).1^2+(D v).2^2) = ‖v‖ := by
  let : Fact (Module.finrank ℝ E = 2+1) := ⟨hd⟩
  let K := (ℝ ∙ a)ᗮ
  let b : OrthonormalBasis (Fin 2) ℝ K := OrthonormalBasis.fromOrthogonalSpanSingleton 2 ha
  let D : E →L[ℝ] (ℝ × ℝ) :=
    (InnerProductSpace.toDual ℝ E (b 0 : E)).prod (InnerProductSpace.toDual ℝ E (b 1 : E))
  have hD (v : E) : (D v).1^2+(D v).2^2 = ‖K.orthogonalProjectionOnto v‖^2 := by
    have hh := b.sum_sq_inner_right (K.orthogonalProjectionOnto v)
    simpa only [Fin.sum_univ_two,
      K.inner_orthogonalProjectionOnto_eq_of_mem_left, D,
      ContinuousLinearMap.prod_apply,InnerProductSpace.toDual_apply_apply] using hh
  have hDa : D a = 0 := by
    ext
    · change inner ℝ (b 0 : E) a = 0
      rw [real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 0).property
    · change inner ℝ (b 1 : E) a = 0
      rw [real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b 1).property
  refine ⟨D,hDa,?_,?_⟩
  · intro v
    rw [hD,Real.sqrt_sq (norm_nonneg _)]
    exact K.norm_orthogonalProjectionOnto_apply_le v
  · intro v hv
    rw [hD,Real.sqrt_sq (norm_nonneg _)]
    exact K.norm_orthogonalProjectionOnto_apply
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv)

theorem exists_metric_two_coframe (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) (ψ : E → ℝ) {p : E}
    (ha : coordinateMetricGradient g ψ p ≠ 0) :
    ∃ D : E →L[ℝ] (ℝ × ℝ), D (coordinateMetricGradient g ψ p) = 0 ∧
      (∀ v, twoCoframeForm D v v ≤ selfMetricFlat g p v v) ∧
      ∀ v, fderiv ℝ ψ p v = 0 → twoCoframeForm D v v = selfMetricFlat g p v v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : E → Type _) := ⟨g.toRiemannianMetric⟩
  let j := NormedSpace.fromTangentSpace (𝕜:=ℝ) p
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) p) := Module.Finite.equiv j.symm.toLinearEquiv
  have hg : metricGradient g ψ p ≠ 0 := by
    intro hh
    apply ha
    rw [coordinateMetricGradient_eq,hh,map_zero]
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ,E) p) = 3 :=
    (j.toLinearEquiv.finrank_eq).trans hd
  obtain ⟨D,hDa,hDu,hDe⟩ := exists_transverse_two_coframe hdim hg
  let D₀ := D.comp j.symm.toContinuousLinearMap
  have hnorm (v : E) : selfMetricFlat g p v v = ‖j.symm v‖^2 := by
    have hn := real_inner_self_eq_norm_sq (j.symm v : TangentSpace 𝓘(ℝ,E) p)
    change g.inner p (j.symm v) (j.symm v) = ‖j.symm v‖^2 at hn
    simpa only [j,selfMetricFlat,ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe,NormedSpace.fromTangentSpace] using hn
  have hsq (v : E) : (Real.sqrt ((D (j.symm v)).1^2+(D (j.symm v)).2^2))^2 =
      twoCoframeForm D₀ v v := by
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),twoCoframeForm_apply]
    rfl
  refine ⟨D₀,?_,?_,?_⟩
  · rw [coordinateMetricGradient_eq]
    simpa only [D₀,j,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hDa
  · intro v
    rw [hnorm,←hsq]
    exact sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _) |>.mpr (hDu _)
  · intro v hv
    have hor : inner ℝ (metricGradient g ψ p) (j.symm v) = 0 := by
      change g.inner p (metricGradient g ψ p) (j.symm v) = 0
      rw [metricGradient_pairing,mfderiv_eq_fderiv]
      exact hv
    rw [hnorm,←hsq,hDe _ hor]

theorem exists_local_metric_coframe (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {p : E}
    (ha : coordinateMetricGradient g ψ p ≠ 0) :
    ∃ (W : Set E) (y : E → ℝ × ℝ), IsOpen W ∧ p ∈ W ∧ ContDiff ℝ ∞ y ∧
      ∀ x ∈ W, fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 ∧
        (∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v) ∧
        ∀ v, fderiv ℝ ψ x v = 0 → selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v := by
  obtain ⟨D,hDa,hDu,hDe⟩ := exists_metric_two_coframe hd g ψ ha
  obtain ⟨O,σ,hOo,hOp,hσ,hσp,hσd,hrect⟩ :=
    smooth_flowbox (contDiff_coordinateMetricGradient g hψ) ha
  obtain ⟨σ',hσ',he⟩ := smooth_extension_near_compact isCompact_singleton hOo
    (singleton_subset_iff.mpr hOp) hσ
  have he' : σ =ᶠ[𝓝 p] σ' := by simpa only [nhdsSet_singleton] using he
  let y := D ∘ σ'
  have hy : ContDiff ℝ ∞ y := D.contDiff.comp hσ'
  have hyd (x : E) : fderiv ℝ y x = D.comp (fderiv ℝ σ' x) := by
    exact (D.hasFDerivAt.comp x (hσ'.differentiable (by simp) x).hasFDerivAt).fderiv
  have hydp : fderiv ℝ y p = D := by
    rw [hyd,←he'.fderiv_eq (𝕜:=ℝ),hσd,ContinuousLinearMap.comp_id]
  have hf : ∀ᶠ x in 𝓝 p, fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 := by
    filter_upwards [he'.fderiv (𝕜:=ℝ),hOo.mem_nhds hOp] with x hx hxO
    rw [hyd,←hx,ContinuousLinearMap.comp_apply,hrect x hxO,hDa]
  let q : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ ψ x)
  have hq : Continuous q := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hψ.continuous_fderiv (by simp))
  have hqv (x v : E) : inner ℝ (q x) v = fderiv ℝ ψ x v := InnerProductSpace.toDual_symm_apply
  have hb := twoCoframe_bounds_eventually (selfMetricFlat g) q (fderiv ℝ y)
    (contDiff_selfMetricFlat g).continuous.continuousAt hq.continuousAt
    (hy.continuous_fderiv (by simp)).continuousAt
    (fun v hv => selfMetricFlat_pos g p hv)
    (fun v => by rw [hydp]; exact hDu v)
    (fun v hv => by rw [hydp]; exact hDe v ((hqv p v).symm.trans hv))
  obtain ⟨W,hW,hWo,hWp⟩ := _root_.mem_nhds_iff.mp (hf.and hb)
  refine ⟨W,y,hWo,hWp,hy,?_⟩
  intro x hx
  obtain ⟨hf,hb₁,hb₂⟩ := hW hx
  exact ⟨hf,hb₁,fun v hv => hb₂ v ((hqv x v).trans hv)⟩

end


section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff
abbrev ProfileTorus := UnitAddCircle × UnitAddCircle

def profileTorusQuotient (z : ProfilePlane) : ProfileTorus := (z.1,z.2)
def profileTorusLift (τ : ProfileTorus) : ProfilePlane := ((AddCircle.equivIco (1:ℝ) 0 τ.1 : ℝ),(AddCircle.equivIco (1:ℝ) 0 τ.2 : ℝ))

lemma profileTorusQuotient_lift (τ : ProfileTorus) :
    profileTorusQuotient (profileTorusLift τ) = τ := by
  simp [profileTorusQuotient,profileTorusLift]

lemma circle_ball_round {s q ρ : ℝ} (h : (s : UnitAddCircle) ∈ ball (q : UnitAddCircle) ρ) :
    |s-q-(round (s-q) : ℝ)| < ρ := by
  simpa only [mem_ball,dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq,
    inv_one,one_mul,mul_one] using h

lemma profileTorus_ball_lift {q z : ProfilePlane} {ρ : ℝ}
    (hz : profileTorusQuotient z ∈
      (ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ)) :
    ∃ k : ProfileLattice, dist (z-profileLatticePoint k) q < ρ := by
  refine ⟨(round (z.1-q.1),round (z.2-q.2)),?_⟩
  have h₁ := circle_ball_round hz.1
  have h₂ := circle_ball_round hz.2
  simp only [dist_eq_norm,Prod.norm_def,Real.norm_eq_abs,Prod.fst_sub,Prod.snd_sub,
    profileLatticePoint, max_lt_iff]
  constructor
  · convert h₁ using 1
    congr 1
    ring
  · convert h₂ using 1
    congr 1
    ring

theorem exists_radial_phase_window {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    {a b R : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b < R^2) (hR : 0 < R)
    (hsmall : 2*R < 1) (hmid : β ((a+b)/2) = 1) :
    ∃ (q : ProfilePlane) (ρ c : ℝ), 0 < ρ ∧ ρ ≤ 1/4 ∧ 0 < c ∧
      ∀ z, profileTorusQuotient z ∈
        (ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ) →
        c ≤ periodicRadialSpeed β R z := by
  let s := Real.sqrt ((a+b)/2)
  have ht : 0 < (a+b)/2 := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  have hs2 : s^2 = (a+b)/2 := Real.sq_sqrt ht.le
  have hsR : s < R := by nlinarith
  let q : ProfilePlane := (s,0)
  have hqn : ‖q‖ = s := by simp [q,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hs,hs.le]
  let f : ProfilePlane → ℝ := fun z => 2*Real.sqrt (z.1^2+z.2^2)*β (z.1^2+z.2^2)
  have hf : Continuous f := (continuous_const.mul
    (Real.continuous_sqrt.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2)))).mul
    (hβ.continuous.comp ((continuous_fst.pow 2).add (continuous_snd.pow 2)))
  have hq : s < f q := by
    dsimp [f,q]
    rw [zero_pow (by norm_num : 2 ≠ 0),add_zero,hs2,hmid,mul_one]
    change s < 2*s
    linarith
  obtain ⟨η,hη,hηsub⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hf) q hq
  let ρ := min η (min ((R-s)/2) (1/4))
  have hρ : 0 < ρ := lt_min hη (lt_min (by linarith) (by norm_num))
  refine ⟨q,ρ,s,hρ,(min_le_right _ _).trans (min_le_right _ _),hs,?_⟩
  intro z hz
  obtain ⟨k,hk⟩ := profileTorus_ball_lift hz
  have hnk : ‖z-profileLatticePoint k‖ < R := by
    have htri := norm_le_norm_add_norm_sub' (z-profileLatticePoint k) q
    have hks : ‖z-profileLatticePoint k-q‖ < ρ := by simpa [dist_eq_norm] using hk
    have hr : ρ ≤ (R-s)/2 := (min_le_right _ _).trans (min_le_left _ _)
    rw [hqn] at htri
    linarith
  have hh : s < f (z-profileLatticePoint k) := hηsub (hk.trans_le (min_le_left _ _))
  rw [periodicRadialSpeed,periodicRadialOffset_eq hsmall k hnk]
  exact hh.le

end


section
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal

lemma profileTorusQuotient_add (z w : ProfilePlane) :
    profileTorusQuotient (z+w) = profileTorusQuotient z+profileTorusQuotient w := rfl

lemma continuous_profileTorusQuotient : Continuous profileTorusQuotient :=
  ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd)

lemma radial_phase_fraction (q : ProfilePlane) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1/4) :
    ((volume : Measure UnitAddCircle).prod volume)
      (ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ) =
      ENNReal.ofReal ((2*ρ)^2) := by
  rw [Measure.prod_prod]
  have hb (x : UnitAddCircle) : volume (ball x ρ) = ENNReal.ofReal (2*ρ) := by
    rw [←measure_congr (AddCircle.closedBall_ae_eq_ball (x:=x) (ε:=ρ)),
      AddCircle.volume_closedBall,min_eq_right (by linarith : 2*ρ ≤ 1)]
  rw [hb,hb,pow_two]
  exact (ENNReal.ofReal_mul (show 0 ≤ 2*ρ by positivity)).symm

theorem exists_radial_phase {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (y : X → ProfilePlane) (hy : Measurable y)
    (N : ℝ) (q : ProfilePlane) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1/4) :
    ∃ τ : ProfilePlane, μ univ * ENNReal.ofReal ((2*ρ)^2) ≤
      μ {x | profileTorusQuotient (N • y x+τ) ∈
        ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ} := by
  let ν : Measure ProfileTorus := (volume : Measure UnitAddCircle).prod volume
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  have ha : Measurable (fun x => profileTorusQuotient (N • y x)) :=
    continuous_profileTorusQuotient.measurable.comp (hy.const_smul N)
  obtain ⟨τ,hτ⟩ := exists_periodic_phase_mass μ ν
    (fun x => profileTorusQuotient (N • y x)) ha
    (E:=ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ)
    (measurableSet_ball.prod measurableSet_ball)
  refine ⟨profileTorusLift τ,?_⟩
  simp_rw [profileTorusQuotient_add,profileTorusQuotient_lift]
  rw [show ν (ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ) =
    ENNReal.ofReal ((2*ρ)^2) from radial_phase_fraction q hρ hρ1] at hτ
  exact hτ

end


open Set Function Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ENNReal InnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance radialFiniteDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance radialFiniteDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance radialFiniteFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance radialFiniteFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

omit [MeasurableSpace E] [BorelSpace E] in
lemma actualProfileSpeed_eventuallyEq (g : SmoothMetric E E) {u v : E → ℝ} {x : E}
    (h : u =ᶠ[𝓝 x] v) : actualProfileSpeed g u x = actualProfileSpeed g v x := by
  rw [actualProfileSpeed,actualProfileSpeed,(actualJet_eventuallyEq g h).1]

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_local_metric_radial_patch (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {p : E}
    (ha : coordinateMetricGradient g ψ p ≠ 0) :
    ∃ (W : Set E) (y : E → ProfilePlane) (A : ℝ), IsOpen W ∧ p ∈ W ∧
      ContDiff ℝ ∞ y ∧ 0 < A ∧ ∀ x ∈ W,
      fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 ∧
      (∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v) ∧
      (∀ v, fderiv ℝ ψ x v = 0 → selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v) ∧
      A ≤ 2*actualProfileSpeed g ψ x ∧ actualProfileSpeed g ψ x/2 ≤ A := by
  obtain ⟨O,y,hOo,hOp,hy,hdata⟩ := exists_local_metric_coframe hdim g hψ ha
  let A := actualProfileSpeed g ψ p
  have hA : 0 < A := actualCoordinateNorm_pos g p ha
  let W := O ∩ {x | A/2 < actualProfileSpeed g ψ x ∧ actualProfileSpeed g ψ x < 2*A}
  have hc := continuous_actualProfileSpeed g hψ
  have hWo : IsOpen W := hOo.inter ((isOpen_lt continuous_const hc).inter
    (isOpen_lt hc continuous_const))
  refine ⟨W,y,A,hWo,⟨hOp,by dsimp only [A]; constructor <;> linarith⟩,hy,hA,?_⟩
  intro x hx
  obtain ⟨hf,hU,hL⟩ := hdata x hx.1
  exact ⟨hf,hU,hL,by linarith [hx.2.1],by linarith [hx.2.2]⟩

theorem actual_metric_radial_finite (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {Ω U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Ω)
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g ψ x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g ψ x)
    (hfull : ∀ x ∈ U, actualProfileFull g ψ x)
    (μ : Measure E) [IsFiniteMeasure μ]
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (hβv : ∀ t, β t ∈ Icc 0 1)
    {b r R δ c ε ε₀ : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 2*R < 1)
    (hb : b ≤ r^2) (hz : ∀ t, b ≤ t → β t = 0)
    (hδ : 0 < δ) (hc : 0 ≤ c) (hε : 0 < ε) (hε1 : ε < 1) (hε₀ : 0 < ε₀)
    (Fmax S Kb : ℝ) (hFmax : 0 < Fmax) (hS : 0 < S) (hKb : 0 < Kb)
    (hcoef : ∀ z, 0 ≤ periodicRadialSpeed β R z ∧ periodicRadialSpeed β R z ≤ Fmax ∧
      0 ≤ periodicAngularSecond β R z ∧
      (periodicRadialSpeed β R z)^2 ≤ S*periodicAngularSecond β R z ∧
      |periodicRadialSecond β R z| ≤ Kb)
    (hsmall : 9216*Kb*S*δ^2 ≤ 1)
    (q : ProfilePlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hwindow : ∀ z, profileTorusQuotient z ∈
      ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ →
        c ≤ periodicRadialSpeed β R z) :
    ∃ (v : E → ℝ) (G : Set E), ContDiff ℝ ∞ v ∧
      HasCompactSupport (fun x => v x-ψ x) ∧ tsupport (fun x => v x-ψ x) ⊆ U ∧
      (∀ x, |v x-ψ x| < ε₀) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
        (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x) ∧
      MeasurableSet G ∧ G ⊆ U ∧
      μ U/2 * ENNReal.ofReal ((2*ρ)^2) ≤ μ G ∧
      ∀ x ∈ G, (Real.sqrt (1+δ^2*c^2/16)-ε)*actualProfileSpeed g ψ x ≤
        actualProfileSpeed g v x := by
  classical
  by_cases hzero : μ U = 0
  · refine ⟨ψ,∅,hψ,?_,?_,?_,?_,MeasurableSet.empty,empty_subset _,?_,?_⟩
    · dsimp [HasCompactSupport]; simp
    · simp
    · simpa using (fun _ : E => hε₀)
    · intro x hx
      refine ⟨ha x hx,hstrict x hx,?_⟩
      have hn := actualCoordinateNorm_nonneg g x (coordinateMetricGradient g ψ x)
      change 0 ≤ actualProfileSpeed g ψ x at hn
      nlinarith
    · simp [hzero]
    · simp
  have hhalf : μ U/2 < μ U := by
    have hh := ENNReal.mul_lt_mul_left hzero (measure_ne_top μ U)
      (by norm_num : (1/2 : ℝ≥0∞) < 1)
    simpa only [one_mul,div_eq_mul_inv,one_mul,mul_comm] using hh
  have hloc : ∀ p : E, ∃ (W : Set E) (y : E → ProfilePlane) (A : ℝ), IsOpen W ∧
      (p ∈ U → p ∈ W ∧ ContDiff ℝ ∞ y ∧ 0 < A ∧ ∀ x ∈ W,
        fderiv ℝ y x (coordinateMetricGradient g ψ x) = 0 ∧
        (∀ v, twoCoframeForm (fderiv ℝ y x) v v ≤ 4*selfMetricFlat g x v v) ∧
        (∀ v, fderiv ℝ ψ x v = 0 → selfMetricFlat g x v v ≤ 4*twoCoframeForm (fderiv ℝ y x) v v) ∧
        A ≤ 2*actualProfileSpeed g ψ x ∧ actualProfileSpeed g ψ x/2 ≤ A) := by
    intro p
    by_cases hp : p ∈ U
    · obtain ⟨W,y,A,hWo,hWp,hy,hA,hd⟩ := exists_local_metric_radial_patch hdim g hψ
        (ha p (subset_closure (hUΩ hp)))
      exact ⟨W,y,A,hWo,fun _ => ⟨hWp,hy,hA,hd⟩⟩
    · exact ⟨∅,0,1,isOpen_empty,fun h => (hp h).elim⟩
  choose W y A hWo hW using hloc
  obtain ⟨t,r₀,ht,htd,htm⟩ := finite_disjoint_profile_cores μ hU W
    (fun p hp => (hWo p).mem_nhds (hW p hp).1) hhalf
  let ι := {p // p ∈ t}
  let C : ι → Set E := fun i => closedBall i.val (r₀ i.val)
  have hC : ∀ i, IsCompact (C i) := fun _ => isCompact_closedBall _ _
  have hCd : Pairwise (Disjoint on C) := by
    intro i j hij
    exact htd i.property j.property (fun he => hij (Subtype.ext he))
  obtain ⟨χ,hχ,hχd⟩ := compact_disjoint_smooth_cutoffs C (fun i => U ∩ W i.val) hC hCd
    (fun i => hU.inter (hWo i.val)) (fun i => (ht i.val i.property).2.2)
  have hχ1 : ∀ i, ∀ x ∈ C i, χ i x = 1 := fun i x hx =>
    (eventually_nhdsSet_iff_forall.mp (hχ i).2.2.2.1 x hx).self_of_nhds
  have hCχ : ∀ i, C i ⊆ tsupport (χ i) := by
    intro i x hx
    apply subset_tsupport
    simp only [Function.mem_support,hχ1 i x hx,ne_eq,one_ne_zero,not_false_eq_true]
  let w (i : ι) (N : ℕ) (d : ProfilePlane) :=
    radialCorrugation ψ (χ i) (fun x => y i.val x+d) β b δ (A i.val) N
  have hpdata : ∀ i : ι, ∀ᶠ N : ℕ in atTop, ∀ d : ProfilePlane,
      ContDiff ℝ ∞ (w i N d) ∧ HasCompactSupport (fun x => w i N d x-ψ x) ∧
      tsupport (fun x => w i N d x-ψ x) ⊆ tsupport (χ i) ∧
      (∀ x, |w i N d x-ψ x| < ε₀) ∧
      ∀ x ∈ tsupport (χ i), coordinateMetricGradient g (w i N d) x ≠ 0 ∧
        actualProfileStrict g (w i N d) x ∧
        (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g (w i N d) x ∧
        (χ i x = 1 → c ≤ periodicRadialSpeed β R ((N:ℝ) • (y i.val x+d)) →
          (Real.sqrt (1+δ^2*c^2/16)-ε)*actualProfileSpeed g ψ x ≤
            actualProfileSpeed g (w i N d) x) := by
    intro i
    have hi := hW i.val (ht i.val i.property).1
    have hreg := fun x hx => (hχ i).2.2.1 (show x ∈ tsupport (χ i) from hx)
    exact actual_metric_radial_patch_shift hdim g (hχ i).2.1 hψ (hχ i).1 hi.2.1
      (hχ i).2.1 (hχ i).2.2.2.2
      (fun x hx => ha x (subset_closure (hUΩ (hreg x hx).1)))
      (fun x hx => hfull x (hreg x hx).1)
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).1)
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).2.1)
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).2.2.1)
      hβ hβ0 hβv hr hrR hR hb hz hδ hi.2.2.1 hc hε hε1 hε₀
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).2.2.2.1)
      (fun x hx => (hi.2.2.2 x (hreg x hx).2).2.2.2.2)
      Fmax S Kb hFmax hS hKb hcoef hsmall
  obtain ⟨N,hNpos,hN⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (Filter.eventually_all.mpr hpdata)).exists
  have hNz : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
  let D : Set E := ⋃ i, C i
  have hDm : MeasurableSet D := MeasurableSet.iUnion fun i => (hC i).measurableSet
  have hDU : D ⊆ U := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ((ht i.val i.property).2.2 hi).1
  have hMD : μ U/2 ≤ μ D := by
    apply le_of_lt
    convert htm using 1
    congr 1
    ext x
    simp only [D,C,ι,mem_iUnion,Subtype.exists,exists_prop]
  let yg : E → ProfilePlane := fun x => ∑ i, (C i).indicator (y i.val) x
  have hyg : Measurable yg := Finset.measurable_sum _ (fun i _ =>
    ((hW i.val (ht i.val i.property).1).2.1.continuous.measurable).indicator (hC i).measurableSet)
  have hygi : ∀ i, ∀ x ∈ C i, yg x = y i.val x := by
    intro i x hx
    dsimp only [yg]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hx _
    · intro j _ hji
      exact indicator_of_notMem ((hCd hji).notMem_of_mem_right hx) _
    · simp
  obtain ⟨τ,hτ⟩ := exists_radial_phase (μ.restrict D) yg hyg (N:ℝ) q hρ.le hρ1
  let d : ProfilePlane := (N:ℝ)⁻¹ • τ
  have hphase (x : E) (i : ι) (hx : x ∈ C i) :
      (N:ℝ) • (y i.val x+d) = (N:ℝ) • yg x+τ := by
    rw [hygi i x hx,smul_add,show (N:ℝ) • d = τ by dsimp [d]; rw [smul_smul,mul_inv_cancel₀ hNz,one_smul]]
  let f : ι → E → ℝ := fun i x => w i N d x-ψ x
  let v : E → ℝ := fun x => ψ x+∑ i, f i x
  have hv : ContDiff ℝ ∞ v := hψ.add (ContDiff.sum (fun i _ => (hN i d).1.sub hψ))
  have hfs : ∀ i, tsupport (f i) ⊆ tsupport (χ i) := fun i => (hN i d).2.2.1
  have hfd : Pairwise (Disjoint on fun i => tsupport (f i)) := fun i j hij =>
    (hχd hij).mono (hfs i) (hfs j)
  have heq : ∀ i, ∀ x ∈ tsupport (χ i), v =ᶠ[𝓝 x] w i N d := by
    intro i x hx
    simpa only [f,add_sub_cancel] using disjoint_supported_sum_eq_patch ψ χ f hχd hfs hx
  have hcases (x : E) : (v =ᶠ[𝓝 x] ψ) ∨ ∃ i, x ∈ tsupport (χ i) ∧ v =ᶠ[𝓝 x] w i N d := by
    rcases disjoint_sum_eventuallyEq ψ f hfd x with h|⟨i,hi,hei⟩
    · exact Or.inl h
    · exact Or.inr ⟨i,hfs i hi,heq i x (hfs i hi)⟩
  have hvs : tsupport (fun x => v x-ψ x) ⊆ ⋃ i, tsupport (χ i) := by
    apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
    intro x hx
    by_contra hh
    have hz : ∀ i, f i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
      (fun hi => hh (mem_iUnion_of_mem i (hfs i hi)))
    exact hx (by simp [v,hz])
  have hcpt : HasCompactSupport (fun x => v x-ψ x) :=
    (isCompact_iUnion fun i => (hχ i).2.1).of_isClosed_subset (isClosed_tsupport _) hvs
  have hsub : tsupport (fun x => v x-ψ x) ⊆ U := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hvs hx)
    exact ((hχ i).2.2.1 hi).1
  have heps : ∀ x, |v x-ψ x| < ε₀ := by
    intro x
    rcases hcases x with hh|⟨i,hi,hei⟩
    · simpa only [hh.self_of_nhds,sub_self,abs_zero] using hε₀
    · rw [hei.self_of_nhds]
      exact (hN i d).2.2.2.1 x
  have hglobal : ∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
      (1-ε)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x := by
    intro x hx
    rcases hcases x with hh|⟨i,hi,hei⟩
    · obtain ⟨hg,hH,hS,hF⟩ := actualJet_eventuallyEq g hh
      refine ⟨hg ▸ ha x hx,hS.mpr (hstrict x hx),?_⟩
      rw [actualProfileSpeed_eventuallyEq g hh]
      have hn := actualCoordinateNorm_nonneg g x (coordinateMetricGradient g ψ x)
      change 0 ≤ actualProfileSpeed g ψ x at hn
      nlinarith
    · have hp := (hN i d).2.2.2.2 x hi
      obtain ⟨hg,hH,hS,hF⟩ := actualJet_eventuallyEq g hei
      exact ⟨hg ▸ hp.1,hS.mpr hp.2.1,(actualProfileSpeed_eventuallyEq g hei).symm ▸ hp.2.2.1⟩
  let B : Set E := {x | profileTorusQuotient ((N:ℝ) • yg x+τ) ∈
    ball (q.1 : UnitAddCircle) ρ ×ˢ ball (q.2 : UnitAddCircle) ρ}
  have hBm : MeasurableSet B := (measurableSet_ball.prod measurableSet_ball).preimage
    (continuous_profileTorusQuotient.measurable.comp ((hyg.const_smul (N:ℝ)).add_const τ))
  refine ⟨v,B ∩ D,hv,hcpt,hsub,heps,hglobal,hBm.inter hDm,inter_subset_right.trans hDU,?_,?_⟩
  · rw [Measure.restrict_apply_univ,Measure.restrict_apply hBm] at hτ
    exact (mul_le_mul_left hMD _).trans hτ
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx.2
    rw [actualProfileSpeed_eventuallyEq g (heq i x (hCχ i hi))]
    apply ((hN i d).2.2.2.2 x (hCχ i hi)).2.2.2 (hχ1 i x hi)
    rw [hphase x i hi]
    exact hwindow _ hx.1

end
end YauCounterexamples

end OAI
