import OAI.Geometry.KahlerSplitting.BoxGluing

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open scoped ContDiff
open Set Metric
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open scoped Manifold ContDiff
open Set

namespace UniversalCoverSplitting

section AlternatingBilinear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def alternatingBilinear (B : E →L[ℝ] E →L[ℝ] ℝ) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  (1/2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
    (((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap).comp B)

theorem alternatingBilinear_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (v : Fin 2 → E) :
    alternatingBilinear B v = (B (v 0) (v 1) - B (v 1) (v 0)) / 2 := by
  simp [alternatingBilinear, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, Fin.removeNth, Fin.succAbove, div_eq_mul_inv]
  ring

theorem alternatingBilinear_contDiff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {B : D → E →L[ℝ] E →L[ℝ] ℝ} {U : Set D} {k : WithTop ℕ∞}
    (hB : ContDiffOn ℝ k B U) : ContDiffOn ℝ k (fun x ↦ alternatingBilinear (B x)) U := by
  exact ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).contDiff.comp_contDiffOn
    (contDiffOn_const.clm_comp hB)).const_smul (1/2 : ℝ)

end AlternatingBilinear

variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.skew_I (g : KahlerMetric X) (x : X.Carrier) (u v : Tangent X x) :
    g.metric x (Complex.I • u) v = - g.metric x (Complex.I • v) u := by
  have h := g.hermitian x u (Complex.I • v)
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at h
  rw [g.symmetric x u (Complex.I • v)] at h
  linarith

theorem KahlerMetric.skew_fundamentalInChart (g : KahlerMetric X) (c : X.Carrier)
    (z u v : Model n) : fundamentalInChart g.metric c z u v =
      -fundamentalInChart g.metric c z v u := by
  let q : Model n →L[ℂ] Tangent X ((extChartAt (model n) c).symm z) :=
    mfderiv (model n) (model n) (extChartAt (model n) c).symm z
  change g.metric _ (q (Complex.I • u)) (q v) = - g.metric _ (q (Complex.I • v)) (q u)
  rw [q.map_smul, q.map_smul]
  exact g.skew_I _ _ _

def kahlerFormInChart (g : KahlerMetric X) (c : X.Carrier) (z : Model n) :
    (Model n) [⋀^Fin 2]→L[ℝ] ℝ :=
  alternatingBilinear ((continuousMetricInChart g.metric c z).comp
    ((Complex.I • ContinuousLinearMap.id ℂ (Model n)).restrictScalars ℝ))

theorem kahlerFormInChart_apply (g : KahlerMetric X) (c : X.Carrier)
    (z : Model n) (v : Fin 2 → Model n) :
    kahlerFormInChart g c z v = fundamentalInChart g.metric c z (v 0) (v 1) := by
  rw [kahlerFormInChart, alternatingBilinear_apply]
  change (fundamentalInChart g.metric c z (v 0) (v 1) -
    fundamentalInChart g.metric c z (v 1) (v 0)) / 2 = _
  rw [g.skew_fundamentalInChart c z (v 1) (v 0)]
  ring

theorem KahlerMetric.smooth_formInChart (g : KahlerMetric X) (c : X.Carrier) :
    ContDiffOn ℝ ∞ (kahlerFormInChart g c) (extChartAt (model n) c).target := by
  have hB : ContDiffOn ℝ ∞ (continuousMetricInChart g.metric c)
      (extChartAt (model n) c).target := by
    apply contDiffOn_clm_apply.mpr
    intro u
    apply contDiffOn_clm_apply.mpr
    intro v
    exact g.smooth c u v
  exact alternatingBilinear_contDiff (hB.clm_comp contDiffOn_const)

theorem KahlerMetric.closed_formInChart (g : KahlerMetric X) (c : X.Carrier)
    {z : Model n} (hz : z ∈ (extChartAt (model n) c).target) :
    extDeriv (kahlerFormInChart g c) z = 0 := by
  have hd := (g.smooth_formInChart c).differentiableOn (by simp) z hz
  have hda := hd.differentiableAt (isOpen_extChartAt_target c |>.mem_nhds hz)
  ext v
  rw [extDeriv_apply hda]
  norm_num [kahlerFormInChart_apply, Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove]
  have hm : (fun y ↦ fundamentalInChart g.metric c y (v 0) (v 2)) =
      -(fun y ↦ fundamentalInChart g.metric c y (v 2) (v 0)) := by
    funext y
    exact g.skew_fundamentalInChart c y _ _
  rw [hm, fderiv_neg]
  simpa [add_assoc] using g.closed c z hz (v 0) (v 1) (v 2)

end UniversalCoverSplitting

open Set Filter Topology Metric Complex
open scoped Real

namespace UniversalCoverSplitting

section CauchyParameters
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in

theorem continuousOn_cauchy_partial {T S : Set (ℂ × ℂ)} {f : ℂ × ℂ → F}
    (hf : ContinuousOn f T) {r : ℝ} (hr : 0 < r)
    (hmap : ∀ z ∈ S, ∀ θ : ℝ, (circleMap z.1 r θ, z.2) ∈ T) :
    ContinuousOn (fun z : ℂ × ℂ ↦ cderiv r (fun w ↦ f (w, z.2)) z.1) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  let G : S → ℝ → F := fun z θ ↦
    (circleMap 0 r θ * I) • (((circleMap 0 r θ) ^ 2)⁻¹ •
      f (circleMap z.val.1 r θ, z.val.2))
  have hG : Continuous G.uncurry := by
    have hshift : Continuous (fun p : S × ℝ ↦
        (circleMap p.1.val.1 r p.2, p.1.val.2)) := by
      unfold circleMap
      fun_prop
    have hm : MapsTo (fun p : S × ℝ ↦
        (circleMap p.1.val.1 r p.2, p.1.val.2)) univ T :=
      fun p _ ↦ hmap p.1.val p.1.property p.2
    have hcomp := continuousOn_univ.mp (hf.comp hshift.continuousOn hm)
    have hne (p : S × ℝ) : circleMap 0 r p.2 ≠ 0 := by
      exact circleMap_ne_mem_ball (mem_ball_self hr) p.2
    dsimp [G, Function.uncurry]
    apply Continuous.smul
    · fun_prop
    · exact (((continuous_circleMap 0 r).comp continuous_snd).pow 2).inv₀
        (fun p ↦ pow_ne_zero 2 (hne p)) |>.smul hcomp
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hG (a₀ := 0) (b₀ := 2 * Real.pi)
  have hc := hi.const_smul ((2 * Real.pi * I : ℂ)⁻¹)
  change Continuous (fun z : S ↦ cderiv r (fun w ↦ f (w, z.val.2)) z.val.1)
  convert! hc using 1
  ext z
  simp only [cderiv, circleIntegral, deriv_circleMap, G, circleMap, zero_add,
    add_sub_cancel_left, Pi.smul_apply]

theorem continuousAt_partial_deriv {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ × ℂ → F} (hf : ContinuousOn f (U ×ˢ V))
    (hd : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x, y)) U)
    {p : ℂ × ℂ} (hp : p ∈ U ×ˢ V) :
    ContinuousAt (fun z : ℂ × ℂ ↦ deriv (fun w ↦ f (w, z.2)) z.1) p := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp.1)
  let S := Metric.ball p.1 (r / 2) ×ˢ V
  have hS : S ∈ 𝓝 p := prod_mem_nhds (ball_mem_nhds _ (by linarith)) (hV.mem_nhds hp.2)
  have hball (z : ℂ × ℂ) (hz : z ∈ S) : closedBall z.1 (r / 2) ⊆ U := by
    apply Subset.trans (Metric.closedBall_subset_ball' (y := p.1) ?_) hrU
    have : dist z.1 p.1 < r / 2 := hz.1
    linarith
  have hc := continuousOn_cauchy_partial (S := S) hf (by linarith : 0 < r / 2)
    (fun z hz θ ↦ ⟨hball z hz (circleMap_mem_closedBall _ (by linarith) _), hz.2⟩)
  have heq : (fun z : ℂ × ℂ ↦ cderiv (r / 2) (fun w ↦ f (w, z.2)) z.1)
      =ᶠ[𝓝 p] (fun z : ℂ × ℂ ↦ deriv (fun w ↦ f (w, z.2)) z.1) := by
    filter_upwards [hS] with z hz
    exact cderiv_eq_deriv hU (hd z.2 hz.2) (by linarith) (hball z hz)
  exact (hc.continuousAt hS).congr heq

def totalPartialDeriv (f : ℂ × ℂ → F) (p : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] F :=
  (ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) F (ContinuousLinearMap.fst ℂ ℂ ℂ))
    (deriv (fun w ↦ f (w, p.2)) p.1) +
  (ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) F (ContinuousLinearMap.snd ℂ ℂ ℂ))
    (deriv (fun w ↦ f (p.1, w)) p.2)

theorem hasStrictFDerivAt_of_continuousOn_of_separately
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ × ℂ → F} (hf : ContinuousOn f (U ×ˢ V))
    (h₁ : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x, y)) U)
    (h₂ : ∀ x ∈ U, DifferentiableOn ℂ (fun y ↦ f (x, y)) V)
    {p : ℂ × ℂ} (hp : p ∈ U ×ˢ V) :
    HasStrictFDerivAt f (totalPartialDeriv f p) p := by
  let L : F →L[ℂ] (ℂ →L[ℂ] F) := ContinuousLinearMap.smulRightL ℂ ℂ F 1
  let D₁ : ℂ → ℂ → ℂ →L[ℂ] F := fun x y ↦ L (deriv (fun w ↦ f (w, y)) x)
  let D₂ : ℂ → ℂ → ℂ →L[ℂ] F := fun x y ↦ L (deriv (fun w ↦ f (x, w)) y)
  have hd₁ : ∀ᶠ z in 𝓝 p, HasFDerivAt (fun x ↦ f (x, z.2)) (D₁ z.1 z.2) z.1 := by
    filter_upwards [(hU.prod hV).mem_nhds hp] with z hz
    exact ((h₁ z.2 hz.2).differentiableAt (hU.mem_nhds hz.1)).hasDerivAt.hasFDerivAt
  have hd₂ : ∀ᶠ z in 𝓝 p, HasFDerivAt (fun y ↦ f (z.1, y)) (D₂ z.1 z.2) z.2 := by
    filter_upwards [(hU.prod hV).mem_nhds hp] with z hz
    exact ((h₂ z.1 hz.1).differentiableAt (hV.mem_nhds hz.2)).hasDerivAt.hasFDerivAt
  have hc₁ : ContinuousAt D₁.uncurry p :=
    L.continuous.continuousAt.comp (continuousAt_partial_deriv hU hV hf h₁ hp)
  have hfs : ContinuousOn (fun z : ℂ × ℂ ↦ f z.swap) (V ×ˢ U) :=
    hf.comp continuous_swap.continuousOn (fun z hz ↦ ⟨hz.2, hz.1⟩)
  have hds : ∀ y ∈ U, DifferentiableOn ℂ (fun x ↦ f (y, x)) V := h₂
  have hcs := continuousAt_partial_deriv hV hU hfs hds (p := p.swap) ⟨hp.2, hp.1⟩
  have hc₂ : ContinuousAt D₂.uncurry p := by
    exact L.continuous.continuousAt.comp (hcs.comp continuous_swap.continuousAt)
  have hs := (hasStrictFDerivAt_uncurry_coprod (𝕜 := ℂ) (f := fun x y ↦ f (x, y))
    (f₁ := D₁) (f₂ := D₂) (u := p) hd₁ hd₂ hc₁ hc₂)
  convert! hs using 1

theorem differentiableOn_of_continuousOn_of_separately
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ × ℂ → F} (hf : ContinuousOn f (U ×ˢ V))
    (h₁ : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x, y)) U)
    (h₂ : ∀ x ∈ U, DifferentiableOn ℂ (fun y ↦ f (x, y)) V) :
    DifferentiableOn ℂ f (U ×ˢ V) := by
  intro p hp
  exact (hasStrictFDerivAt_of_continuousOn_of_separately hU hV hf h₁ h₂ hp
    ).hasFDerivAt.differentiableAt.differentiableWithinAt

theorem continuousAt_totalPartialDeriv
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ × ℂ → F} (hf : ContinuousOn f (U ×ˢ V))
    (h₁ : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x, y)) U)
    (h₂ : ∀ x ∈ U, DifferentiableOn ℂ (fun y ↦ f (x, y)) V)
    {p : ℂ × ℂ} (hp : p ∈ U ×ˢ V) :
    ContinuousAt (totalPartialDeriv f) p := by
  have hfs : ContinuousOn (fun z : ℂ × ℂ ↦ f z.swap) (V ×ˢ U) :=
    hf.comp continuous_swap.continuousOn (fun z hz ↦ ⟨hz.2, hz.1⟩)
  have hcs := continuousAt_partial_deriv hV hU hfs h₂ (p := p.swap) ⟨hp.2, hp.1⟩
  exact ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) F
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).continuous.continuousAt.comp
      (continuousAt_partial_deriv hU hV hf h₁ hp)).add
    ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) F
      (ContinuousLinearMap.snd ℂ ℂ ℂ)).continuous.continuousAt.comp
        (hcs.comp continuous_swap.continuousAt))

theorem continuousAt_fderiv_twoDim_prod
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℂ × ℂ → F} (hf : DifferentiableOn ℂ f (U ×ˢ V))
    {p : ℂ × ℂ} (hp : p ∈ U ×ˢ V) : ContinuousAt (fderiv ℂ f) p := by
  have h₁ : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x, y)) U := by
    intro y hy
    exact hf.comp (differentiableOn_id.prodMk (differentiableOn_const y))
      (fun x hx ↦ ⟨hx, hy⟩)
  have h₂ : ∀ x ∈ U, DifferentiableOn ℂ (fun y ↦ f (x, y)) V := by
    intro x hx
    exact hf.comp ((differentiableOn_const x).prodMk differentiableOn_id)
      (fun y hy ↦ ⟨hx, hy⟩)
  have he : totalPartialDeriv f =ᶠ[𝓝 p] fderiv ℂ f := by
    filter_upwards [(hU.prod hV).mem_nhds hp] with z hz
    exact (hasStrictFDerivAt_of_continuousOn_of_separately hU hV
      hf.continuousOn h₁ h₂ hz).hasFDerivAt.fderiv.symm
  exact (continuousAt_totalPartialDeriv hU hV hf.continuousOn h₁ h₂ hp).congr he

theorem continuousOn_fderiv_twoDim {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {f : ℂ × ℂ → F} (hf : DifferentiableOn ℂ f Ω) :
    ContinuousOn (fderiv ℂ f) Ω := by
  intro p hp
  obtain ⟨r, hr, hrΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hp)
  have hsub : Metric.ball p.1 r ×ˢ Metric.ball p.2 r ⊆ Ω := by
    rw [ball_prod_same]
    exact hrΩ
  exact (continuousAt_fderiv_twoDim_prod isOpen_ball isOpen_ball (hf.mono hsub)
    ⟨mem_ball_self hr, mem_ball_self hr⟩).continuousWithinAt

end CauchyParameters
end UniversalCoverSplitting

end

end OAI
