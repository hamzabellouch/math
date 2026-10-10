import OAI.Geometry.KahlerSplitting.ClosedForm

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
open Set Filter Topology Metric Complex
open scoped Real

namespace UniversalCoverSplitting
section CauchyParameters
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

open MeasureTheory

omit [CompleteSpace F] in

theorem differentiableAt_intervalIntegral_of_continuous_deriv
    {U : Set ℂ} (hU : IsOpen U) {G D : ℂ → ℝ → F}
    (hG : ContinuousOn G.uncurry (U ×ˢ univ))
    (hD : ContinuousOn D.uncurry (U ×ˢ univ))
    (hd : ∀ w ∈ U, ∀ t, HasDerivAt (fun z ↦ G z t) (D w t) w)
    {w : ℂ} (hw : w ∈ U) (a b : ℝ) :
    DifferentiableAt ℂ (fun z ↦ ∫ t in a..b, G z t) w := by
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hw)
  have hGc (z : ℂ) (hz : z ∈ U) : Continuous (G z) := by
    exact continuousOn_univ.mp (hG.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ ↦ ⟨hz,mem_univ _⟩))
  have hDc (z : ℂ) (hz : z ∈ U) : Continuous (D z) := by
    exact continuousOn_univ.mp (hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ ↦ ⟨hz,mem_univ _⟩))
  obtain ⟨C,hC⟩ := ((isCompact_closedBall w r).prod (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn
    (hD.mono (fun p hp ↦ ⟨hrU hp.1,mem_univ _⟩))
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := D) (bound := fun _ ↦ C)
    (Metric.closedBall_mem_nhds w hr)
    (by filter_upwards [hU.mem_nhds hw] with z hz
        exact (hGc z hz).aestronglyMeasurable)
    ((hGc w hw).intervalIntegrable a b)
    (hDc w hw).aestronglyMeasurable
    (by filter_upwards with t ht z hz
        exact hC (z,t) ⟨hz,uIoc_subset_uIcc ht⟩)
    (intervalIntegrable_const)
    (by filter_upwards with t _ z hz; exact hd z (hrU hz) t)).2.differentiableAt

theorem differentiableOn_weighted_curveIntegral
    {f : ℂ × ℂ → F} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f (U ×ˢ V))
    {γ K : ℝ → ℂ} (hγ : Continuous γ) (hK : Continuous K)
    (hm : ∀ t, γ t ∈ V) (a b : ℝ) :
    DifferentiableOn ℂ (fun w ↦ ∫ t in a..b, K t • f (w,γ t)) U := by
  let G : ℂ → ℝ → F := fun w t ↦ K t • f (w,γ t)
  let D : ℂ → ℝ → F := fun w t ↦ K t • deriv (fun z ↦ f (z,γ t)) w
  have hmap : MapsTo (fun p : ℂ × ℝ ↦ (p.1,γ p.2)) (U ×ˢ univ) (U ×ˢ V) :=
    fun p hp ↦ ⟨hp.1,hm p.2⟩
  have hcmap : Continuous (fun p : ℂ × ℝ ↦ (p.1,γ p.2)) :=
    continuous_fst.prodMk (hγ.comp continuous_snd)
  have hG : ContinuousOn G.uncurry (U ×ˢ univ) :=
    ((hK.comp continuous_snd).continuousOn).smul (hf.continuousOn.comp hcmap.continuousOn hmap)
  have hslice : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x,y)) U := by
    intro y hy
    exact hf.comp ((differentiable_id.prodMk (differentiable_const _)).differentiableOn)
      (fun z hz ↦ ⟨hz,hy⟩)
  have hD : ContinuousOn D.uncurry (U ×ˢ univ) := by
    apply ((hK.comp continuous_snd).continuousOn).smul
    have hpart : ContinuousOn (fun p : ℂ × ℂ ↦ deriv (fun z ↦ f (z,p.2)) p.1) (U ×ˢ V) :=
      fun p hp ↦ (continuousAt_partial_deriv hU hV hf.continuousOn hslice hp).continuousWithinAt
    exact hpart.comp hcmap.continuousOn hmap
  have hdG : ∀ w ∈ U, ∀ t, HasDerivAt (fun z ↦ G z t) (D w t) w := by
    intro w hw t
    exact ((hslice _ (hm t)).differentiableAt (hU.mem_nhds hw)).hasDerivAt.const_smul (K t)
  intro w hw
  exact (differentiableAt_intervalIntegral_of_continuous_deriv hU hG hD hdG hw a b).differentiableWithinAt

theorem differentiableOn_partial_deriv
    {f : ℂ × ℂ → F} {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hf : DifferentiableOn ℂ f (U ×ˢ V)) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ deriv (fun z ↦ f (z,p.2)) p.1) (U ×ˢ V) := by
  have hslice : ∀ y ∈ V, DifferentiableOn ℂ (fun x ↦ f (x,y)) U := by
    intro y hy
    exact hf.comp ((differentiable_id.prodMk (differentiable_const _)).differentiableOn)
      (fun z hz ↦ ⟨hz,hy⟩)
  apply differentiableOn_of_continuousOn_of_separately hU hV
    (fun p hp ↦ (continuousAt_partial_deriv hU hV hf.continuousOn hslice hp).continuousWithinAt)
  · intro y hy
    exact (hslice y hy).deriv hU
  · intro x hx
    obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
    let K : ℝ → ℂ := fun t ↦ circleMap 0 r t * I * ((circleMap x r t - x) ^ 2)⁻¹
    have hK : Continuous K := by
      apply Continuous.mul (by fun_prop)
      apply Continuous.inv₀ (by fun_prop)
      intro t
      exact pow_ne_zero 2 (sub_ne_zero.mpr (circleMap_ne_center hr.ne'))
    have hfs : DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ f p.swap) (V ×ˢ U) :=
      hf.comp ((differentiable_snd.prodMk differentiable_fst).differentiableOn)
        (fun p hp ↦ ⟨hp.2,hp.1⟩)
    have hi := differentiableOn_weighted_curveIntegral hV hU hfs
      (continuous_circleMap x r) hK (fun t ↦ hrU (circleMap_mem_closedBall _ hr.le t))
        0 (2 * Real.pi)
    have hci : DifferentiableOn ℂ (fun y ↦ cderiv r (fun z ↦ f (z,y)) x) V := by
      have heq : (fun y ↦ cderiv r (fun z ↦ f (z,y)) x) =
          fun y ↦ ((2 * Real.pi * I : ℂ)⁻¹) •
            ∫ t in (0:ℝ)..2 * Real.pi, K t • f (circleMap x r t,y) := by
        funext y
        simp only [cderiv,circleIntegral,deriv_circleMap,K,smul_smul]
      rw [heq]
      exact hi.const_smul _
    exact hci.congr (fun y hy ↦ (cderiv_eq_deriv hU (hslice y hy) hr hrU).symm)

theorem differentiableOn_partial_deriv_open
    {f : ℂ × ℂ → F} {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ deriv (fun z ↦ f (z,p.2)) p.1) Ω := by
  intro p hp
  obtain ⟨r,hr,hrs⟩ := Metric.isOpen_iff.mp hΩ p hp
  have hsub : Metric.ball p.1 r ×ˢ Metric.ball p.2 r ⊆ Ω := by
    rw [ball_prod_same]
    exact hrs
  have hd := differentiableOn_partial_deriv Metric.isOpen_ball Metric.isOpen_ball (hf.mono hsub)
  exact (hd.differentiableAt (prod_mem_nhds (Metric.ball_mem_nhds _ hr)
    (Metric.ball_mem_nhds _ hr))).differentiableWithinAt

theorem differentiableOn_fderiv_apply_open
    {f : ℂ × ℂ → F} {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) (v : ℂ × ℂ) :
    DifferentiableOn ℂ (fun p ↦ fderiv ℂ f p v) Ω := by
  have h₁ : DifferentiableOn ℂ (fun p ↦ fderiv ℂ f p (1,0)) Ω := by
    apply (differentiableOn_partial_deriv_open hΩ hf).congr
    intro p hp
    exact ((hf.differentiableAt (hΩ.mem_nhds hp)).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv.symm
  have hs : DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ f p.swap) (Prod.swap ⁻¹' Ω) :=
    hf.comp ((differentiable_snd.prodMk differentiable_fst).differentiableOn)
      (mapsTo_preimage _ _)
  have h₂ : DifferentiableOn ℂ (fun p ↦ fderiv ℂ f p (0,1)) Ω := by
    have h := (differentiableOn_partial_deriv_open
      (hΩ.preimage continuous_swap) hs).comp
      ((differentiable_snd.prodMk differentiable_fst).differentiableOn)
      (fun p hp ↦ by simpa using hp)
    apply h.congr
    intro p hp
    exact ((hf.differentiableAt (hΩ.mem_nhds hp)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))).deriv.symm
  apply ((h₁.const_smul v.1).add (h₂.const_smul v.2)).congr
  intro p hp
  change fderiv ℂ f p v = v.1 • fderiv ℂ f p (1,0) + v.2 • fderiv ℂ f p (0,1)
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

end CauchyParameters
end UniversalCoverSplitting

open scoped ContDiff
open Set
namespace UniversalCoverSplitting
section TwoDimSmooth
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem holomorphic_twoDim_contDiffOn_nat {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) (k : ℕ)
    {f : ℂ × ℂ → F} (hf : DifferentiableOn ℂ f Ω) : ContDiffOn ℂ k f Ω := by
  induction k generalizing f with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_apply hΩ.uniqueDiffOn]
    refine ⟨hf, by simp, fun v ↦ ?_⟩
    apply (ih (differentiableOn_fderiv_apply_open hΩ hf v)).congr
    intro z hz
    rw [fderivWithin_of_isOpen hΩ hz]

theorem holomorphic_twoDim_contDiffOn {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {f : ℂ × ℂ → F} (hf : DifferentiableOn ℂ f Ω) : ContDiffOn ℂ ∞ f Ω :=
  contDiffOn_infty.mpr (fun k ↦ holomorphic_twoDim_contDiffOn_nat hΩ k hf)

end TwoDimSmooth
end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set Filter Topology
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

def pullbackMetric (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier) (z : ℂ × ℂ) :
    (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) →L[ℝ] ℝ :=
  let D := (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z).restrictScalars ℝ
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp
    ((g.metric (f z)).compl₁₂ D.toLinearMap D.toLinearMap))

def pullbackKahler (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier) (z : ℂ × ℂ) :
    (ℂ × ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  alternatingBilinear ((pullbackMetric g f z).comp
    ((Complex.I • ContinuousLinearMap.id ℂ (ℂ × ℂ)).restrictScalars ℝ))

theorem pullbackKahler_apply (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    (z : ℂ × ℂ) (v : Fin 2 → ℂ × ℂ) :
    pullbackKahler g f z v = g.metric (f z)
      (Complex.I • mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (v 0))
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z (v 1)) := by
  rw [pullbackKahler, alternatingBilinear_apply]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f z) := mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z
  change (g.metric (f z) (D (Complex.I • v 0)) (D (v 1)) -
    g.metric (f z) (D (Complex.I • v 1)) (D (v 0))) / 2 = _
  rw [D.map_smul, D.map_smul, g.skew_I (f z) (D (v 1)) (D (v 0))]
  dsimp only [D]
  ring_nf
  rfl

theorem chart_derivative_twoDim {f : ℂ × ℂ → X.Carrier} {z : ℂ × ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) :
    fderiv ℂ ((extChartAt (model n) c) ∘ f) z =
      (mfderiv (model n) (model n) (extChartAt (model n) c) (f z)).comp
        (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z) := by
  have he : MDifferentiableAt (model n) (model n) (extChartAt (model n) c) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hc)
  rw [← mfderiv_eq_fderiv, mfderiv_comp z he hf]

theorem pullbackKahler_eq_chart (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {z : ℂ × ℂ} (hf : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) :
    pullbackKahler g f z =
      (kahlerFormInChart g c ((extChartAt (model n) c) (f z))).compContinuousLinearMap
        (fderiv ℝ ((extChartAt (model n) c) ∘ f) z) := by
  have he : MDifferentiableAt (model n) (model n) (extChartAt (model n) c) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hc)
  have hd := (he.comp z hf).differentiableAt
  rw [hd.fderiv_restrictScalars ℝ, chart_derivative_twoDim hf c hc]
  ext v
  simp only [pullbackKahler_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    kahlerFormInChart_apply, Function.comp_apply]
  unfold fundamentalInChart
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f z) := mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z
  let Q : Tangent X (f z) →L[ℂ] Model n :=
    mfderiv (model n) (model n) (extChartAt (model n) c) (f z)
  change g.metric (f z) (Complex.I • D (v 0)) (D (v 1)) =
    metricInChart g.metric c ((extChartAt (model n) c) (f z))
      (Complex.I • Q (D (v 0))) (Q (D (v 1)))
  rw [← Q.map_smul]
  exact (metricInChart_forward g.metric c hc _ _).symm

theorem pullbackKahler_closed (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    {z : ℂ × ℂ} (hz : z ∈ U) : extDeriv (pullbackKahler g f) z = 0 := by
  let c := f z
  let e := extChartAt (model n) c
  have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz)).continuousAt
  have hN : U ∩ f ⁻¹' e.source ∈ 𝓝 z := inter_mem (hU.mem_nhds hz)
    (hcf (extChartAt_source_mem_nhds (I := model n) c))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hN
  have hd : DifferentiableOn ℂ (e ∘ f) (Metric.ball z r) := by
    intro w hw
    have he : MDifferentiableAt (model n) (model n) e (f w) :=
      mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source, mem_preimage] using (hrs hw).2)
    exact (he.comp w (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1))).differentiableAt.differentiableWithinAt
  have hs : ContDiffAt ℝ ∞ (e ∘ f) z :=
    ((holomorphic_twoDim_contDiffOn isOpen_ball hd).restrict_scalars ℝ).contDiffAt
      (Metric.ball_mem_nhds z hr)
  have hchart : e (f z) ∈ e.target := e.map_source (hrs (Metric.mem_ball_self hr)).2
  have hω : DifferentiableAt ℝ (kahlerFormInChart g c) (e (f z)) :=
    ((g.smooth_formInChart c).differentiableOn (by simp)).differentiableAt
      ((isOpen_extChartAt_target c).mem_nhds hchart)
  have heq : pullbackKahler g f =ᶠ[𝓝 z]
      (fun w ↦ (kahlerFormInChart g c (e (f w))).compContinuousLinearMap
        (fderiv ℝ (e ∘ f) w)) := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    exact pullbackKahler_eq_chart g (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1)) c (hrs hw).2
  have hdeq : extDeriv (pullbackKahler g f) z =
      extDeriv (fun w ↦ (kahlerFormInChart g c (e (f w))).compContinuousLinearMap
        (fderiv ℝ (e ∘ f) w)) z := by
    unfold extDeriv
    rw [heq.fderiv_eq]
  rw [hdeq]
  have hr2 : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    simp
  have hp := extDeriv_pullback (f := e ∘ f) hω hs hr2
  have hc0 : extDeriv (kahlerFormInChart g c) ((e ∘ f) z) = 0 :=
    g.closed_formInChart c hchart
  rw [hc0] at hp
  exact hp.trans (by ext v; rfl)

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set Filter Topology
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.contDiff_metricInChart (g : KahlerMetric X) (c : X.Carrier) :
    ContDiffOn ℝ ∞ (continuousMetricInChart g.metric c) (extChartAt (model n) c).target := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  exact g.smooth c u v

theorem exists_smooth_chart_twoDim {f : ℂ × ℂ → X.Carrier}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    {z : ℂ × ℂ} (hz : z ∈ U) :
    ∃ (c : X.Carrier) (r : ℝ), 0 < r ∧
      Metric.ball z r ⊆ U ∩ f ⁻¹' (extChartAt (model n) c).source ∧
      ContDiffOn ℝ ∞ ((extChartAt (model n) c) ∘ f) (Metric.ball z r) := by
  let c := f z
  let e := extChartAt (model n) c
  have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz)).continuousAt
  have hN : U ∩ f ⁻¹' e.source ∈ 𝓝 z := inter_mem (hU.mem_nhds hz)
    (hcf (extChartAt_source_mem_nhds (I := model n) c))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hN
  refine ⟨c,r,hr,hrs,?_⟩
  have hd : DifferentiableOn ℂ (e ∘ f) (Metric.ball z r) := by
    intro w hw
    have he : MDifferentiableAt (model n) (model n) e (f w) :=
      mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source, mem_preimage] using (hrs hw).2)
    exact (he.comp w (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1))).differentiableAt.differentiableWithinAt
  exact (holomorphic_twoDim_contDiffOn isOpen_ball hd).restrict_scalars ℝ

theorem pullbackMetric_apply_eq_chart (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {z : ℂ × ℂ} (hf : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) (u v : ℂ × ℂ) :
    pullbackMetric g f z u v = metricInChart g.metric c ((extChartAt (model n) c) (f z))
      (fderiv ℝ ((extChartAt (model n) c) ∘ f) z u)
      (fderiv ℝ ((extChartAt (model n) c) ∘ f) z v) := by
  have he : MDifferentiableAt (model n) (model n) (extChartAt (model n) c) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hc)
  have hd := (he.comp z hf).differentiableAt
  rw [hd.fderiv_restrictScalars ℝ, chart_derivative_twoDim hf c hc]
  exact (metricInChart_forward g.metric c hc _ _).symm

theorem pullbackMetric_smooth (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U) :
    ContDiffOn ℝ ∞ (pullbackMetric g f) U := by
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v z hz
  obtain ⟨c,r,hr,hrs,hs⟩ := exists_smooth_chart_twoDim hU hf hz
  let e := extChartAt (model n) c
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (e ∘ f)) (Metric.ball z r) :=
    hs.fderiv_of_isOpen isOpen_ball (by simp)
  have hB : ContDiffOn ℝ ∞ (fun w ↦ continuousMetricInChart g.metric c (e (f w)))
      (Metric.ball z r) := (g.contDiff_metricInChart c).comp hs
        (fun w hw ↦ e.map_source (hrs hw).2)
  have hS := (hB.clm_apply (hD.clm_apply (contDiffOn_const (c := u)))).clm_apply
    (hD.clm_apply (contDiffOn_const (c := v)))
  have hC : ContDiffOn ℝ ∞ (fun w ↦ pullbackMetric g f w u v) (Metric.ball z r) := by
    apply hS.congr
    intro w hw
    exact pullbackMetric_apply_eq_chart g (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1)) c (hrs hw).2 u v
  exact (hC.contDiffAt (Metric.ball_mem_nhds z hr)).contDiffWithinAt

theorem pullbackKahler_smooth (g : KahlerMetric X) {f : ℂ × ℂ → X.Carrier}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U) :
    ContDiffOn ℝ ∞ (pullbackKahler g f) U := by
  exact alternatingBilinear_contDiff ((pullbackMetric_smooth g hU hf).clm_comp contDiffOn_const)

end UniversalCoverSplitting

open scoped Manifold ContDiff
open Set Filter Topology
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

section RealPullback
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realPullbackKahler (g : KahlerMetric X) (f : ℂ × ℂ → X.Carrier)
    (H : E → ℂ × ℂ) (x : E) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  (pullbackKahler g f (H x)).compContinuousLinearMap (fderiv ℝ H x)

theorem realPullbackKahler_as_bilinear (g : KahlerMetric X)
    (f : ℂ × ℂ → X.Carrier) (H : E → ℂ × ℂ) (x : E) :
    realPullbackKahler g f H x = alternatingBilinear
      (((pullbackMetric g f (H x)).comp
        ((Complex.I • ContinuousLinearMap.id ℂ (ℂ × ℂ)).restrictScalars ℝ)).bilinearComp
        (fderiv ℝ H x) (fderiv ℝ H x)) := by
  ext v
  simp only [realPullbackKahler, pullbackKahler,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, alternatingBilinear_apply,
    ContinuousLinearMap.bilinearComp_apply, Function.comp_apply]

theorem realPullbackKahler_smooth [FiniteDimensional ℝ E] (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {H : E → ℂ × ℂ}
    {U : Set (ℂ × ℂ)} {V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hH : ContDiffOn ℝ ∞ H V) (hmap : MapsTo H V U) :
    ContDiffOn ℝ ∞ (realPullbackKahler g f H) V := by
  change ContDiffOn ℝ ∞ (fun x ↦ realPullbackKahler g f H x) V
  simp_rw [realPullbackKahler_as_bilinear]
  apply alternatingBilinear_contDiff
  apply contDiffOn_clm_apply.mpr
  intro u
  apply contDiffOn_clm_apply.mpr
  intro v
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ H) V := hH.fderiv_of_isOpen hV (by simp)
  have hB := ((pullbackMetric_smooth g hU hf).comp hH hmap).clm_comp
    (contDiffOn_const (c := (Complex.I • ContinuousLinearMap.id ℂ (ℂ × ℂ)).restrictScalars ℝ))
  exact (hB.clm_apply (hD.clm_apply (contDiffOn_const (c := u)))).clm_apply
    (hD.clm_apply (contDiffOn_const (c := v)))

theorem realPullbackKahler_closed (g : KahlerMetric X)
    {f : ℂ × ℂ → X.Carrier} {H : E → ℂ × ℂ}
    {U : Set (ℂ × ℂ)} {V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) (model n) f U)
    (hH : ContDiffOn ℝ ∞ H V) (hmap : MapsTo H V U) {x : E} (hx : x ∈ V) :
    extDeriv (realPullbackKahler g f H) x = 0 := by
  have hd : DifferentiableAt ℝ (pullbackKahler g f) (H x) :=
    ((pullbackKahler_smooth g hU hf).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (hmap hx))
  have hr2 : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    simp
  have hp := extDeriv_pullback (f := H) hd (hH.contDiffAt (hV.mem_nhds hx)) hr2
  rw [pullbackKahler_closed g hU hf (hmap hx)] at hp
  exact hp.trans (by ext v; rfl)

theorem realPullbackKahler_apply (g : KahlerMetric X)
    (f : ℂ × ℂ → X.Carrier) (H : E → ℂ × ℂ) (x : E) (v : Fin 2 → E) :
    realPullbackKahler g f H x v = g.metric (f (H x))
      (Complex.I • mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (H x) (fderiv ℝ H x (v 0)))
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f (H x) (fderiv ℝ H x (v 1))) := by
  exact pullbackKahler_apply g f (H x) _

end RealPullback
end UniversalCoverSplitting

namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.moving_flux_nonpos (g : KahlerMetric X) (x : X.Carrier)
    (u v : Tangent X x) (R d C : ℝ) (hR : 0 ≤ R) (hd : d ≤ -C)
    (hu : metricNorm g x u ≤ C * metricNorm g x v) :
    g.metric x (Complex.I • (u + d • v)) (R • (Complex.I • v)) ≤ 0 := by
  have hq : metricNorm g x v ^ 2 = g.metric x v v :=
    Real.sq_sqrt (g.nonnegative x v)
  have hq0 : 0 ≤ metricNorm g x v := Real.sqrt_nonneg _
  have huv : g.metric x u v ≤ C * g.metric x v v := by
    calc
      _ ≤ |g.metric x u v| := le_abs_self _
      _ ≤ metricNorm g x u * metricNorm g x v := metric_abs_le g x u v
      _ ≤ (C * metricNorm g x v) * metricNorm g x v := mul_le_mul_of_nonneg_right hu hq0
      _ = C * g.metric x v v := by rw [← hq]; ring
  have hin : g.metric x u v + d * g.metric x v v ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right hd (g.nonnegative x v)
    nlinarith
  have heq : g.metric x (Complex.I • (u + d • v)) (R • (Complex.I • v)) =
      R * (g.metric x u v + d * g.metric x v v) := by
    rw [smul_add, smul_comm Complex.I d]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [g.hermitian x u v, g.hermitian x v v]
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos hR hin

theorem KahlerMetric.radial_angular_density (g : KahlerMetric X) (x : X.Carrier)
    (v : Tangent X x) (R r : ℝ) :
    g.metric x (Complex.I • (R • v)) ((R*r) • (Complex.I • v)) =
      r * R^2 * g.metric x v v := by
  rw [smul_comm Complex.I R]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [g.hermitian x v v]
  ring

end UniversalCoverSplitting

end

end OAI
