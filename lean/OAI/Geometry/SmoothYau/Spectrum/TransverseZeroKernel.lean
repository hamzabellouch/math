import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.DirectionalCompEquiv
import OAI.Geometry.SmoothYau.Geometry.LocalizeRepresentative
import OAI.Geometry.SmoothYau.Geometry.ZeroInterior
import OAI.Geometry.SmoothYau.Smoothness.BundleRankOne
import OAI.Geometry.SmoothYau.Smoothness.ChartDerivativeNeZeroTransfer
import OAI.Geometry.SmoothYau.Smoothness.CutoffExactificationSmoothNeighborhood

namespace OAI


noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

lemma laplaceBeltrami_const (g : SmoothMetric E M) (c : ℝ) (x : M) :
    laplaceBeltrami g (fun _ => c) x = 0 := by
  simp [laplaceBeltrami, Function.comp_def]

lemma laplaceBeltrami_add {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y + v y) x =
      laplaceBeltrami g u x + laplaceBeltrami g v x := by
  have h := congrArg Complex.re (complexLaplaceBeltrami_add
    (Complex.ofRealCLM.contMDiff.comp hu) (Complex.ofRealCLM.contMDiff.comp hv) g x)
  simpa only [complexLaplaceBeltrami, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
    Function.comp_def, Complex.ofRealCLM_apply, Pi.sub_apply] using h

lemma laplaceBeltrami_sub {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 v) (g : SmoothMetric E M) (x : M) :
    laplaceBeltrami g (fun y => u y - v y) x =
      laplaceBeltrami g u x - laplaceBeltrami g v x := by
  have h := congrArg Complex.re (complexLaplaceBeltrami_sub
    (Complex.ofRealCLM.contMDiff.comp hu) (Complex.ofRealCLM.contMDiff.comp hv) g x)
  simpa only [complexLaplaceBeltrami, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
    Function.comp_def, Complex.ofRealCLM_apply, Pi.sub_apply] using h

lemma weightedLaplacian_shift {b h : M → ℝ}
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 b)
    (hh : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 h) (g : SmoothMetric E M) (x : M) :
    weightedLaplacian g b (fun y => 1 + h y) x =
      weightedLaplacian g (fun y => b y - 1) h x + laplaceBeltrami g h x := by
  rw [weightedLaplacian_product_formula (u := fun y => 1 + h y) hb (contMDiff_const.add hh),
    weightedLaplacian_product_formula (b := fun y => b y - 1) (hb.sub contMDiff_const) hh]
  have he1 : (fun y => b y * (1 + h y)) = fun y => b y + b y * h y := by
    funext y; ring
  have he2 : (fun y => (b y - 1) * h y) = fun y => b y * h y - h y := by
    funext y; ring
  rw [he1, he2, laplaceBeltrami_add (v := fun y => b y * h y) hb (hb.mul hh),
    laplaceBeltrami_sub (u := fun y => b y * h y) (hb.mul hh) hh, laplaceBeltrami_sub (v := fun _ => 1) hb contMDiff_const,
    laplaceBeltrami_add (u := fun _ => 1) contMDiff_const hh, laplaceBeltrami_const]
  ring

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_small_jets_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u →
      ∀ (x : E), x ∈ K → ∀ ε : ℝ, 0 ≤ ε →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E p).symm) x‖ ≤ ε) →
      ∀ j ≤ h, ‖iteratedFDeriv ℝ j ((laplaceBeltrami g u) ∘ (chartAt E p).symm) x‖ ≤ C*ε := by
  obtain ⟨C,hC,hJ⟩ := weightedLaplacian_small_jets_on_compact g p hK hKt h
  refine ⟨C,hC,?_⟩
  intro u hu x hx ε hε huJ
  have he : weightedLaplacian g (fun _ => 1) (fun z => u z+1) = laplaceBeltrami g u := by
    funext z
    have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun z => u z+1) := hu.add contMDiff_const
    rw [weightedLaplacian_expansion (b := fun _ => 1) (u := fun z => u z+1) contMDiff_const
      (hw.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    rw [laplaceBeltrami_add (u := u) (v := fun _ => 1)
      (hu.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) contMDiff_const,laplaceBeltrami_const]
    simp [coordinateGradientPair,Function.comp_def]
  have hh := hJ (fun _ => 1) (fun z => u z+1) contMDiff_const (hu.add contMDiff_const)
    x hx 1 ε zero_le_one hε (by
      intro j hj
      cases j with
      | zero => simp
      | succ j => simp [Function.comp_def,iteratedFDeriv_succ_const]) (by
      intro j hj
      simpa only [add_sub_cancel_right,Function.comp_def] using huJ j hj)
  rw [he] at hh
  simpa only [mul_one] using hh

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_residual_small_jets_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u →
      ∀ (x : E), x ∈ K → ∀ ε Λ : ℝ, 0 ≤ ε → 0 ≤ Λ →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (u ∘ (chartAt E p).symm) x‖ ≤ ε) →
      ∀ j ≤ h, ‖iteratedFDeriv ℝ j
        ((fun z => laplaceBeltrami g u z+Λ*u z) ∘ (chartAt E p).symm) x‖ ≤ (C+Λ)*ε := by
  obtain ⟨C,hC,hJ⟩ := laplaceBeltrami_small_jets_on_compact g p hK hKt h
  refine ⟨C,hC,?_⟩
  intro u hu x hx ε Λ hε hΛ huJ j hj
  have hc : ContDiffAt ℝ ∞ (u ∘ (chartAt E p).symm) x := contDiffAt_inChart hu p (hKt hx)
  have hl : ContDiffAt ℝ ∞ ((laplaceBeltrami g u) ∘ (chartAt E p).symm) x :=
    contDiffAt_inChart (contMDiff_laplaceBeltrami hu g) p (hKt hx)
  have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have he : ((fun z => laplaceBeltrami g u z+Λ*u z) ∘ (chartAt E p).symm) =
      (fun y => ((laplaceBeltrami g u) ∘ (chartAt E p).symm) y + Λ • (u ∘ (chartAt E p).symm) y) := rfl
  rw [he, fun_iteratedFDeriv_add_apply (hl.of_le hle) ((hc.const_smul Λ).of_le hle),
    iteratedFDeriv_const_smul_apply' (hc.of_le hle)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j ((laplaceBeltrami g u) ∘ (chartAt E p).symm) x‖ +
        ‖Λ • iteratedFDeriv ℝ j (u ∘ (chartAt E p).symm) x‖ := norm_add_le _ _
    _ ≤ C*ε + Λ*ε := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hΛ]
      exact add_le_add (hJ u hu x hx ε hε huJ j hj)
        (mul_le_mul_of_nonneg_left (huJ j (by omega)) hΛ)
    _ = (C+Λ)*ε := by ring

end

section
open Set Filter Metric Manifold
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem metric_unique_continuation_general [PreconnectedSpace M] (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (hsol : ∀ x, -laplaceBeltrami g u x = lam*u x)
    (hz : ∃ x, u =ᶠ[𝓝 x] 0) : u = 0 := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let L : E ≃L[ℝ] F := toEuclidean
  let Z := {x : M | u =ᶠ[𝓝 x] 0}
  have hZ : IsOpen Z := isOpen_setOfPred_eventually_nhds
  have hcl : closure Z ⊆ Z := by
    intro p hp
    obtain ⟨a,V,w,r,hr,ha,hT,hw,hpos,hP⟩ := exists_metric_ucp_model_equiv L g hu lam hsol p
    let c := chartAt E p
    have hps : p ∈ c.source := mem_chart_source E p
    have hb : ball (L (c p)) r ∈ 𝓝 (L (c p)) := ball_mem_nhds _ hr
    have hN : c.source ∩ (fun x => L (c x)) ⁻¹' ball (L (c p)) r ∈ 𝓝 p :=
      inter_mem (c.open_source.mem_nhds hps)
        ((L.continuous.continuousAt.comp (c.continuousAt hps)).preimage_mem_nhds hb)
    obtain ⟨x,hxN,hxZ⟩ := mem_closure_iff_nhds.mp hp _ hN
    have hct : c x ∈ c.target := c.map_source hxN.1
    have hctend : Tendsto (fun y => c.symm (L.symm y)) (𝓝 (L (c x))) (𝓝 x) := by
      have htL : Tendsto L.symm (𝓝 (L (c x))) (𝓝 (c x)) := by
        simpa only [L.symm_apply_apply] using L.symm.continuous.continuousAt.tendsto (x := L (c x))
      have ht := ((c.continuousAt_symm hct).tendsto).comp htL
      simpa only [L.symm_apply_apply,Function.comp_def,c.left_inv hxN.1] using ht
    have hzw : L (c x) ∈ zeroInterior w := by
      filter_upwards [isOpen_ball.mem_nhds hxN.2, hxZ.comp_tendsto hctend] with y hy hyz
      change w y = 0
      rw [hw y hy]
      exact hyz
    let e : Module.Basis (CoordIndex E) ℝ F := (Module.finBasis ℝ E).map L.toLinearEquiv
    have hwzero := weak_unique_continuation e a ha V w
      (ball (L (c p)) r) isOpen_ball (convex_ball (L (c p)) r).isPreconnected hpos hP
      ⟨L (c x),hxN.2,hzw⟩
    have hpzero : u =ᶠ[𝓝 p] 0 := by
      filter_upwards [hN] with x hx
      have hh := hwzero (L (c x)) hx.2
      rw [hw (L (c x)) hx.2,L.symm_apply_apply,c.left_inv hx.1] at hh
      exact hh
    exact hpzero
  have hsub : (univ : Set M) ⊆ Z := isPreconnected_univ.subset_of_closure_inter_subset hZ
    (by obtain ⟨x,hx⟩ := hz; exact ⟨x,mem_univ _,hx⟩) (fun _ hx => hcl hx.1)
  funext x
  exact (hsub (mem_univ x)).eq_of_nhds

lemma eigenfunction_nonzero_on_open_general [PreconnectedSpace M] (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (lam : ℝ)
    (hsol : ∀ x, -laplaceBeltrami g u x = lam*u x) (hun : u ≠ 0)
    (O : Set M) (hO : IsOpen O) (hne : O.Nonempty) : ∃ x ∈ O, u x ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨p,hp⟩ := hne
  apply hun
  apply metric_unique_continuation_general g hu lam hsol
  refine ⟨p,?_⟩
  filter_upwards [hO.mem_nhds hp] with x hx
  exact hn x hx


end

open Set Filter Function Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma transverse_zero_kernel (g : SmoothMetric E M) (u v : M → ℝ) (x : M)
    (hp : bundleTransverse g u x (metricGradient g v x) = 0)
    (w : TangentSpace 𝓘(ℝ,E) x) (hw : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x w = 0) :
    mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) v x w = 0 := by
  have hv : metricGradient g v x =
      (g.inner x (metricGradient g u x) (metricGradient g u x))⁻¹ •
        (g.inner x (metricGradient g u x) (metricGradient g v x) • metricGradient g u x) := by
    simpa only [bundleTransverse,sub_apply,ContinuousLinearMap.id_apply,
      smul_apply,bundleRankOne,ContinuousLinearMap.smulRight_apply,
      sub_eq_zero] using hp
  have hzero : g.inner x (metricGradient g u x) w = 0 :=
    (metricGradient_pairing g u x w).trans hw
  rw [←metricGradient_pairing g v x w,hv]
  erw [map_smul, smul_apply, map_smul, smul_apply, hzero]
  simp only [smul_zero]
  rfl
lemma transverse_zero_chart_kernel (g : SmoothMetric E M) {u v : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (hp : bundleTransverse g u ((chartAt E p).symm y)
      (metricGradient g v ((chartAt E p).symm y)) = 0) :
    ∀ w, fderiv ℝ (u ∘ (chartAt E p).symm) y w = 0 →
      fderiv ℝ (v ∘ (chartAt E p).symm) y w = 0 := by
  intro w hw
  have hd := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) p) hy).mdifferentiableAt (by simp)
  have he (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f) :
      fderiv ℝ (f ∘ (chartAt E p).symm) y w =
        mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f ((chartAt E p).symm y)
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y w) := by
    have hh := mfderiv_comp y (hf.mdifferentiable (by simp)).mdifferentiableAt hd
    rw [mfderiv_eq_fderiv] at hh
    exact congrArg (fun L => L w) hh
  rw [he u hu] at hw
  rw [he v hv]
  exact transverse_zero_kernel g u v _ hp _ hw
lemma proportional_eigen_global [PreconnectedSpace M] (g : SmoothMetric E M)
    {u v : M → ℝ} (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (ell c : ℝ)
    (hue : ∀ x, -laplaceBeltrami g u x = ell*u x)
    (hve : ∀ x, -laplaceBeltrami g v x = ell*v x)
    (he : ∃ x, v =ᶠ[𝓝 x] (fun y => c*u y)) : v = fun y => c*u y := by
  have hcu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun y => c*u y) := contMDiff_const.mul hu
  let w := fun y => v y - c*u y
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w := hv.sub (contMDiff_const.mul hu)
  have hscalar (x : M) : laplaceBeltrami g (fun y => c*u y) x = c * laplaceBeltrami g u x := by
    have hh := laplaceBeltrami_comp_at g x
      ((contDiff_const.mul contDiff_id : ContDiff ℝ 2 (fun s : ℝ => c*s)).contDiffAt) (hu.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
    have hd : deriv (fun s : ℝ => c*s) = fun _ => c := by
      funext s; simp
    simpa only [Function.comp_def,hd,deriv_const,mul_zero,zero_mul,add_zero] using hh
  have hsub (x : M) : laplaceBeltrami g w x =
      laplaceBeltrami g v x - laplaceBeltrami g (fun y => c*u y) x := by
    have hh := congrArg Complex.re (complexLaplaceBeltrami_sub
      (Complex.ofRealCLM.contMDiff.comp (hv.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))))
      (Complex.ofRealCLM.contMDiff.comp (hcu.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))) g x)
    simpa only [complexLaplaceBeltrami,Complex.sub_re,Complex.add_re,Complex.mul_re,
      Complex.I_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero,
      Function.comp_def,Complex.ofRealCLM_apply,Pi.sub_apply,w] using hh
  have hwz : w = 0 := metric_unique_continuation_general g hw ell (fun x => by
    rw [hsub,hscalar]
    dsimp only [w]
    rw [show laplaceBeltrami g v x = -ell*v x by linarith [hve x],
      show laplaceBeltrami g u x = -ell*u x by linarith [hue x]]
    ring) (by
      obtain ⟨x,hx⟩ := he
      refine ⟨x,?_⟩
      filter_upwards [hx] with y hy
      simp only [w,hy,sub_self,Pi.zero_apply])
  funext x
  have hh := congrFun hwz x
  change v x - c*u x = 0 at hh
  exact sub_eq_zero.mp hh



end YauCounterexamples
end

end OAI
