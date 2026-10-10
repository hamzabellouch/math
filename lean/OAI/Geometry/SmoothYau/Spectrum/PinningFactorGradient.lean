import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RectangularFactorization
import OAI.Geometry.SmoothYau.Smoothness.ChartJetBoundGlobalValue

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold
open scoped Topology ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma laplaceBeltrami_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (hu : u =ᶠ[𝓝 x] v) : laplaceBeltrami g u x=laplaceBeltrami g v x := by
  let c := chartAt E x
  have hx := c.map_source (mem_chart_source E x)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source E x)] using (c.continuousAt_symm hx).tendsto
  have hu' := (hu.comp_tendsto ht).fderiv (𝕜:=ℝ)
  have he (i : CoordIndex E) :
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))
      =ᶠ[𝓝 (c x)]
      (fun y => Real.sqrt (metricCoefficients g x y).det * ∑ j,
        (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (v ∘ c.symm) y (Module.finBasis ℝ E j)) := by
    filter_upwards [hu'] with y hy
    rw [hy]
  unfold laplaceBeltrami
  change (Real.sqrt (metricCoefficients g x (c x)).det)⁻¹ * ∑ i, _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T : E →L[ℝ] ℝ => T (Module.finBasis ℝ E i)) (he i).fderiv_eq

lemma laplaceBeltrami_tsupport (g : SmoothMetric E M) (u : M → ℝ) :
    tsupport (laplaceBeltrami g u) ⊆ tsupport u := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have he := laplaceBeltrami_congr_nhds g (notMem_tsupport_iff_eventuallyEq.mp hn)
  have hz : laplaceBeltrami g (fun _ : M => (0:ℝ)) x=0 := by
    simp [laplaceBeltrami,Function.comp_def]
  exact hx (he.trans hz)

lemma laplaceResidual_tsupport (g : SmoothMetric E M) (u : M → ℝ) (Λ : ℝ) :
    tsupport (fun x => laplaceBeltrami g u x+Λ*u x) ⊆ tsupport u := by
  apply (tsupport_add _ _).trans
  apply union_subset (laplaceBeltrami_tsupport g u)
  exact tsupport_mul_subset_right (f := fun _ : M => Λ) (g := u)

variable [T2Space M]

theorem compact_chart_weighted_jet_transfer (p q : M) {L : Set M} (hL : IsCompact L)
    (hLp : L ⊆ (chartAt E p).source) {K : Set E} (hK : IsCompact K)
    (hKq : K ⊆ (chartAt E q).target) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : M → ℝ) (f : E → ℝ), ContDiff ℝ ∞ f →
      tsupport U ⊆ L → (∀ z ∈ (chartAt E p).target, U ((chartAt E p).symm z)=f z) →
      ∀ (B : ℕ → M → ℝ), (∀ j x, 0 ≤ B j x) →
      (∀ x ∈ L, ∀ j ≤ m, ∀ i ≤ j,
        ‖iteratedFDeriv ℝ i f (chartAt E p x)‖ ≤ B j x) →
      ∀ y ∈ K, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (U ∘ (chartAt E q).symm) y‖ ≤ C*B j ((chartAt E q).symm y) := by
  obtain ⟨C,hC,hT⟩ := compact_chart_jet_transfer (F := ℝ) p q hL hLp hK hKq m
  refine ⟨C,hC,?_⟩
  intro U f hf hs he B hB hb y hy j hj
  by_cases hx : (chartAt E q).symm y ∈ L
  · exact hT U f hf hs he y hy j hj _ (hB j _) (fun i hi => hb _ hx j hj i hi)
  · have hn : (chartAt E q).symm y ∉ tsupport U := fun h => hx (hs h)
    have hzero : U ∘ (chartAt E q).symm =ᶠ[𝓝 y] (fun _ => (0:ℝ)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        ((chartAt E q).continuousAt_symm (hKq hy)).tendsto
    rw [(hzero.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa using mul_nonneg hC.le (hB j ((chartAt E q).symm y))


end



section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff

lemma pinning_factor_squared (F : ℝ → ℝ) {I : Set ℝ} (hIo : IsOpen I)
    (hIc : IsPreconnected I) (hF : ContDiffOn ℝ 2 F I)
    {n : ℕ} (hn : 2 ≤ n) {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr : r₀ < r₁)
    (he : ∀ s ∈ I, ∀ r ∈ ({r₀,r₁} : Set ℝ),
      (n : ℝ)^2 * deriv (deriv F) s * (r^(n-1) - s^2) +
        ((n : ℝ)*((n : ℝ)+2)) * (F s - s * deriv F s) = 0) :
    ∃ c : ℝ, ∀ s ∈ I, F s = c * s := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : r₀^(n-1) < r₁^(n-1) := pow_lt_pow_left₀ hr hr₀.le (by omega)
  have hsecond (s : ℝ) (hs : s ∈ I) : deriv (deriv F) s = 0 := by
    have h0 := he s hs r₀ (by simp)
    have h1 := he s hs r₁ (by simp)
    have hx : (n : ℝ)^2 * (r₁^(n-1)-r₀^(n-1)) ≠ 0 :=
      (mul_pos (sq_pos_of_pos hn₀) (sub_pos.mpr hp)).ne'
    have hz : ((n : ℝ)^2 * (r₁^(n-1)-r₀^(n-1))) * deriv (deriv F) s = 0 := by
      nlinarith [h0,h1]
    exact (mul_eq_zero.mp hz).resolve_left hx
  have hd : DifferentiableOn ℝ (deriv F) I :=
    (hF.deriv_of_isOpen (m := 1) hIo (by norm_num)).differentiableOn (by norm_num)
  obtain ⟨c,hc⟩ := hIo.exists_is_const_of_deriv_eq_zero hIc hd (fun s hs => hsecond s hs)
  refine ⟨c,fun s hs => ?_⟩
  have h0 := he s hs r₀ (by simp)
  rw [hsecond s hs,hc s hs] at h0
  have hlambda : (n : ℝ)*((n : ℝ)+2) ≠ 0 := (mul_pos hn₀ (by linarith)).ne'
  have hz : F s - s * c = 0 := (mul_eq_zero.mp (by simpa using h0)).resolve_left hlambda
  linarith
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma chart_germ_of_pullback {u v : M → ℝ} (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (he : (u ∘ (chartAt E p).symm) =ᶠ[𝓝 y] (v ∘ (chartAt E p).symm)) :
    u =ᶠ[𝓝 ((chartAt E p).symm y)] v := by
  let c := chartAt E p
  have hs : c.symm y ∈ c.source := c.map_target hy
  have ht : Tendsto c (𝓝 (c.symm y)) (𝓝 y) := by
    simpa only [c.right_inv hy] using (c.continuousAt hs).tendsto
  filter_upwards [he.comp_tendsto ht,c.open_source.mem_nhds hs] with z hz hzs
  change u (c.symm (c z)) = v (c.symm (c z)) at hz
  simpa only [c.left_inv hzs] using hz

theorem local_eigen_proportional_of_annular_rank
    (g : SmoothMetric E M) {u v R : M → ℝ} (p : M) {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hUt : U ⊆ (chartAt E p).target)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 v)
    (hdu : fderiv ℝ (u ∘ (chartAt E p).symm) x ≠ 0)
    (hker : ∀ y ∈ U, ∀ w, fderiv ℝ (u ∘ (chartAt E p).symm) y w = 0 →
      fderiv ℝ (v ∘ (chartAt E p).symm) y w = 0)
    (hpair : ContDiffAt ℝ 1 (fun y => (u ((chartAt E p).symm y), R ((chartAt E p).symm y))) x)
    (hrank : Function.Surjective (fderiv ℝ
      (fun y => (u ((chartAt E p).symm y), R ((chartAt E p).symm y))) x))
    (hR : 0 < R ((chartAt E p).symm x)) {n : ℕ} (hn : 2 ≤ n)
    (hue : ∀ y ∈ U, laplaceBeltrami g u ((chartAt E p).symm y) =
      -((n:ℝ)*((n:ℝ)+2)) * u ((chartAt E p).symm y))
    (hve : ∀ y ∈ U, laplaceBeltrami g v ((chartAt E p).symm y) =
      -((n:ℝ)*((n:ℝ)+2)) * v ((chartAt E p).symm y))
    (hquad : ∀ y ∈ U, coordinateGradientPair g u u ((chartAt E p).symm y) =
      (n:ℝ)^2 * ((R ((chartAt E p).symm y))^(n-1) - (u ((chartAt E p).symm y))^2)) :
    ∃ c : ℝ, v =ᶠ[𝓝 ((chartAt E p).symm x)] (fun y => c*u y) := by
  let chart := chartAt E p
  let f := u ∘ chart.symm
  let h := v ∘ chart.symm
  let H : E → ℝ × ℝ := fun y => (f y, R (chart.symm y))
  have hf : ContDiffOn ℝ 2 f U := fun y hy =>
    (contDiffAt_inChart_C2 hu p (hUt hy)).contDiffWithinAt
  have hh : ContDiffOn ℝ 2 h U := fun y hy =>
    (contDiffAt_inChart_C2 hv p (hUt hy)).contDiffWithinAt
  obtain ⟨V,I,F,hVo,hxV,hVU,hIo,hIc,hfxI,hF,hfV,hVF⟩ :=
    local_factor_of_kernel hU hx hf hh hdu hker
  have hlocal (y : E) (hy : y ∈ V) :
      v =ᶠ[𝓝 (chart.symm y)] (F ∘ u) := by
    apply chart_germ_of_pullback p (hUt (hVU hy))
    filter_upwards [hVo.mem_nhds hy] with z hz
    exact hVF hz
  have hPDE (y : E) (hy : y ∈ V) :
      (n:ℝ)^2 * deriv (deriv F) (f y) * ((R (chart.symm y))^(n-1) - (f y)^2) +
      ((n:ℝ)*((n:ℝ)+2)) * (F (f y) - f y * deriv F (f y)) = 0 := by
    have hcomp := laplaceBeltrami_comp_at g (chart.symm y)
      ((hF _ (hfV hy)).contDiffAt (hIo.mem_nhds (hfV hy))) hu
    rw [← laplaceBeltrami_congr_nhds g (hlocal y hy),hue y (hVU hy),hve y (hVU hy),hquad y (hVU hy)] at hcomp
    have hval : v (chart.symm y) = F (f y) := hVF hy
    rw [hval] at hcomp
    change -((n:ℝ)*((n:ℝ)+2))*F (f y) =
      deriv F (f y) * (-((n:ℝ)*((n:ℝ)+2))*f y) +
      deriv (deriv F) (f y) * ((n:ℝ)^2 * ((R (chart.symm y))^(n-1) - (f y)^2)) at hcomp
    linear_combination -hcomp
  have hmap : Filter.map H (𝓝 x) = 𝓝 (H x) :=
    (hpair.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hrank)
  have himage : H '' V ∈ 𝓝 (H x) := by
    rw [←hmap]
    exact Filter.image_mem_map (hVo.mem_nhds hxV)
  have hbox : I ×ˢ Ioi (0:ℝ) ∈ 𝓝 (H x) :=
    (hIo.prod isOpen_Ioi).mem_nhds ⟨hfxI,hR⟩
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp (inter_mem himage hbox)
  let K := ball (f x) ε
  let r₀ := R (chart.symm x) - ε/2
  let r₁ := R (chart.symm x) + ε/2
  have hr₀B : r₀ ∈ ball (R (chart.symm x)) ε := by
    rw [mem_ball,Real.dist_eq,abs_lt]; dsimp [r₀]; constructor <;> linarith
  have hr₁B : r₁ ∈ ball (R (chart.symm x)) ε := by
    rw [mem_ball,Real.dist_eq,abs_lt]; dsimp [r₁]; constructor <;> linarith
  have hpairmem (s : ℝ) (hs : s ∈ K) (r : ℝ) (hr : r ∈ ({r₀,r₁}:Set ℝ)) :
      (s,r) ∈ H '' V ∩ (I ×ˢ Ioi (0:ℝ)) := by
    apply hεsub
    change (s,r) ∈ ball (f x,R (chart.symm x)) ε
    rw [←ball_prod_same]
    refine ⟨hs,?_⟩
    simp only [mem_insert_iff,mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> assumption
  have hKI : K ⊆ I := fun s hs => (hpairmem s hs r₀ (by simp)).2.1
  have hr₀pos : 0 < r₀ := (hpairmem (f x) (mem_ball_self hε) r₀ (by simp)).2.2
  have hrr : r₀ < r₁ := by dsimp [r₀,r₁]; linarith
  obtain ⟨a,ha⟩ := pinning_factor_squared F isOpen_ball (convex_ball (f x) ε).isPreconnected
    (hF.mono hKI) hn hr₀pos hrr (fun s hs r hr => by
      obtain ⟨y,hy,hyr⟩ := (hpairmem s hs r hr).1
      have hs' : f y = s := congrArg Prod.fst hyr
      have hr' : R (chart.symm y) = r := congrArg Prod.snd hyr
      simpa only [hs',hr'] using hPDE y hy)
  refine ⟨a,chart_germ_of_pullback p (hUt hx) ?_⟩
  have hnx : f ⁻¹' K ∈ 𝓝 x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε))
  filter_upwards [hVo.mem_nhds hxV,hnx] with y hy hyK
  exact (hVF hy).trans (ha (f y) hyK)


end

open Set Filter Function Manifold Metric
open scoped Topology ContDiff
lemma pinning_factor_gradient (F : ℝ → ℝ) {I : Set ℝ} (hIo : IsOpen I)
    (hIc : IsPreconnected I) (hF : ContDiffOn ℝ 2 F I)
    {Λ : ℝ} (hΛ : 0<Λ) {r₀ r₁ : ℝ} (hr : r₀<r₁)
    (he : ∀ s ∈ I, ∀ r ∈ ({r₀,r₁}:Set ℝ),
      deriv (deriv F) s*r + Λ*(F s-s*deriv F s)=0) :
    ∃ c : ℝ, ∀ s ∈ I, F s=c*s := by
  have hsecond (s : ℝ) (hs : s∈I) : deriv (deriv F) s=0 := by
    have h0 := he s hs r₀ (by simp)
    have h1 := he s hs r₁ (by simp)
    have hz : (r₁-r₀)*deriv (deriv F) s=0 := by nlinarith [h0,h1]
    exact (mul_eq_zero.mp hz).resolve_left (sub_pos.mpr hr).ne'
  have hd : DifferentiableOn ℝ (deriv F) I :=
    (hF.deriv_of_isOpen (m:=1) hIo (by norm_num)).differentiableOn (by norm_num)
  obtain ⟨c,hc⟩ := hIo.exists_is_const_of_deriv_eq_zero hIc hd hsecond
  refine ⟨c,fun s hs => ?_⟩
  have h0 := he s hs r₀ (by simp)
  rw [hsecond s hs,hc s hs] at h0
  have hz : F s-s*c=0 := (mul_eq_zero.mp (by simpa using h0)).resolve_left hΛ.ne'
  linarith
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem local_eigen_proportional_of_gradient_rank
    (g : SmoothMetric E M) {u v R : M → ℝ} (p : M) {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hUt : U ⊆ (chartAt E p).target)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 u)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) 2 v)
    (hdu : fderiv ℝ (u ∘ (chartAt E p).symm) x ≠ 0)
    (hker : ∀ y ∈ U, ∀ w, fderiv ℝ (u ∘ (chartAt E p).symm) y w = 0 →
      fderiv ℝ (v ∘ (chartAt E p).symm) y w = 0)
    (hpair : ContDiffAt ℝ 1 (fun y => (u ((chartAt E p).symm y), R ((chartAt E p).symm y))) x)
    (hrank : Function.Surjective (fderiv ℝ
      (fun y => (u ((chartAt E p).symm y), R ((chartAt E p).symm y))) x))
    (hR : 0 < R ((chartAt E p).symm x)) {Λ : ℝ} (hΛ : 0 < Λ)
    (hue : ∀ y ∈ U, laplaceBeltrami g u ((chartAt E p).symm y) =
      -Λ * u ((chartAt E p).symm y))
    (hve : ∀ y ∈ U, laplaceBeltrami g v ((chartAt E p).symm y) =
      -Λ * v ((chartAt E p).symm y))
    (hquad : ∀ y ∈ U, coordinateGradientPair g u u ((chartAt E p).symm y) =
      R ((chartAt E p).symm y)) :
    ∃ c : ℝ, v =ᶠ[𝓝 ((chartAt E p).symm x)] (fun y => c*u y) := by
  let chart := chartAt E p
  let f := u ∘ chart.symm
  let h := v ∘ chart.symm
  let H : E → ℝ × ℝ := fun y => (f y, R (chart.symm y))
  have hf : ContDiffOn ℝ 2 f U := fun y hy =>
    (contDiffAt_inChart_C2 hu p (hUt hy)).contDiffWithinAt
  have hh : ContDiffOn ℝ 2 h U := fun y hy =>
    (contDiffAt_inChart_C2 hv p (hUt hy)).contDiffWithinAt
  obtain ⟨V,I,F,hVo,hxV,hVU,hIo,hIc,hfxI,hF,hfV,hVF⟩ :=
    local_factor_of_kernel hU hx hf hh hdu hker
  have hlocal (y : E) (hy : y ∈ V) :
      v =ᶠ[𝓝 (chart.symm y)] (F ∘ u) := by
    apply chart_germ_of_pullback p (hUt (hVU hy))
    filter_upwards [hVo.mem_nhds hy] with z hz
    exact hVF hz
  have hPDE (y : E) (hy : y ∈ V) :
      deriv (deriv F) (f y) * R (chart.symm y) +
      Λ * (F (f y) - f y * deriv F (f y)) = 0 := by
    have hcomp := laplaceBeltrami_comp_at g (chart.symm y)
      ((hF _ (hfV hy)).contDiffAt (hIo.mem_nhds (hfV hy))) hu
    rw [← laplaceBeltrami_congr_nhds g (hlocal y hy),hue y (hVU hy),hve y (hVU hy),hquad y (hVU hy)] at hcomp
    have hval : v (chart.symm y) = F (f y) := hVF hy
    rw [hval] at hcomp
    change -Λ*F (f y) =
      deriv F (f y) * (-Λ*f y) +
      deriv (deriv F) (f y) * R (chart.symm y) at hcomp
    linear_combination -hcomp
  have hmap : Filter.map H (𝓝 x) = 𝓝 (H x) :=
    (hpair.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hrank)
  have himage : H '' V ∈ 𝓝 (H x) := by
    rw [←hmap]
    exact Filter.image_mem_map (hVo.mem_nhds hxV)
  have hbox : I ×ˢ Ioi (0:ℝ) ∈ 𝓝 (H x) :=
    (hIo.prod isOpen_Ioi).mem_nhds ⟨hfxI,hR⟩
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp (inter_mem himage hbox)
  let K := ball (f x) ε
  let r₀ := R (chart.symm x) - ε/2
  let r₁ := R (chart.symm x) + ε/2
  have hr₀B : r₀ ∈ ball (R (chart.symm x)) ε := by
    rw [mem_ball,Real.dist_eq,abs_lt]; dsimp [r₀]; constructor <;> linarith
  have hr₁B : r₁ ∈ ball (R (chart.symm x)) ε := by
    rw [mem_ball,Real.dist_eq,abs_lt]; dsimp [r₁]; constructor <;> linarith
  have hpairmem (s : ℝ) (hs : s ∈ K) (r : ℝ) (hr : r ∈ ({r₀,r₁}:Set ℝ)) :
      (s,r) ∈ H '' V ∩ (I ×ˢ Ioi (0:ℝ)) := by
    apply hεsub
    change (s,r) ∈ ball (f x,R (chart.symm x)) ε
    rw [←ball_prod_same]
    refine ⟨hs,?_⟩
    simp only [mem_insert_iff,mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> assumption
  have hKI : K ⊆ I := fun s hs => (hpairmem s hs r₀ (by simp)).2.1
  have hrr : r₀ < r₁ := by dsimp [r₀,r₁]; linarith
  obtain ⟨a,ha⟩ := pinning_factor_gradient F isOpen_ball (convex_ball (f x) ε).isPreconnected
    (hF.mono hKI) hΛ hrr (fun s hs r hr => by
      obtain ⟨y,hy,hyr⟩ := (hpairmem s hs r hr).1
      have hs' : f y = s := congrArg Prod.fst hyr
      have hr' : R (chart.symm y) = r := congrArg Prod.snd hyr
      simpa only [hs',hr'] using hPDE y hy)
  refine ⟨a,chart_germ_of_pullback p (hUt hx) ?_⟩
  have hnx : f ⁻¹' K ∈ 𝓝 x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε))
  filter_upwards [hVo.mem_nhds hxV,hnx] with y hy hyK
  exact (hVF hy).trans (ha (f y) hyK)

end YauCounterexamples
end

end OAI
