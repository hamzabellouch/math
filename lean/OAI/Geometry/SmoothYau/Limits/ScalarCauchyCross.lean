import Mathlib
import OAI.Geometry.SmoothYau.Geometry.AnnularRelativeMargin

namespace OAI

noncomputable section
namespace YauCounterexamples
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
open Set Filter
open scoped Topology ContDiff Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma weightedLaplacian_congr_nhds (g : SmoothMetric E M) {b c u v : M → ℝ} {x : M}
    (hb : b =ᶠ[𝓝 x] c) (hu : u =ᶠ[𝓝 x] v) :
    weightedLaplacian g b u x = weightedLaplacian g c v x := by
  let chart := chartAt E x
  have hx := chart.map_source (mem_chart_source E x)
  have ht : Tendsto chart.symm (𝓝 (chart x)) (𝓝 x) := by
    simpa only [chart.left_inv (mem_chart_source E x)] using
      (chart.continuousAt_symm hx).tendsto
  have hb' := hb.comp_tendsto ht
  have hu' := (hu.comp_tendsto ht).fderiv (𝕜:=ℝ)
  have he (i : CoordIndex E) :
      (fun y => b (chart.symm y) *
        (Real.sqrt (metricCoefficients g x y).det * ∑ j,
          (metricCoefficients g x y)⁻¹ i j *
          fderiv ℝ (u ∘ chart.symm) y (Module.finBasis ℝ E j))) =ᶠ[𝓝 (chart x)]
      (fun y => c (chart.symm y) *
        (Real.sqrt (metricCoefficients g x y).det * ∑ j,
          (metricCoefficients g x y)⁻¹ i j *
          fderiv ℝ (v ∘ chart.symm) y (Module.finBasis ℝ E j))) := by
    filter_upwards [hb',hu'] with y hby huy
    simp only [Function.comp_apply] at hby
    rw [hby,huy]
  unfold weightedLaplacian
  change (Real.sqrt (metricCoefficients g x (chart x)).det)⁻¹ * ∑ i, _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun T : E →L[ℝ] ℝ => T (Module.finBasis ℝ E i)) (he i).fderiv_eq

lemma weightedLaplacian_const (g : SmoothMetric E M) (b : M → ℝ) (c : ℝ) (x : M) :
    weightedLaplacian g b (fun _ => c) x = 0 := by
  simp [weightedLaplacian,Function.comp_def]

lemma coordinateGradientPair_cauchy (g : SmoothMetric E M) (u v : M → ℝ) (x : M) :
    coordinateGradientPair g u v x ^ 2 ≤
      coordinateGradientPair g u u x * coordinateGradientPair g v v x := by
  let c := chartAt E x
  let a := (metricCoefficients g x (c x))⁻¹
  let du := fun i => fderiv ℝ (u ∘ c.symm) (c x) (Module.finBasis ℝ E i)
  let dv := fun i => fderiv ℝ (v ∘ c.symm) (c x) (Module.finBasis ℝ E i)
  have hp := (metricCoefficients_posDef g x (c.map_source (mem_chart_source E x))).inv
  have he (f h : M → ℝ) : coordinateGradientPair g f h x =
      (fun i => fderiv ℝ (f ∘ c.symm) (c x) (Module.finBasis ℝ E i)) ⬝ᵥ
        (a *ᵥ (fun i => fderiv ℝ (h ∘ c.symm) (c x) (Module.finBasis ℝ E i))) := by
    simp only [coordinateGradientPair,dotProduct,Matrix.mulVec,Finset.mul_sum,a,c]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he u v,he u u,he v v]
  exact real_matrix_cauchy hp.posSemidef du dv

lemma conjugate_gradient_nonzero {U v : M → ℝ}
    (hU : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v) (g : SmoothMetric E M)
    (hv0 : ∀ x, v x ≠ 0) (x : M)
    (hmargin : U x^2*coordinateGradientPair g v v x <
      v x^2*coordinateGradientPair g U U x) :
    coordinateGradientPair g (fun y => U y/v y) (fun y => U y/v y) x ≠ 0 := by
  let u := fun y => U y/v y
  have hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u := hU.div₀ hv hv0
  have he : U = fun y => v y*u y := by funext y; dsimp [u]; field_simp [hv0 y]
  intro hz
  have hc := coordinateGradientPair_cauchy g v u x
  rw [hz,mul_zero] at hc
  have hcross : coordinateGradientPair g v u x=0 := by nlinarith [sq_nonneg (coordinateGradientPair g v u x)]
  have hcross' : coordinateGradientPair g u v x=0 := by rw [coordinateGradientPair_symm,hcross]
  have h₁ := coordinateGradientPair_mul_left hv hu U g x
  have h₂ := coordinateGradientPair_mul_left hv hu u g x
  have h₃ := coordinateGradientPair_mul_left hv hu v g x
  have hpair : coordinateGradientPair g U U x=u x^2*coordinateGradientPair g v v x := by
    rw [←he] at h₁ h₂ h₃
    rw [h₁,coordinateGradientPair_symm g u U x,h₂,
      coordinateGradientPair_symm g v U x,h₃,hz,hcross,hcross']
    ring
  rw [hpair] at hmargin
  have hUx : U x=v x*u x := congrFun he x
  rw [hUx] at hmargin
  nlinarith

def cutoffFactor (χ v : M → ℝ) (x : M) : ℝ := 1+χ x*(v x-1)

omit [TopologicalSpace M] in
lemma cutoffFactor_pos {χ v : M → ℝ} (hχ : ∀ x, χ x ∈ Icc (0:ℝ) 1)
    (hv : ∀ x, 0 < v x) (x : M) : 0 < cutoffFactor χ v x := by
  have h := hχ x
  by_cases hχ0 : χ x=0
  · simp [cutoffFactor,hχ0]
  · have hp : 0 < χ x*v x := mul_pos (lt_of_le_of_ne h.1 (Ne.symm hχ0)) (hv x)
    dsimp [cutoffFactor]
    nlinarith [h.2]

theorem cutoff_conductivity_exactification
    (hdim : Module.finrank ℝ E=3) (g : SmoothMetric E M)
    {b s U v χ : M → ℝ} {Λ : ℝ} {O F : Set M}
    (hb : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b)
    (hs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s)
    (hU : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U)
    (hv : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ)
    (hΛ : Λ ≠ 0) (hbpos : ∀ x, 0 < b x)
    (hχrange : ∀ x, χ x ∈ Icc (0:ℝ) 1)
    (hvsmall : ∀ x, |v x-1| ≤ 1/2)
    (hssmall : ∀ x, |s x-1| ≤ 1/2)
    (hweighted : ∀ x, weightedLaplacian g b U x+Λ*s x*U x=0)
    (hfactor : ∀ x, weightedLaplacian g b v x=Λ*b x^3*v x^5-Λ*s x*v x)
    (hO : IsOpen O) (hF : IsOpen F)
    (hχO : ∀ x ∈ O, χ x=1) (hχF : ∀ x ∈ F, χ x=0)
    (hext : ∀ x ∈ F, b x=1 ∧ s x=1)
    (hsmall : ∀ x, |Λ⁻¹*cutoffFactor χ v x*weightedLaplacian g b (cutoffFactor χ v) x| ≤ 1/16)
    (hmargin : ∀ x ∉ O ∪ F,
      U x^2*coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x <
        cutoffFactor χ v x^2*coordinateGradientPair g U U x) :
    ∃ ĝ : SmoothMetric E M, ∃ u : M → ℝ,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u ∧
      (∀ x, -laplaceBeltrami ĝ u x=Λ*u x) ∧
      (∀ x, u x=U x/cutoffFactor χ v x) ∧
      (∀ x, u x=0 ↔ U x=0) ∧ (∀ x, 0 < u x ↔ 0 < U x) ∧
      (∀ x ∈ F, (∀ a c, ĝ.inner x a c=g.inner x a c) ∧ u x=U x) := by
  classical
  let w := cutoffFactor χ v
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hwsmall (x : M) : |w x-1| ≤ 1/2 := by
    change |1+χ x*(v x-1)-1| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (hχrange x).1]
    calc
      χ x*|v x-1| ≤ 1*|v x-1| := mul_le_mul_of_nonneg_right (hχrange x).2 (abs_nonneg _)
      _ ≤ 1/2 := by simpa using hvsmall x
  have hwge (x : M) : 1/2 ≤ w x := by have h := (abs_le.mp (hwsmall x)).1; linarith
  have hwpos (x : M) : 0 < w x := by linarith [hwge x]
  let q := fun x => b x*w x^2
  let d := fun x => s x*w x^2+Λ⁻¹*w x*weightedLaplacian g b w x
  have hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q := hb.mul (hw.pow 2)
  have hd : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d :=
    (hs.mul (hw.pow 2)).add ((contMDiff_const.mul hw).mul (contMDiff_weightedLaplacian hb hw g))
  have hqpos (x : M) : 0 < q x := mul_pos (hbpos x) (sq_pos_of_pos (hwpos x))
  have hdpos (x : M) : 0 < d x := by
    have hsge : 1/2 ≤ s x := by have h := (abs_le.mp (hssmall x)).1; linarith
    have hw2 : 1/4 ≤ w x^2 := by nlinarith [hwge x]
    have hsw : 1/8 ≤ s x*w x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hsge) (sq_nonneg (w x))]
    have hz := (abs_le.mp (hsmall x)).1
    change -(1/16) ≤ Λ⁻¹*w x*weightedLaplacian g b w x at hz
    dsimp only [d]
    linarith
  have hwO {x : M} (hx : x ∈ O) : w =ᶠ[𝓝 x] v := by
    filter_upwards [hO.mem_nhds hx] with y hy
    simp [w,cutoffFactor,hχO y hy]
  have hwF {x : M} (hx : x ∈ F) : w =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hF.mem_nhds hx] with y hy
    simp [w,cutoffFactor,hχF y hy]
  have hcompat {x : M} (hx : x ∈ O) : d x=q x^3 := by
    have he := weightedLaplacian_congr_nhds g (Filter.EventuallyEq.rfl (f:=b)) (hwO hx)
    dsimp only [d,q]
    rw [he,(hwO hx).eq_of_nhds,hfactor x]
    field_simp [hΛ]
    ring
  have hde {x : M} (hx : x ∈ F) : d x=1 ∧ q x=1 := by
    have he := weightedLaplacian_congr_nhds g (Filter.EventuallyEq.rfl (f:=b)) (hwF hx)
    rw [weightedLaplacian_const] at he
    dsimp only [d,q]
    rw [he,(hwF hx).eq_of_nhds,(hext x hx).1,(hext x hx).2]
    simp
  have hsupp : tsupport (fun x => d x-q x^3) ⊆ (O ∪ F)ᶜ := by
    apply closure_minimal _ (hO.union hF).isClosed_compl
    intro x hx
    rw [mem_compl_iff,mem_union]
    rintro (hxo|hxf)
    · exact hx (sub_eq_zero.mpr (hcompat hxo))
    · obtain ⟨hde,hqe⟩ := hde hxf
      exact hx (by change d x-q x^3=0; rw [hde,hqe]; norm_num)
  let u := fun x => U x/w x
  have hu := hU.div₀ hw (fun x => (hwpos x).ne')
  have hsupp' : tsupport (fun x => d x-q x^3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0} := by
    intro x hx
    exact conjugate_gradient_nonzero hU hw g (fun y => (hwpos y).ne') x (hmargin x (hsupp hx))
  obtain ⟨ĝ,heq,hmetric⟩ := conductivity_metric_realization hdim g u hu d q hd hq hdpos hqpos hsupp'
  refine ⟨ĝ,u,hu,?_,fun _ => rfl,?_,?_,?_⟩
  · intro x
    have hz := intrinsic_conjugated_equation hb hU hw g hΛ (fun x => (hwpos x).ne') hweighted x
    change weightedLaplacian g q u x+Λ*d x*u x=0 at hz
    rw [heq]
    have hdn := (hdpos x).ne'
    field_simp
    nlinarith [hz]
  · intro x
    change U x/w x=0 ↔ U x=0
    simp [(hwpos x).ne']
  · intro x
    exact div_pos_iff_of_pos_right (hwpos x)
  · intro x hx
    obtain ⟨hdx,hqx⟩ := hde hx
    refine ⟨hmetric x hdx hqx,?_⟩
    change U x/w x=U x
    rw [(hwF hx).eq_of_nhds,div_one]

end

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
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace

lemma scalar_cauchy_cross {a b c X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hc : c^2 ≤ X*Y) : 2*a*b*c ≤ a^2*X+b^2*Y := by
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg (a*b))
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith [sq_nonneg (a^2*X-b^2*Y)]

lemma coordinateGradientPair_mul_self_le {E M : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    {f u : M → ℝ} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ f)
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (g : SmoothMetric E M) (x : M) :
    coordinateGradientPair g (fun y => f y*u y) (fun y => f y*u y) x ≤
      2*(f x)^2*coordinateGradientPair g u u x + 2*(u x)^2*coordinateGradientPair g f f x := by
  have hc := scalar_cauchy_cross (a:=f x) (b:=u x)
    (coordinateGradientPair_nonneg g u x) (coordinateGradientPair_nonneg g f x)
    (coordinateGradientPair_cauchy g u f x)
  rw [coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_symm g u (fun y => f y*u y) x,
    coordinateGradientPair_symm g f (fun y => f y*u y) x,
    coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_mul_left hf hu,
    coordinateGradientPair_symm g f u x]
  nlinarith

lemma annular_conjugate_gradient_lower (n : ℕ) (hn : 1 ≤ n)
    {R t U u w Gu Gw : ℝ} (hR : 0 < R) (hRt : R ≤ t) (ht : t < 1)
    (hU : U^2 ≤ R^n) (he : U=w*u) (hwl : 1/2 ≤ w) (hwu : w ≤ 2)
    (hGu : 0 ≤ Gu) (hGw : 0 ≤ Gw) (hGws : Gw ≤ (1-t)/16)
    (hgrad : (n:ℝ)^2*(R^(n-1)-U^2) ≤ 2*w^2*Gu+2*u^2*Gw) :
    (1-t)/16*(n:ℝ)^2*R^n ≤ Gu := by
  have hnR : 1 ≤ (n:ℝ)^2 := by
    have hh : 1 ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith
  have hR1 : R ≤ 1 := hRt.trans ht.le
  have hRp : 0 < R^(n-1) := pow_pos hR _
  have hRn : R^n=R^(n-1)*R := by rw [←pow_succ,Nat.sub_add_cancel hn]
  have hstep : R^n ≤ R^(n-1) := by rw [hRn]; nlinarith [mul_le_mul_of_nonneg_left hR1 hRp.le]
  have hdiff : (1-t)*R^n ≤ R^(n-1)-U^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hRt hRp.le
    have h₂ := mul_le_mul_of_nonneg_left hstep (sub_pos.mpr ht).le
    rw [hRn] at hU
    nlinarith
  have hwwl : 1/4 ≤ w^2 := by nlinarith
  have hwwu : w^2 ≤ 4 := by nlinarith
  have huu : u^2 ≤ 4*R^n := by
    have hh := mul_le_mul_of_nonneg_right hwwl (sq_nonneg u)
    rw [he] at hU
    nlinarith
  have hsmall : 2*u^2*Gw ≤ (1-t)/2*R^n := by
    have hh := mul_le_mul huu hGws hGw (by positivity : 0 ≤ 4*R^n)
    nlinarith
  have hbig : 2*w^2*Gu ≤ 8*Gu := by nlinarith [mul_le_mul_of_nonneg_right hwwu hGu]
  have hlower := mul_le_mul_of_nonneg_left hdiff (sq_nonneg (n:ℝ))
  have hfreq := mul_le_mul_of_nonneg_right hnR (mul_nonneg (sub_pos.mpr ht).le (pow_nonneg hR.le n))
  nlinarith

variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_conjugate_gradient_lower
    (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ v z : TangentSpace 𝓘(ℝ,Euclidean d) p,
      g.inner p v z = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p z))
    (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
    (ha : inner ℝ a a=1) (hb : inner ℝ b b=1) (hab : inner ℝ a b=0)
    {t : ℝ} (hR : 0 < Complex.normSq (planarLinear a b p))
    (hRt : Complex.normSq (planarLinear a b p) ≤ t) (ht : t < 1)
    (w : Sphere d → ℝ) (hw : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ w)
    (hw0 : ∀ x, w x ≠ 0) (hwl : 1/2 ≤ w p) (hwu : w p ≤ 2)
    (hG : coordinateGradientPair g w w p ≤ (1-t)/16) :
    (1-t)/16*(n:ℝ)^2*Complex.normSq (planarLinear a b p)^n ≤
      coordinateGradientPair g (fun x => roundPower a b n x/w x)
        (fun x => roundPower a b n x/w x) p := by
  let u := fun x => roundPower a b n x/w x
  have hU := roundPower_smooth a b n
  have hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u := hU.div₀ hw hw0
  have he : roundPower a b n = fun x => w x*u x := by funext x; dsimp [u]; field_simp [hw0 x]
  have hupper := coordinateGradientPair_mul_self_le hw hu g p
  rw [←he,roundPower_coordinateGradientPair g p hg a b n hn ha hb hab] at hupper
  exact annular_conjugate_gradient_lower n hn hR hRt ht
    (complex_power_real_sq_bound (planarLinear a b p) n) (congrFun he p) hwl hwu
    (coordinateGradientPair_nonneg g u p) (coordinateGradientPair_nonneg g w p) hG hupper


end YauCounterexamples
end

end OAI
