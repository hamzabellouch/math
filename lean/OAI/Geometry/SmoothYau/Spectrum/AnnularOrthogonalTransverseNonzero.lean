import Mathlib
import OAI.Geometry.SmoothYau.Geometry.CoordinateGradientPairCongrNhds
import OAI.Geometry.SmoothYau.Smoothness.ExistsSupportedPinningBump

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace
section Orthogonality
variable {M : Type*} [TopologicalSpace M] [CompactSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M]
lemma proportional_orthogonal_zero (μ : Measure M) [Measure.IsOpenPosMeasure μ]
    [IsFiniteMeasureOnCompacts μ] {u v : M → ℝ} (hv : Continuous v)
    (ht : ∃ t : ℝ, v = fun x => t*u x) (ho : ∫ x, v x*u x ∂μ = 0) : v = 0 := by
  by_contra hn
  obtain ⟨x,hx⟩ : ∃ x, v x ≠ 0 := by
    by_contra hn'; push Not at hn'; exact hn (funext hn')
  have hp : 0 < ∫ x, v x*v x ∂μ :=
    (hv.mul hv).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun x => mul_self_nonneg (v x))
      (mul_self_pos.mpr hx).ne'
  obtain ⟨t,ht⟩ := ht
  have he : (fun x => v x*v x) = fun x => t*(v x*u x) := by
    funext x
    rw [congrFun ht x]
    ring
  rw [he, integral_const_mul, ho, mul_zero] at hp
  exact (lt_irrefl 0) hp
end Orthogonality
section Gradient
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma metricGradient_ne_zero_of_chart (g : SmoothMetric E M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (p : M) {y : E}
    (hy : y ∈ (chartAt E p).target)
    (hd : fderiv ℝ (u ∘ (chartAt E p).symm) y ≠ 0) :
    metricGradient g u ((chartAt E p).symm y) ≠ 0 := by
  intro hz
  apply hd
  have hf := (contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) p) hy).mdifferentiableAt (by simp)
  have hh := mfderiv_comp y (hu.mdifferentiable (by simp)).mdifferentiableAt hf
  rw [mfderiv_eq_fderiv] at hh
  ext w
  have he : fderiv ℝ (u ∘ (chartAt E p).symm) y w =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u ((chartAt E p).symm y)
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (chartAt E p).symm y w) :=
    congrArg (fun L => L w) hh
  rw [he,←metricGradient_pairing g u _ _,hz]
  simp
end Gradient
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩
lemma annular_gradient_ne_zero (g : SmoothMetric (Euclidean d) (Sphere d))
    (a b : Euclidean (d+1)) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1)
    (hab : inner ℝ a b = 0) (n : ℕ) (hn : 1 ≤ n) {l h : ℝ}
    (hl : 0 < l) (hh : h < 1) {u : Sphere d → ℝ}
    (hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u)
    (hup : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (p : Sphere d) (hpl : l < Complex.normSq (planarLinear a b p))
    (hph : Complex.normSq (planarLinear a b p) < h) : metricGradient g u p ≠ 0 := by
  have hp : (chartAt (Euclidean d) p).symm 0 = p := by
    simpa only [sphere_chart_center] using (chartAt (Euclidean d) p).left_inv (mem_chart_source _ p)
  have hA := round_annulus_open a b l h
  have he : (u ∘ (chartAt (Euclidean d) p).symm) =ᶠ[𝓝 0]
      (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) := by
    have hx : (0 : Euclidean d) ∈ (chartAt (Euclidean d) p).symm ⁻¹'
        {q : Sphere d | l < Complex.normSq (planarLinear a b q) ∧
          Complex.normSq (planarLinear a b q) < h} := by
      change l < Complex.normSq (planarLinear a b ((chartAt (Euclidean d) p).symm 0)) ∧ _
      rw [hp]; exact ⟨hpl,hph⟩
    filter_upwards [(hA.preimage (sphere_chart_symm_continuous_general p)).mem_nhds hx] with y hy
    exact hup _ hy.1 hy.2
  have hd : fderiv ℝ (u ∘ (chartAt (Euclidean d) p).symm) 0 ≠ 0 := by
    rw [he.fderiv_eq]
    exact roundPower_annulus_noncritical a b n hn ha hb hab p (hl.trans hpl) (hph.trans hh)
  have hz := metricGradient_ne_zero_of_chart g hu p
    (show (0 : Euclidean d) ∈ (chartAt (Euclidean d) p).target by
      rw [sphere_chart_target]; exact mem_univ _) hd
  change (fun q : Sphere d => metricGradient g u q ≠ 0) ((chartAt (Euclidean d) p).symm 0) at hz
  rw [hp] at hz
  exact hz

end

open Set Filter Function Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩
theorem annular_orthogonal_transverse_nonzero [PreconnectedSpace (Sphere d)]
    (μ : Measure (Sphere d)) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric (Euclidean d) (Sphere d))
    (a b c : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
    {u v : Sphere d → ℝ}
    (hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ v)
    (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
    (hve : ∀ p, -laplaceBeltrami g v p = ((n:ℝ)*((n:ℝ)+2))*v p)
    (hup : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (hgp : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h →
      ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean d) p),
        g.inner p X Y = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
            (fun q : Sphere d => (q : Euclidean (d+1))) p X)
          (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
            (fun q : Sphere d => (q : Euclidean (d+1))) p Y))
    (hv0 : v ≠ 0) (ho : ∫ q, v q*u q ∂μ = 0) :
    ∃ p : Sphere d, l < Complex.normSq (planarLinear a b p) ∧
      Complex.normSq (planarLinear a b p) < h ∧
      bundleTransverse g u p (metricGradient g v p) ≠ 0 := by
  classical
  by_contra hnone
  apply hv0
  apply proportional_orthogonal_zero μ hv.continuous _ ho
  apply annular_transverse_zero_proportional g a b c ha hb hc hab hac hbc n hn hl hlh hh hu hv hue hve hup hgp
  intro p hpl hph
  by_contra hz
  exact hnone ⟨p,hpl,hph,hz⟩

theorem annular_eigenfunction_separating_tensor [PreconnectedSpace (Sphere d)]
    (μ : Measure (Sphere d)) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (g : SmoothMetric (Euclidean d) (Sphere d))
    (a b c : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
    {u v : Sphere d → ℝ}
    (hu : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ v)
    (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
    (hve : ∀ p, -laplaceBeltrami g v p = ((n:ℝ)*((n:ℝ)+2))*v p)
    (hup : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (hgp : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h →
      ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean d) p),
        g.inner p X Y = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
            (fun q : Sphere d => (q : Euclidean (d+1))) p X)
          (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1))
            (fun q : Sphere d => (q : Euclidean (d+1))) p Y))
    (hv0 : v ≠ 0) (ho : ∫ q, v q*u q ∂μ = 0) (hd : d = 3) :
    ∃ χ : Sphere d → ℝ,
      tsupport χ ⊆ {p | l < Complex.normSq (planarLinear a b p) ∧
        Complex.normSq (planarLinear a b p) < h} ∧
      ContMDiff 𝓘(ℝ,Euclidean d)
        (𝓘(ℝ,Euclidean d).prod 𝓘(ℝ,Euclidean d →L[ℝ] Euclidean d)) ∞
        (fun y => TotalSpace.mk' (Euclidean d →L[ℝ] Euclidean d) y
          (supportedPinningTensor g u v χ y)) ∧
      (∀ y, LinearMap.trace ℝ (TangentSpace 𝓘(ℝ,Euclidean d) y)
        (supportedPinningTensor g u v χ y).toLinearMap = 0) ∧
      (∀ y, supportedPinningTensor g u v χ y (metricGradient g u y) = 0) ∧
      0 < ∫ y, g.inner y (metricGradient g v y)
        (supportedPinningTensor g u v χ y (metricGradient g v y)) ∂μ := by
  obtain ⟨p,hpl,hph,hp⟩ := annular_orthogonal_transverse_nonzero μ g a b c ha hb hc hab hac hbc
    n hn hl hlh hh hu hv hue hve hup hgp hv0 ho
  exact exists_supported_separating_tensor μ g hu hv (round_annulus_open a b l h)
    (fun q hq => annular_gradient_ne_zero g a b ha hb hab n (by omega) hl hh hu hup q hq.1 hq.2)
    ⟨hpl,hph⟩ hp (by simpa [Euclidean] using hd)




end YauCounterexamples
end

end OAI
