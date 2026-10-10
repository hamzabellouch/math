import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ExistsPowerRadius
import OAI.Geometry.SmoothYau.Smoothness.RoundPowerRadius
import OAI.Geometry.SmoothYau.Spectrum.PinningFactorGradient
import OAI.Geometry.SmoothYau.Spectrum.TransverseZeroKernel

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩
lemma exists_annular_rank_point (a b c : Euclidean (d+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 0 < n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1) :
    ∃ p : Sphere d, l < Complex.normSq (planarLinear a b p) ∧
      Complex.normSq (planarLinear a b p) < h ∧ ((planarLinear a b p)^n).im ≠ 0 := by
  let s := (l+h)/2
  have hs : 0 < s := by dsimp [s]; linarith
  obtain ⟨z,hzr,hzn⟩ := exists_power_radius n hn (Real.sqrt_pos.mpr hs)
  have hz : Complex.normSq z = s := by rwa [Real.sq_sqrt hs.le] at hzr
  obtain ⟨p,hp,hpz⟩ := planar_sphere_point a b c ha hb hc hab hac hbc z
    (by rw [hz]; dsimp [s]; linarith)
  let q : Sphere d := ⟨p,by simpa only [Metric.mem_sphere,dist_zero_right] using hp⟩
  refine ⟨q,?_,?_,?_⟩
  · change l < Complex.normSq (planarLinear a b p)
    rw [hpz,hz]; dsimp [s]; linarith
  · change Complex.normSq (planarLinear a b p) < h
    rw [hpz,hz]; dsimp [s]; linarith
  · change ((planarLinear a b p)^n).im ≠ 0
    rwa [hpz]
lemma sphere_chart_symm_continuous_general (p : Sphere d) : Continuous (chartAt (Euclidean d) p).symm := by
  rw [←continuousOn_univ]
  simpa only [sphere_chart_target] using (chartAt (Euclidean d) p).continuousOn_symm
lemma round_annulus_open (a b : Euclidean (d+1)) (l h : ℝ) :
    IsOpen {p : Sphere d | l < Complex.normSq (planarLinear a b p) ∧
      Complex.normSq (planarLinear a b p) < h} := by
  have hc : Continuous (fun p : Sphere d => Complex.normSq (planarLinear a b p)) :=
    Complex.continuous_normSq.comp ((planarLinear a b).continuous.comp continuous_subtype_val)
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
lemma round_pair_rank_transfer (a b : Euclidean (d+1)) (n : ℕ) (hn : 1 ≤ n)
    (p : Sphere d) (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hr : Complex.normSq (planarLinear a b p) < 1)
    (hi : ((planarLinear a b p)^n).im ≠ 0) {H : Euclidean d → ℝ × ℝ}
    (he : H =ᶠ[𝓝 0] (roundPowerRadius a b n ∘ (chartAt (Euclidean d) p).symm)) :
    ContDiffAt ℝ 1 H 0 ∧ Function.Surjective (fderiv ℝ H 0) := by
  constructor
  · exact (((roundPowerRadius_chart_contDiff a b n p).of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))).contDiffAt.congr_of_eventuallyEq he)
  · rw [he.fderiv_eq]
    exact roundPowerRadius_chart_surjective a b n p ha hb hab hn hr hi


end

open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
section LocalPair
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma coordinateGradientPair_congr_nhds (g : SmoothMetric E M) {u v : M → ℝ} {x : M}
    (he : u =ᶠ[𝓝 x] v) : coordinateGradientPair g u u x = coordinateGradientPair g v v x := by
  let c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source _ _)
  have ht : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    simpa only [c.left_inv (mem_chart_source _ _)] using (c.continuousAt_symm hx).tendsto
  have hd : fderiv ℝ (u ∘ c.symm) (c x) = fderiv ℝ (v ∘ c.symm) (c x) :=
    (he.comp_tendsto ht).fderiv_eq
  dsimp only [c] at hd
  simp only [coordinateGradientPair,hd]
end LocalPair
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

theorem annular_transverse_zero_proportional [PreconnectedSpace (Sphere d)]
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
    (hzero : ∀ p : Sphere d, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → bundleTransverse g u p (metricGradient g v p) = 0) :
    ∃ t : ℝ, v = fun p => t*u p := by
  let A := {p : Sphere d | l < Complex.normSq (planarLinear a b p) ∧
    Complex.normSq (planarLinear a b p) < h}
  have hAo : IsOpen A := round_annulus_open a b l h
  obtain ⟨p,hpl,hph,hpn⟩ := exists_annular_rank_point a b c ha hb hc hab hac hbc n (by omega) hl hlh hh
  let chart := chartAt (Euclidean d) p
  have hsym : chart.symm 0 = p := by
    change (chartAt (Euclidean d) p).symm 0 = p
    simpa only [sphere_chart_center] using (chartAt (Euclidean d) p).left_inv (mem_chart_source _ p)
  let U := chart.symm ⁻¹' A
  have hU : IsOpen U := hAo.preimage (sphere_chart_symm_continuous_general p)
  have hx : (0 : Euclidean d) ∈ U := by change chart.symm 0 ∈ A; rw [hsym]; exact ⟨hpl,hph⟩
  have hUt : U ⊆ chart.target := by rw [sphere_chart_target]; exact subset_univ _
  have hgerm (q : Sphere d) (hq : q ∈ A) : u =ᶠ[𝓝 q] roundPower a b n := by
    filter_upwards [hAo.mem_nhds hq] with z hz
    exact hup z hz.1 hz.2
  have hchart : (u ∘ chart.symm) =ᶠ[𝓝 (0 : Euclidean d)] (roundPower a b n ∘ chart.symm) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hup _ hy.1 hy.2
  let R := fun q : Sphere d => Complex.normSq (planarLinear a b q)
  let H := fun y : Euclidean d => (u (chart.symm y),R (chart.symm y))
  have hH : H =ᶠ[𝓝 0] (roundPowerRadius a b n ∘ chart.symm) := by
    filter_upwards [hchart] with y hy
    change (u (chart.symm y),R (chart.symm y)) =
      (((planarLinear a b (chart.symm y))^n).re,Complex.normSq (planarLinear a b (chart.symm y)))
    exact Prod.ext hy rfl
  have hdu : fderiv ℝ (u ∘ chart.symm) 0 ≠ 0 := by
    rw [hchart.fderiv_eq]
    exact roundPower_annulus_noncritical a b n (by omega) ha hb hab p (hl.trans hpl) (hph.trans hh)
  have hquad (y : Euclidean d) (hy : y ∈ U) :
      coordinateGradientPair g u u (chart.symm y) =
        (n:ℝ)^2 * ((R (chart.symm y))^(n-1) - (u (chart.symm y))^2) := by
    rw [coordinateGradientPair_congr_nhds g (hgerm _ hy),
      roundPower_coordinateGradientPair g _ (hgp _ hy.1 hy.2) a b n (by omega) ha hb hab,
      hup _ hy.1 hy.2]
  have hpr : ContDiffAt ℝ 1 H 0 ∧ Function.Surjective (fderiv ℝ H 0) :=
    round_pair_rank_transfer a b n (by omega) p ha hb hab (hph.trans hh) hpn hH
  obtain ⟨t,ht⟩ := local_eigen_proportional_of_annular_rank g (u := u) (v := v) (R := R) p (U := U) (x := 0) hU hx hUt
    (hu.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) (hv.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hdu
    (fun y hy => transverse_zero_chart_kernel g hu hv p (hUt hy) (hzero _ hy.1 hy.2))
    hpr.1 hpr.2
    (by change 0 < R (chart.symm 0); rw [hsym]; exact hl.trans hpl) hn
    (fun y _ => by linarith [hue (chart.symm y)])
    (fun y _ => by linarith [hve (chart.symm y)]) hquad
  exact ⟨t,proportional_eigen_global g hu hv _ t hue hve ⟨chart.symm 0,ht⟩⟩



end YauCounterexamples
end

end OAI
