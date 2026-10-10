import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ThreeCoupledCleanChartJets

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples

theorem exists_spherical_radial_cutoff {a b : ℝ} (hab : a < b) :
    ∃ χ : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ χ ∧
      (∀ q, χ q ∈ Icc (0:ℝ) 1) ∧
      (∀ q, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ a → χ q=1) ∧
      (∀ q, b ≤ sphericalRadius sourceAxisOne sourceAxisTwo q → χ q=0) := by
  let f := sphericalRadius sourceAxisOne sourceAxisTwo
  have hf : Continuous f := sphericalRadius_continuous _ _
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,Euclidean 3)) (n := (⊤ : ℕ∞))
    (s := {q : Sphere 3 | f q ≤ a}) (t := {q : Sphere 3 | f q < b})
    (isClosed_le hf continuous_const) (by
      rw [(isOpen_lt hf continuous_const).interior_eq]
      exact fun q hq => lt_of_le_of_lt hq hab)
  exact ⟨χ,χ.contMDiff,hχrange,fun q hq => hχ1.self_of_nhdsSet q hq,
    fun q hq => hχ0 q (not_lt.mpr hq)⟩

theorem spherical_wave_residual_support
    (g g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {F : Set (Sphere 3)} (hF : IsClosed F) {r : ℝ}
    (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    {u : Euclidean 3 → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r})
    {n : ℕ} (hn : 2 ≤ n) :
    tsupport (fun q => laplaceBeltrami g
      (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
      sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ⊆
      {q | sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r} := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hb := roundPower_residual_tsupport g g₀ hg₀ hF hext
    sourceAxisOne sourceAxisTwo n hn source_axes_orthonormal.1
    source_axes_orthonormal.2.1 source_axes_orthonormal.2.2
  have he : (fun q => laplaceBeltrami g (roundPower sourceAxisOne sourceAxisTwo n) q+
      (n:ℝ)*((n:ℝ)+(3:ℝ)-1)*roundPower sourceAxisOne sourceAxisTwo n q)=
      (fun q => laplaceBeltrami g (roundPower sourceAxisOne sourceAxisTwo n) q+
        sphereFrequency n*roundPower sourceAxisOne sourceAxisTwo n q) := by
    funext q; unfold sphereFrequency; ring
  simp only [Nat.cast_ofNat] at hb
  rw [he] at hb
  have hadd : (fun q => laplaceBeltrami g
      (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
      sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)=
      (fun q => laplaceBeltrami g (roundPower sourceAxisOne sourceAxisTwo n) q+
        sphereFrequency n*roundPower sourceAxisOne sourceAxisTwo n q)+
      (fun q => laplaceBeltrami g (sphericalWaveLift u) q+
        sphereFrequency n*sphericalWaveLift u q) := by
    funext q
    simp only [Pi.add_apply]
    change laplaceBeltrami g (fun y => roundPower sourceAxisOne sourceAxisTwo n y+sphericalWaveLift u y) q+_=_
    rw [laplaceBeltrami_add ((roundPower_smooth _ _ _).of_le h2)
      ((sphericalWaveLift_smooth hu hc).of_le h2) g]
    ring
  rw [hadd]
  apply (tsupport_add _ _).trans
  apply union_subset (hb.trans hFr)
  exact (laplaceResidual_tsupport g _ _).trans
    ((sphericalWaveLift_tsupport hc hs).trans (fun q hq => (show sphericalRadius sourceAxisOne sourceAxisTwo q < r from hq).le))

lemma spherical_wave_exterior_germ {u : Euclidean 3 → ℝ} (hc : HasCompactSupport u)
    {r : ℝ} (hs : tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r})
    (n : ℕ) {q : Sphere 3} (hq : r ≤ sphericalRadius sourceAxisOne sourceAxisTwo q) :
    (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) =ᶠ[𝓝 q]
      roundPower sourceAxisOne sourceAxisTwo n := by
  have hz : q ∉ tsupport (sphericalWaveLift u) := fun hq' =>
    (not_lt_of_ge hq) (sphericalWaveLift_tsupport hc hs hq')
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with x hx
  simp only [Pi.add_apply,hx,Pi.zero_apply,add_zero]

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma coordinateGradientPair_pos_derivative_ne (g : SmoothMetric E M) (u : M → ℝ)
    (x : M) (hp : 0 < coordinateGradientPair g u u x) :
    fderiv ℝ (u ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0 := by
  intro hz
  simp [coordinateGradientPair,hz] at hp

lemma regular_quotient_at_zero (g : SmoothMetric E M) {u w : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w)
    (hw0 : ∀ x, w x ≠ 0) (x : M) (hxu : u x=0)
    (hp : 0 < coordinateGradientPair g u u x) :
    fderiv ℝ ((fun q => u q/w q) ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0 := by
  let c := chartAt E x
  have hxt : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hc : c.symm (c x)=x := c.left_inv (mem_chart_source E x)
  have hdu := (contDiffAt_inChart hu x hxt).differentiableAt (by simp)
  have hdw := (contDiffAt_inChart hw x hxt).differentiableAt (by simp)
  have hne : (w ∘ c.symm) (c x) ≠ 0 := by
    simpa only [Function.comp_apply,hc] using hw0 x
  have he := fderiv_fun_mul hdu (hdw.inv hne)
  change fderiv ℝ (fun y => (u ∘ c.symm) y/(w ∘ c.symm) y) (c x) ≠ 0
  simp only [div_eq_mul_inv]
  have he' : fderiv ℝ (fun y => (u ∘ c.symm) y*((w ∘ c.symm) y)⁻¹) (c x) =
      (u ∘ c.symm) (c x) • fderiv ℝ (w ∘ c.symm)⁻¹ (c x)+
      ((w ∘ c.symm) (c x))⁻¹ • fderiv ℝ (u ∘ c.symm) (c x) := he
  rw [he']
  simp only [Function.comp_apply,hc,hxu,zero_smul,zero_add]
  exact smul_ne_zero (inv_ne_zero (hw0 x)) (coordinateGradientPair_pos_derivative_ne g u x hp)

end YauCounterexamples
end

end OAI
