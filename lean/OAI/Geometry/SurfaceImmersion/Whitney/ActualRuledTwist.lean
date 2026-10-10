import OAI.Geometry.SurfaceImmersion.Geometry.TwistedTargetTube

namespace OAI

/-! Compactly supported twists inside the actual ruled target tube lift
 to smooth surface maps and preserve the complete singular set. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}
variable {S : CrosscapCoordinateStrip A} {c d : ℝ}

theorem ActualRuledRectangle.twist_family (R : ActualRuledRectangle S c d)
    (hac : A.arc.start < c) (hcd : c ≤ d) (hdb : d < A.arc.finish) :
    ∃ (T : Base × ℝ → Fin 3 → ℝ) (ε : ℝ), ContDiff ℝ ∞ T ∧ 0 < ε ∧
      ∀ θ : Base → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ {x | |x 0| < ε ∧ x 1 ∈ Ioo c d} →
        ∃ (g : M → ProjectionTarget 3) (K : Set M),
          ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧ IsCompact K ∧
          K ⊆ S.chart.source ∧
          (∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x) ↔
            Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) ∧
          (∀ x ∉ K, g =ᶠ[𝓝 x] R.replacement) ∧
          ∀ x ∈ S.chart.source, |S.chart x 0| < ε → S.chart x 1 ∈ Ioo c d →
            g =ᶠ[𝓝 x] (twistedTubeSurface T θ) ∘ S.chart := by
  obtain ⟨T,r,U,hT,hr,hU,hKU,hTI,hTM⟩ := R.target_tube hac hcd hdb
  let ε := min r R.radius
  have hε : 0 < ε := lt_min hr R.radius_pos
  let Ω : Set Base := {x | |x 0| < ε ∧ x 1 ∈ Ioo c d}
  have hΩ : IsOpen Ω := by
    change IsOpen ({x : Base | |x 0| < ε} ∩ ((fun x : Base => x 1) ⁻¹' Ioo c d))
    exact (isOpen_lt (continuous_apply (0 : Fin 2)).abs continuous_const).inter
      (isOpen_Ioo.preimage (continuous_apply 1))
  have hΩD : Ω ⊆ S.domain := by
    intro x hx
    have hx0 : |x 0| ≤ R.radius := (hx.1.trans_le (min_le_right _ _)).le
    have ht : x 1 ∈ Icc (c-R.radius) (d+R.radius) := by
      constructor <;> linarith [hx.2.1,hx.2.2,R.radius_pos]
    have hh := (R.ruled_rectangle (x 0) (abs_le.mp hx0) (x 1) ht).1
    convert hh using 1
    ext i; fin_cases i <;> rfl
  have hbase : ∀ x ∈ Ω, R.model =ᶠ[𝓝 x] twistedTubeSurface T 0 := by
    intro x hx
    filter_upwards [hΩ.mem_nhds hx] with y hy
    have he := hTM (y 0) (hy.1.trans_le (min_le_left _ _)) (y 1) ⟨hy.2.1.le,hy.2.2.le⟩
    have hyid : (![y 0,y 1] : Base) = y := by ext i; fin_cases i <;> rfl
    rw [hyid] at he
    change R.model y = (EuclideanSpace.equiv (Fin 3) ℝ).symm
      (T (twistedRuledCoordinates 0 y))
    rw [twistedRuledCoordinates_zero (show (0 : Base → ℝ) y = 0 from rfl),he]
    exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm_apply_apply _).symm
  have hregular : ∀ θ : Base → ℝ, ContDiff ℝ ∞ θ → ∀ x ∈ Ω,
      Function.Injective (fderiv ℝ (twistedTubeSurface T θ) x) := by
    intro θ hθ x hx
    apply twistedTubeSurface_immersion hT hθ
    apply (hTI (twistedRuledCoordinates θ x).1 ?_ (x 1) (hKU ⟨hx.2.1.le,hx.2.2.le⟩)).1
    exact (twistedRuledCoordinates_bound θ x).trans_lt (hx.1.trans_le (min_le_left _ _))
  refine ⟨T,ε,hT,hε,?_⟩
  intro θ hθ hc hs
  let Q := twistedTubeSurface T θ-twistedTubeSurface T 0
  have hQ : ContDiff ℝ ∞ Q :=
    (twistedTubeSurface_smooth hT hθ).sub (twistedTubeSurface_smooth hT contDiff_const)
  have hQs : tsupport Q ⊆ tsupport θ := twistedTubeSurface_difference_support T θ
  have hQc : HasCompactSupport Q := hc.of_isClosed_subset (isClosed_tsupport Q) hQs
  have he : ∀ x ∈ Ω, R.model+Q =ᶠ[𝓝 x] twistedTubeSurface T θ := by
    intro x hx
    filter_upwards [hbase x hx] with y hy
    change R.model y+(twistedTubeSurface T θ y-twistedTubeSurface T 0 y) = _
    rw [hy]
    abel
  have hrel : ∀ x ∈ tsupport Q, Function.Injective (fderiv ℝ (R.model+Q) x) ↔
      Function.Injective (fderiv ℝ R.model x) := by
    intro x hx
    have hxΩ : x ∈ Ω := hs (hQs hx)
    rw [(he x hxΩ).fderiv_eq,(hbase x hxΩ).fderiv_eq]
    exact iff_of_true (hregular θ hθ x hxΩ) (hregular 0 contDiff_const x hxΩ)
  obtain ⟨g,hg,hreg,hout,hin⟩ := coordinate_regular_replacement S.chart S.chart_smooth
    S.inverse_smooth R.smooth hQ hQc S.domain_open S.domain_target
    (hQs.trans (hs.trans hΩD)) R.model_eq hrel
  let K := S.chart.symm '' tsupport θ
  have hKD : tsupport θ ⊆ S.chart.target := hs.trans (hΩD.trans S.domain_target)
  have hK : IsCompact K := hc.image_of_continuousOn (S.chart.continuousOn_symm.mono hKD)
  refine ⟨g,K,hg,hK,?_,fun x => (hreg x).trans (R.regular_iff x),?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact S.chart.map_target (hKD hy)
  · intro x hx
    apply hout x
    intro hxin
    apply hx
    exact image_mono hQs hxin
  · intro x hx h0 h1
    have hxΩ : S.chart x ∈ Ω := ⟨h0,h1⟩
    exact (hin x hx (hΩD hxΩ)).trans
      (coordinate_replacement_germ S.chart hx (he (S.chart x) hxΩ))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
