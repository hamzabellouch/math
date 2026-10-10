import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.GaussLemma

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance normalCoordinatesNormedSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance normalCoordinatesDualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance normalCoordinatesDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance normalCoordinatesBilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance normalCoordinatesBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance normalCoordinatesTrilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance normalCoordinatesTrilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

lemma coordinate_endpoint_isInvertible
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {Ψ W : ℝ × E → E} {a b R : ℝ} (hR : 0 < R)
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo a b ×ˢ Metric.ball 0 R))
    (hW : ContDiffOn ℝ ∞ W (Ioo a b ×ˢ Metric.ball 0 R))
    (himg : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {x : E} (h0 : 0 ∈ Ioo a b)
    (hΨ0 : ∀ v ∈ Metric.ball 0 R, Ψ (0,v) = x)
    (hW0 : ∀ v ∈ Metric.ball 0 R, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo a b) (hτne : τ ≠ 0) :
    (fderiv ℝ (fun v => Ψ (τ,v)) 0).IsInvertible := by
  have hz : (0:E) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  have hx : x ∈ S := hΨ0 0 hz ▸ himg 0 h0 0 hz
  have hi : ∀ y ∈ S, (g y).IsInvertible :=
    fun y hy => metricDual_isInvertible (g y) (hpos y hy)
  have hgd : ∀ t ∈ Ioo a b, ∀ v ∈ Metric.ball 0 R,
      DifferentiableAt ℝ g (Ψ (t,v)) := fun t ht v hv =>
    (hg.contDiffAt (hS.mem_nhds (himg t ht v hv))).differentiableAt (by simp)
  have hWτ0 : W (τ,0) = 0 := by
    have he := coordinate_geodesic_speed_constant
      (fun t ht => hgd t ht 0 hz) (fun t ht => hi _ (himg t ht 0 hz))
      (fun t ht => hsym _ (himg t ht 0 hz)) (fun t ht => hode t ht 0 hz) hτ h0
    simp only [hΨ0 0 hz,hW0 0 hz,map_zero] at he
    by_contra hn
    exact (ne_of_gt (hpos _ (himg τ hτ 0 hz) _ hn)) he
  have hopen : IsOpen (Ioo a b ×ˢ Metric.ball (0:E) R) :=
    isOpen_Ioo.prod Metric.isOpen_ball
  have hψ : ContDiffAt ℝ ∞ (fun v => Ψ (τ,v)) 0 :=
    (hΨ.contDiffAt (hopen.mem_nhds ⟨hτ,hz⟩)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)
  let L := fderiv ℝ (fun v => Ψ (τ,v)) 0
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro w hw
    let δ := R / (‖w‖+1)
    have hd : 0 < δ := div_pos hR (by positivity)
    have hsw : ∀ s ∈ Ioo (-δ) δ, s • w ∈ Metric.ball 0 R := by
      intro s hs
      rw [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs]
      have hsa := abs_lt.mpr hs
      have hmul : |s| * (‖w‖+1) < R := (lt_div_iff₀ (by positivity)).mp hsa
      nlinarith [abs_nonneg s]
    let A : ℝ × ℝ → E := fun z => Ψ (z.1,z.2 • w)
    let V : ℝ × ℝ → E := fun z => W (z.1,z.2 • w)
    have hA : ContDiffOn ℝ ∞ A (Ioo a b ×ˢ Ioo (-δ) δ) :=
      hΨ.comp (contDiffOn_fst.prodMk (contDiffOn_snd.smul contDiffOn_const))
        (fun z hz => ⟨hz.1,hsw z.2 hz.2⟩)
    have hV : ContDiffOn ℝ ∞ V (Ioo a b ×ˢ Ioo (-δ) δ) :=
      hW.comp (contDiffOn_fst.prodMk (contDiffOn_snd.smul contDiffOn_const))
        (fun z hz => ⟨hz.1,hsw z.2 hz.2⟩)
    have hs0 : (0:ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hd,hd⟩
    have hrect : IsOpen (Ioo a b ×ˢ Ioo (-δ) δ) := isOpen_Ioo.prod isOpen_Ioo
    have hAat : ContDiffAt ℝ ∞ A (τ,0) := hA.contDiffAt (hrect.mem_nhds ⟨hτ,hs0⟩)
    have hVat : ContDiffAt ℝ ∞ V (τ,0) := hV.contDiffAt (hrect.mem_nhds ⟨hτ,hs0⟩)
    have hJat := contDiffAt_directionalDerivative hAat (0,1)
    have hAr := hasDerivAt_slice_right (hAat.differentiableAt (by simp))
    have hVr := hasDerivAt_slice_right (hVat.differentiableAt (by simp))
    have hJr := hasDerivAt_slice_right (hJat.differentiableAt (by simp))
    have hswder : HasDerivAt (fun s : ℝ => s • w) w 0 := by
      convert (hasDerivAt_id (0:ℝ)).smul_const w using 1 <;> first | rfl | simp only [one_smul]
    have hψder := (show HasFDerivAt (fun v => Ψ (τ,v)) L ((0:ℝ) • w) by
      simpa only [zero_smul] using (hψ.differentiableAt (by simp)).hasFDerivAt
      ).comp_hasDerivAt 0 hswder
    have hJ0 : directionalDerivative A (0,1) (τ,0) = 0 := by
      have he : directionalDerivative A (0,1) (τ,0) = L w := hAr.unique hψder
      exact he.trans hw
    have hV0' : V (τ,0) = 0 := by simpa only [V,zero_smul] using hWτ0
    have hgdA : DifferentiableAt ℝ g (A (τ,0)) := by
      simpa only [A,zero_smul] using hgd τ hτ 0 hz
    have hAg : HasDerivAt (fun s => g (A (τ,s)))
        ((fderiv ℝ g (A (τ,0))) (directionalDerivative A (0,1) (τ,0))) 0 :=
      hgdA.hasFDerivAt.comp_hasDerivAt 0 hAr
    have hH := (hAg.clm_apply hVr).clm_apply hJr
    have hH0 : HasDerivAt (fun s => g (A (τ,s)) (V (τ,s))
        (directionalDerivative A (0,1) (τ,s))) 0 0 := by
      convert hH using 1
      simp only [hJ0,hV0',map_zero,zero_apply,add_zero,zero_add]
    have hHeq : (fun s => g (A (τ,s)) (V (τ,s))
        (directionalDerivative A (0,1) (τ,s))) =ᶠ[𝓝 0]
          (fun s => (τ * g x w w) * s) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs0] with s hs
      have hν : HasDerivAt (fun s : ℝ => s • w) w s := by
        convert (hasDerivAt_id s).smul_const w using 1 <;> first | rfl | simp only [one_smul]
      have hG := coordinate_gauss_variation hS hg hi hsym hA hV
        (fun t ht r hr => himg t ht (r • w) (hsw r hr))
        (fun t ht r hr => hode t ht (r • w) (hsw r hr))
        h0 (fun r hr => hΨ0 (r • w) (hsw r hr))
        (fun r hr => hW0 (r • w) (hsw r hr)) hτ hs hν
      dsimp only [A,V] at hG ⊢
      rw [hG]
      simp only [map_smul,smul_apply,smul_eq_mul]
      ring
    have hderRight : HasDerivAt (fun s => (τ * g x w w) * s) (τ * g x w w) 0 := by
      convert (hasDerivAt_id (0:ℝ)).const_mul (τ * g x w w) using 1 <;> first | rfl | simp only [mul_one]
    have he := (hH0.congr_of_eventuallyEq hHeq.symm).unique hderRight
    have hgww : g x w w = 0 := (mul_eq_zero.mp he.symm).resolve_left hτne
    by_contra hn
    exact (ne_of_gt (hpos x hx w hn)) hgww
  have hsur : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsur),rfl⟩

end WeakMTWTransport

end

end OAI
