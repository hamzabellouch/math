import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.NormalCoordinates2
import OAI.Analysis.BiholderTransport.Volume.RadialCalibration

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

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]

omit [IsManifold I 1 M] in
lemma short_riemannian_path_mapsTo_ball {x : M} {γ : ℝ → M} {δ : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ (Icc 0 1)) (hγ0 : γ 0 = x)
    (hlen : pathELength I γ 0 1 < ENNReal.ofReal δ) :
    MapsTo γ (Icc 0 1) (Metric.ball x δ) := by
  intro t ht
  have hpre := riemannianEDist_le_pathELength (I := I)
    (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγ0 rfl ht.1
  rw [←IsRiemannianManifold.out,edist_dist] at hpre
  have hpm := pathELength_mono (I := I) (γ := γ) (a := 0) (a' := 0) (b := t)
    (b' := 1) le_rfl ht.2
  have hd := (hpre.trans hpm).trans_lt hlen
  rw [Metric.mem_ball,dist_comm]
  exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.mp (zero_le.trans_lt hlen))).mp hd

omit [IsManifold I 1 M] in
lemma riemannian_local_dist_lower_bound {S : Set M} {x y : M} {δ C : ℝ}
    (hball : Metric.ball x δ ⊆ S) (hdist : dist x y < δ)
    (hpath : ∀ γ : ℝ → M, ContMDiffOn 𝓘(ℝ,ℝ) I 1 γ (Icc 0 1) →
      γ 0 = x → γ 1 = y → MapsTo γ (Icc 0 1) S →
      ENNReal.ofReal C ≤ pathELength I γ 0 1) :
    C ≤ dist x y := by
  by_contra hn
  have hlt : dist x y < min C δ := lt_min (lt_of_not_ge hn) hdist
  have hriem : riemannianEDist I x y < ENNReal.ofReal (min C δ) := by
    rw [←IsRiemannianManifold.out,edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (dist_nonneg.trans_lt hlt)).mpr hlt
  obtain ⟨γ,hγ0,hγ1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hriem
  have hlenδ := hlen.trans_le (ENNReal.ofReal_le_ofReal (min_le_right C δ))
  have himg := (short_riemannian_path_mapsTo_ball hγ hγ0 hlenδ).mono_right hball
  have hh := hpath γ hγ hγ0 hγ1 himg
  exact (not_lt_of_ge hh) (hlen.trans_le (ENNReal.ofReal_le_ofReal (min_le_left C δ)))

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coordinate_normal_chart_radial_bound
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {Ψ W : ℝ × E → E} {r : ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (hW : ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (himg : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {x : E} (h0 : 0 ∈ Ioo (-r) r)
    (hΨ0 : ∀ v ∈ Metric.ball 0 r, Ψ (0,v) = x)
    (hW0 : ∀ v ∈ Metric.ball 0 r, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo (-r) r) (hτnonneg : 0 ≤ τ)
    (e : OpenPartialHomeomorph E E) (hef : (e : E → E) = fun v => Ψ (τ,v))
    (hes : 0 ∈ e.source) (hesub : e.source ⊆ Metric.ball 0 r)
    (hed : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hγimg : MapsTo γ (Icc a b) e.target)
    (hγa : γ a = e 0) :
    ENNReal.ofReal (τ * Real.sqrt (g x (e.symm (γ b)) (e.symm (γ b)))) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (g (γ t) (deriv γ t) (deriv γ t))) := by
  have hef_apply : ∀ v, Ψ (τ,v) = e v := fun v => congrFun hef.symm v
  have hi : ∀ y ∈ S, (g y).IsInvertible := fun y hy => metricDual_isInvertible (g y) (hpos y hy)
  have hx : x ∈ S := by
    rw [←hΨ0 0 (hesub hes)]
    exact himg 0 h0 0 (hesub hes)
  have het : ∀ y ∈ e.target, y ∈ S := by
    intro y hy
    have hyv := hesub (e.map_target hy)
    have hh := himg τ hτ (e.symm y) hyv
    rw [hef_apply,e.right_inv hy] at hh
    exact hh
  apply normal_chart_radial_path_bound e (hed.of_le (by simp)) (hei.of_le (by simp)) hes
    (g x) (positive_bilinear_nonneg _ (hpos x hx)) (hsym x hx) g
    (fun y hy => hpos y (het y hy)) (fun y hy => hsym y (het y hy))
    (fun y => W (τ,e.symm y)) hτnonneg ?_ ?_ hab hγ hγimg hγa
  · intro y hy
    have hv := hesub (e.map_target hy)
    have heq : Ψ (τ,e.symm y) = y := by rw [hef_apply,e.right_inv hy]
    have hc := coordinate_geodesic_speed_constant
      (fun t ht => (hg.contDiffAt (hS.mem_nhds (himg t ht (e.symm y) hv))).differentiableAt (by simp))
      (fun t ht => hi _ (himg t ht _ hv))
      (fun t ht => hsym _ (himg t ht _ hv))
      (fun t ht => hode t ht _ hv) hτ h0
    simpa only [heq,hΨ0 _ hv,hW0 _ hv] using hc
  · intro y hy w
    have hv := hesub (e.map_target hy)
    have hh := coordinate_endpoint_gauss hS hg hi hsym hΨ hW himg hode
      h0 hΨ0 hW0 hτ hv w
    rw [hef_apply,e.right_inv hy,←hef] at hh
    exact hh

end WeakMTWTransport

end

end OAI
