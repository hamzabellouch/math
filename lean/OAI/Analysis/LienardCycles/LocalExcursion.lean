import OAI.Analysis.LienardCycles.ReturnNeighborhood

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open RealAnalysis ScaledProfile ScalarArcs AxisFlow
lemma IsRightExcursion.graph_on {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} {s t : ℝ}
    (hc : Continuous z) (hz : ∀ v ∈ Icc s t, HasDerivAt z (vectorField F (z v)) v) (he : IsRightExcursion z s t) :
    ∃ u : ℝ → ℝ, Continuous u ∧ u (z t).2=0 ∧ u (z s).2=0 ∧
      (∀ y ∈ Ioo (z t).2 (z s).2,0<u y ∧ HasDerivAt u (φ a (u y)-y) y) ∧
      (∀ v ∈ Icc s t,u (z v).2=(z v).1^2/2) := by
  have hxd (v : ℝ) (hv : v ∈ Icc s t) : HasDerivAt (fun w=>(z w).1) ((z v).2-F.eval (z v).1) v := by
    simpa [vectorField] using! (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt v (hz v hv)
  have hyd (v : ℝ) (hv : v ∈ Icc s t) : HasDerivAt (fun w=>(z w).2) (-(z v).1) v := by
    simpa [vectorField] using! (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt v (hz v hv)
  have hanti : StrictAntiOn (fun v=>(z v).2) (Icc s t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s t) hc.snd.continuousOn
    intro v hv
    rw [(hyd v (interior_subset hv)).deriv]
    exact neg_neg_of_pos (he.positive v (by simpa using hv))
  have hylt := hanti ⟨le_rfl,he.lt.le⟩ ⟨he.lt.le,le_rfl⟩ he.lt
  have hb : BijOn (fun v=>(z v).2) (Icc s t) (Icc (z t).2 (z s).2) := by
    refine ⟨?_,hanti.injOn,?_⟩
    · intro v hv
      exact ⟨hanti.antitoneOn hv ⟨he.lt.le,le_rfl⟩ hv.2,
        hanti.antitoneOn ⟨le_rfl,he.lt.le⟩ hv hv.1⟩
    · intro y hy
      exact intermediate_value_Icc' he.lt.le hc.snd.continuousOn hy
  obtain ⟨τ,hτc,hτmem,hτr,hτl⟩ := continuous_interval_inverse hylt.le hc.snd.continuousOn hb
  have hτint (y : ℝ) (hy : y ∈ Ioo (z t).2 (z s).2) : τ y ∈ Ioo s t := by
    have hm := hτmem y
    refine ⟨lt_of_le_of_ne hm.1 ?_,lt_of_le_of_ne hm.2 ?_⟩
    · intro hn
      have hh := hτr y (Ioo_subset_Icc_self hy)
      rw [←hn] at hh
      exact hy.2.ne hh.symm
    · intro hn
      have hh := hτr y (Ioo_subset_Icc_self hy)
      rw [hn] at hh
      exact hy.1.ne hh
  let u : ℝ → ℝ := fun y=>(z (τ y)).1^2/2
  have hu : ∀ v ∈ Icc s t,u (z v).2=(z v).1^2/2 := fun v hv=>by dsimp [u];rw [hτl v hv]
  refine ⟨u,(hc.fst.comp hτc).pow 2 |>.div_const 2,?_,?_,?_,hu⟩
  · rw [hu t ⟨he.lt.le,le_rfl⟩,he.right];norm_num
  · rw [hu s ⟨le_rfl,he.lt.le⟩,he.left];norm_num
  · intro y hy
    have hx := he.positive (τ y) (hτint y hy)
    have hτd : HasDerivAt τ (-(z (τ y)).1)⁻¹ y :=
      HasDerivAt.of_local_left_inverse hτc.continuousAt (hyd (τ y) (Ioo_subset_Icc_self (hτint y hy))) (neg_ne_zero.mpr hx.ne')
        ((show ∀ᶠ v in 𝓝 y,v ∈ Ioo (z t).2 (z s).2 from Ioo_mem_nhds hy.1 hy.2).mono fun v hv=>hτr v (Ioo_subset_Icc_self hv))
    refine ⟨div_pos (sq_pos_of_pos hx) (by norm_num),?_⟩
    convert! (((hxd (τ y) (Ioo_subset_Icc_self (hτint y hy))).pow 2).div_const 2).comp y hτd using 1
    symm
    change (2*(z (τ y)).1^(2-1)*((z (τ y)).2-F.eval (z (τ y)).1)/2)*(-(z (τ y)).1)⁻¹=φ a ((z (τ y)).1^2/2)-y
    rw [AxisFlow.φ_square a hx.le,←hF,hτr y (Ioo_subset_Icc_self hy)]
    field_simp [hx.ne']
    ring
lemma IsRightExcursion.axis_peak_on {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} {s t : ℝ}
    (hc : Continuous z) (hz : ∀ v ∈ Icc s t, HasDerivAt z (vectorField F (z v)) v)
    (hl : (z t).2<F.eval 0) (hr : F.eval 0<(z s).2) (he : IsRightExcursion z s t) :
    ∃ H ∈ transversePeaks a,axisEndpoint a false H=(z t).2 ∧ axisEndpoint a true H=(z s).2 := by
  obtain ⟨u,huc,hul,hur,hud,_⟩ := he.graph_on hF hc hz
  have hylt : (z t).2<(z s).2 := hl.trans hr
  have hu : IsOpenArch (φ a) u (z t).2 (z s).2 :=
    ⟨hylt,huc,hul,hur,fun y hy=>(hud y hy).1,fun y hy=>(hud y hy).2⟩
  obtain ⟨H,hH,hp,hpeak,_⟩ := hu.peak_exists
  obtain ⟨hlo,hro⟩ := hu.axis_endpoints (φ_smooth a) (φ_continuous a).continuousOn hH hp hpeak
  refine ⟨H,⟨hH,?_,?_⟩,hlo,hro⟩
  · change axisLower (φ a) H<poly a 0
    rw [hlo,←hF]
    exact hl
  · change poly a 0<axisUpper (φ a) H
    rw [hro,←hF]
    exact hr
end QuinticLienard

end OAI
