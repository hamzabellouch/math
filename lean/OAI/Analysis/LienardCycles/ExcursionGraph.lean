import OAI.Analysis.LienardCycles.IntervalInverse

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open RealAnalysis ScaledProfile AxisFlow

structure IsRightExcursion (z : ℝ → Plane) (s t : ℝ) : Prop where
  lt : s<t
  left : (z s).1=0
  right : (z t).1=0
  positive : ∀ v ∈ Ioo s t,0<(z v).1
lemma IsRightExcursion.y_strictAnti {F : Polynomial ℝ} {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (he : IsRightExcursion z s t) : StrictAntiOn (fun v=>(z v).2) (Icc s t) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc s t) hz.continuous.snd.continuousOn
  intro v hv
  have hv' : v ∈ Ioo s t := by simpa using hv
  rw [(hz.y_deriv v).deriv]
  exact neg_neg_of_pos (he.positive v hv')
lemma IsRightExcursion.y_lt {F : Polynomial ℝ} {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (he : IsRightExcursion z s t) : (z t).2<(z s).2 :=
  he.y_strictAnti hz ⟨le_rfl,he.lt.le⟩ ⟨he.lt.le,le_rfl⟩ he.lt
lemma IsRightExcursion.graph {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (he : IsRightExcursion z s t) :
    ∃ u : ℝ → ℝ, Continuous u ∧ u (z t).2=0 ∧ u (z s).2=0 ∧
      (∀ y ∈ Ioo (z t).2 (z s).2,0<u y ∧ HasDerivAt u (φ a (u y)-y) y) ∧
      (∀ v ∈ Icc s t,u (z v).2=(z v).1^2/2) := by
  have hylt := he.y_lt hz
  have hanti := he.y_strictAnti hz
  have hb : BijOn (fun v=>(z v).2) (Icc s t) (Icc (z t).2 (z s).2) := by
    refine ⟨?_,hanti.injOn,?_⟩
    · intro v hv
      exact ⟨hanti.antitoneOn hv ⟨he.lt.le,le_rfl⟩ hv.2,
        hanti.antitoneOn ⟨le_rfl,he.lt.le⟩ hv hv.1⟩
    · intro y hy
      exact intermediate_value_Icc' he.lt.le hz.continuous.snd.continuousOn hy
  obtain ⟨τ,hτc,hτmem,hτr,hτl⟩ := continuous_interval_inverse hylt.le hz.continuous.snd.continuousOn hb
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
  refine ⟨u,(hz.continuous.fst.comp hτc).pow 2 |>.div_const 2,?_,?_,?_,hu⟩
  · rw [hu t ⟨he.lt.le,le_rfl⟩,he.right];norm_num
  · rw [hu s ⟨le_rfl,he.lt.le⟩,he.left];norm_num
  · intro y hy
    have hx := he.positive (τ y) (hτint y hy)
    have hτd : HasDerivAt τ (-(z (τ y)).1)⁻¹ y :=
      HasDerivAt.of_local_left_inverse hτc.continuousAt (hz.y_deriv (τ y)) (neg_ne_zero.mpr hx.ne')
        ((show ∀ᶠ v in 𝓝 y,v ∈ Ioo (z t).2 (z s).2 from Ioo_mem_nhds hy.1 hy.2).mono fun v hv=>hτr v (Ioo_subset_Icc_self hv))
    refine ⟨div_pos (sq_pos_of_pos hx) (by norm_num),?_⟩
    convert! (((hz.x_deriv (τ y)).pow 2).div_const 2).comp y hτd using 1
    symm
    change (2*(z (τ y)).1^(2-1)*((z (τ y)).2-F.eval (z (τ y)).1)/2)*(-(z (τ y)).1)⁻¹=φ a ((z (τ y)).1^2/2)-y
    rw [AxisFlow.φ_square a hx.le,←hF,hτr y (Ioo_subset_Icc_self hy)]
    field_simp [hx.ne']
    ring
end QuinticLienard

end OAI
