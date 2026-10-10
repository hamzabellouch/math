import OAI.Analysis.LienardCycles.UpperAssembly

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
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile
lemma solution_unique_Icc (F : Polynomial ℝ) {z w : ℝ → Plane} {T : ℝ}
    (hzc : ContinuousOn z (Icc 0 T)) (hwc : ContinuousOn w (Icc 0 T))
    (hz : ∀ t ∈ Icc 0 T,HasDerivAt z (vectorField F (z t)) t)
    (hw : ∀ t ∈ Icc 0 T,HasDerivAt w (vectorField F (w t)) t)
    (he : z 0=w 0) : EqOn z w (Icc 0 T) := by
  obtain ⟨W,K,L,hK,_,hW⟩ := GlobalODE.exists_bounded_lipschitz_cutoff_on (vectorField F)
    ((isCompact_Icc.image_of_continuousOn hzc).union (isCompact_Icc.image_of_continuousOn hwc)) isOpen_univ
    (subset_univ _) ((vectorField_contDiff F).of_le (by simp)).contDiffOn
  apply ODE_solution_unique_of_mem_Icc_right (v:=fun _=>W) (s:=fun _=>(univ : Set Plane))
    (fun _ _=>hK.lipschitzOnWith) hzc _ (fun _ _=>mem_univ _) hwc _ (fun _ _=>mem_univ _) he
  · intro t ht
    rw [(hW (z t) (Or.inl (mem_image_of_mem _ (Ico_subset_Icc_self ht)))).self_of_nhds]
    exact (hz t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  · intro t ht
    rw [(hW (w t) (Or.inr (mem_image_of_mem _ (Ico_subset_Icc_self ht)))).self_of_nhds]
    exact (hw t (Ico_subset_Icc_self ht)).hasDerivWithinAt
lemma IsPeriodicOrbit.positive_axis {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    ∃ b,F.eval 0<b ∧ (0,b) ∈ C ∧ ∀ p ∈ C,p.1=0 → F.eval 0<p.2 → p=(0,b) := by
  obtain ⟨z,S,T,hz,hS,hST,hp,hr,hl,rfl⟩ := hC.oval hF
  refine ⟨(z 0).2,(hr.endpoint_signs hz hr.nonconstant).2,⟨0,Prod.ext hr.left rfl⟩,?_⟩
  intro p hpC hx hy
  exact (hz.oval_axis_positive hS hST hp hr hl hpC hx hy).trans (Prod.ext hr.left rfl)
lemma IsPeriodicOrbit.axis_unique {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsPeriodicOrbit F C)
    {b : ℝ} (hb : F.eval 0<b) (hbp : (0,b) ∈ C)
    {p : Plane} (hp : p ∈ C) (hx : p.1=0) (hy : F.eval 0<p.2) : p=(0,b) := by
  obtain ⟨c,_,_,hu⟩ := hC.positive_axis hF
  exact (hu p hp hx hy).trans (hu (0,b) hbp rfl hb).symm
lemma IsPeriodicOrbit.not_equilibrium {F : Polynomial ℝ} {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    (0,F.eval 0) ∉ C := by
  obtain ⟨z,T,hz,_,_,hn,rfl⟩ := hC
  rintro ⟨t,ht⟩
  exact hz.avoids_equilibrium hn t ht
lemma IsPeriodicOrbit.limitCycle_of_section {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsPeriodicOrbit F C)
    {b : ℝ} (hb : F.eval 0<b) (hbp : (0,b) ∈ C)
    (hi : ∀ᶠ s in 𝓝 b,∀ D : Set Plane,IsPeriodicOrbit F D → (0,s) ∈ D → s=b) : IsLimitCycle F C := by
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hi
  let U : Set Plane := {p | p.1≠0 ∨ p.2<F.eval 0 ∨ |p.2-b|<δ}
  have hU : IsOpen U := (isOpen_ne_fun continuous_fst continuous_const).union
    ((isOpen_lt continuous_snd continuous_const).union (isOpen_lt (continuous_snd.sub continuous_const |>.abs) continuous_const))
  refine ⟨hC,U,hU,?_,?_⟩
  · intro p hp
    by_cases hx : p.1=0
    · by_cases hy : p.2<F.eval 0
      · exact Or.inr (Or.inl hy)
      · have hne : p.2≠F.eval 0 := by
          intro he
          exact hC.not_equilibrium ((show p=(0,F.eval 0) from Prod.ext hx he) ▸ hp)
        have hpos : F.eval 0<p.2 := lt_of_le_of_ne (le_of_not_gt hy) hne.symm
        rw [hC.axis_unique hF hb hbp hp hx hpos]
        exact Or.inr (Or.inr (by simpa using hδ))
    · exact Or.inl hx
  · intro D hD hDU
    obtain ⟨s,hs,hsp,_⟩ := hD.positive_axis hF
    have hDs : (0,s) ∈ U := hDU hsp
    have hnear : |s-b|<δ := by
      rcases hDs with hn|hn|hn
      · exact (hn rfl).elim
      · exact (not_lt_of_ge hs.le hn).elim
      · exact hn
    have he : s=b := hd (by simpa [Metric.mem_ball,Real.dist_eq] using hnear) D hD hsp
    exact hD.eq_of_common hC (he ▸ hsp) hbp
lemma IsPeriodicOrbit.limitCycle_of_return {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {C : Set Plane} (hC : IsPeriodicOrbit F C)
    {b : ℝ} (hb : F.eval 0<b) (hbp : (0,b) ∈ C)
    {g : ℝ → ℝ → Plane} {τ : ℝ → ℝ}
    (hlocal : ∀ᶠ s in 𝓝 b,0<τ s ∧ g s 0=(0,s) ∧
      ContinuousOn (g s) (Icc 0 (τ s)) ∧
      (∀ t ∈ Icc 0 (τ s),HasDerivAt (g s) (vectorField F (g s t)) t) ∧
      (g s (τ s)).1=0 ∧ F.eval 0<(g s (τ s)).2 ∧
      (g s (τ s)=(0,s) → s=b)) : IsLimitCycle F C := by
  apply hC.limitCycle_of_section hF hb hbp
  filter_upwards [hlocal,eventually_gt_nhds hb] with s hs hsb D hD hsD
  obtain ⟨hT,h0,hc,hd,hx,hy,hiso⟩ := hs
  obtain ⟨z,T,hz,hper,hp,hn,rfl⟩ := hD
  obtain ⟨t,ht⟩ := hsD
  have he := solution_unique_Icc F hc (hz.shift t).continuous.continuousOn hd
    (fun u _=>(hz.shift t) u) (by simpa using h0.trans ht.symm)
  have hm : g s (τ s) ∈ range z := ⟨τ s+t,(he ⟨hT.le,le_rfl⟩).symm⟩
  apply hiso
  exact (show IsPeriodicOrbit F (range z) from ⟨z,T,hz,hper,hp,hn,rfl⟩).axis_unique hF
    hsb ⟨t,ht⟩ hm hx hy
end QuinticLienard

end OAI
