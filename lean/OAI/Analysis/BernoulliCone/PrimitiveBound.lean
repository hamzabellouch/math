import OAI.Analysis.BernoulliCone.ClampedGraphBound

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

lemma cap_extension_eventually_eq {K:Set (Space 7×ℝ)} {B:Space 7×ℝ→Space 7}
    (hB:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p)
    {p:Space 7×ℝ} (hp:p∈interior K) (hq:0<Cylindrical.radiusSq axis p.1)
    (hs:seamHeight p.1<p.2) : B =ᶠ[𝓝 p] upperFlux := by
  have hn:∀ᶠ z:Space 7×ℝ in 𝓝 p,seamHeight z.1<z.2:=
    ((seamHeight_contDiffAt hq).continuousAt.comp continuous_fst.continuousAt).eventually_lt
      continuous_snd.continuousAt hs
  filter_upwards [mem_interior_iff_mem_nhds.mp hp,hn] with z hz hzs
  exact hB z hz hzs.le

lemma clamped_interior_seam {u v:Space 7→ℝ} {x:Space 7}
    (huw:u x<clampedHeight u seamHeight v x)
    (hwv:clampedHeight u seamHeight v x<v x) :
    u x<seamHeight x ∧ seamHeight x<v x ∧ clampedHeight u seamHeight v x=seamHeight x := by
  have hs:seamHeight x<v x:=by
    by_contra hn
    have he:clampedHeight u seamHeight v x=max (u x) (v x):=by
      rw [clampedHeight,min_eq_left (not_lt.mp hn)]
    have hh:=le_max_right (u x) (v x)
    rw [←he] at hh
    exact not_lt.mpr hh hwv
  have he:clampedHeight u seamHeight v x=max (u x) (seamHeight x):=by
    rw [clampedHeight,min_eq_right hs.le]
  have hu:u x<seamHeight x:=by
    rw [he] at huw
    exact (lt_max_iff.mp huw).resolve_left (lt_irrefl _)
  exact ⟨hu,hs,by rw [he,max_eq_right hu.le]⟩

lemma clamped_seam_gradient {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (hq:0<Cylindrical.radiusSq axis x)
    (huw:u x<clampedHeight u seamHeight v x)
    (hwv:clampedHeight u seamHeight v x<v x) :
    gradient (clampedHeight u seamHeight v) x=gradient seamHeight x := by
  obtain ⟨h1,h2,h3⟩:=clamped_interior_seam huw hwv
  have hc:ContinuousAt seamHeight x:=(seamHeight_contDiffAt hq).continuousAt
  have he:clampedHeight u seamHeight v =ᶠ[𝓝 x] seamHeight:=by
    filter_upwards [hu.eventually_lt hc h1,hc.eventually_lt hv h2] with y hy1 hy2
    rw [clampedHeight,min_eq_right hy2.le,max_eq_right hy1.le]
  unfold gradient
  rw [he.fderiv_eq]

lemma primitive_eq_split_germ {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (huv:∀y,u y≤v y)
    {K:Set (Space 7×ℝ)} (hKi:({x}×ˢ Icc (u x) (v x))⊆interior K)
    (hKp:∀p∈K,U p.1<p.2) (hKq:∀p∈K,0<Cylindrical.radiusSq axis p.1)
    {A B:Space 7×ℝ→Space 7} (hA:Continuous A) (hB:Continuous B)
    (hAe:EqOn A exteriorFlux K) (hBe:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p) :
    verticalPotential upperFlux u v =ᶠ[𝓝 x]
      splitGraphPotential A B u (clampedHeight u seamHeight v) v := by
  have hn:=eventually_vertical_segment hu hv (huv x) (subset_interior_iff_mem_nhdsSet.mp hKi)
  filter_upwards [hn] with y hy
  apply clamped_integral_identity hA hB (huv y) (upperFlux_intervalIntegrable y)
  · intro t ht hts
    have hp:(y,t)∈K:=hy (huv y) t ⟨ht.1.le,ht.2.le⟩
    rw [hAe hp,upperFlux_eq_exterior (hKp _ hp) (hKq _ hp) hts]
  · intro t ht hst
    have hp:(y,t)∈K:=hy (huv y) t ⟨ht.1.le,ht.2.le⟩
    exact (hBe _ hp hst.le).symm

lemma exterior_extension_bulk {K:Set (Space 7×ℝ)} {A:Space 7×ℝ→Space 7}
    (hAe:EqOn A exteriorFlux K) {p:Space 7×ℝ} (hp:p∈interior K)
    (hu:U p.1<p.2) (hq:0<Cylindrical.radiusSq axis p.1) (hs:p.2<seamHeight p.1) :
    bulkExpression A p≤0 := by
  have hn:∀ᶠ z in 𝓝 p,z∈K:=mem_interior_iff_mem_nhds.mp hp
  have he:A =ᶠ[𝓝 p] exteriorFlux:=hn.mono fun _ hz=>hAe hz
  rw [bulkExpression_congr (he.trans (exteriorFlux_eventually_eq hu hq hs))]
  exact upperFlux_bulk_off_seam hu hq (ne_of_gt hs)

lemma cap_extension_bulk {K:Set (Space 7×ℝ)} {B:Space 7×ℝ→Space 7}
    (hBe:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p)
    {p:Space 7×ℝ} (hp:p∈interior K) (hu:U p.1<p.2)
    (hq:0<Cylindrical.radiusSq axis p.1) (hs:seamHeight p.1<p.2) :
    bulkExpression B p≤0 := by
  rw [bulkExpression_congr (cap_extension_eventually_eq hBe hp hq hs)]
  exact upperFlux_bulk_off_seam hu hq hs.ne

lemma clamped_extension_jump {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (huU:U x<u x)
    (hq:0<Cylindrical.radiusSq axis x)
    {A B:Space 7×ℝ→Space 7} {K:Set (Space 7×ℝ)}
    (hAe:EqOn A exteriorFlux K) (hBe:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p)
    (hp:(x,clampedHeight u seamHeight v x)∈K)
    (h1:u x<clampedHeight u seamHeight v x) (h2:clampedHeight u seamHeight v x<v x) :
    ‖B (x,clampedHeight u seamHeight v x)‖^2-‖A (x,clampedHeight u seamHeight v x)‖^2-
      2*inner ℝ (B (x,clampedHeight u seamHeight v x)-A (x,clampedHeight u seamHeight v x))
        (gradient (clampedHeight u seamHeight v) x)≤0 := by
  obtain ⟨hs1,hs2,hwσ⟩:=clamped_interior_seam h1 h2
  rw [hBe _ hp (by rw [hwσ]),hAe hp,clamped_seam_gradient hu hv hq h1 h2,hwσ]
  exact upperFlux_seam_jump hq (huU.trans hs1)

lemma clamped_extension_bottom {u v:Space 7→ℝ} {x:Space 7}
    (huU:U x<u x) (hq:0<Cylindrical.radiusSq axis x) (hlt:u x<v x)
    {A B:Space 7×ℝ→Space 7} {K:Set (Space 7×ℝ)}
    (hAe:EqOn A exteriorFlux K) (hBe:∀p∈K,seamHeight p.1≤p.2 → B p=upperFlux p)
    (hp:(x,u x)∈K) :
    (if u x=clampedHeight u seamHeight v x then B else A) (x,u x)=upperFlux (x,u x) := by
  by_cases ht:u x=clampedHeight u seamHeight v x
  · rw [ite_eq_left ht]
    apply hBe _ hp
    by_contra hn
    have hsw:u x<clampedHeight u seamHeight v x:=by
      change u x < max (u x) (min (v x) (seamHeight x))
      exact (lt_min hlt (not_le.mp hn)).trans_le (le_max_right _ _)
    exact hsw.ne ht
  · rw [ite_eq_right ht,hAe hp]
    apply (upperFlux_eq_exterior (p:=(x,u x)) huU hq _).symm
    have hh:u x < max (u x) (min (v x) (seamHeight x)):=
      lt_of_le_of_ne (le_clampedHeight u seamHeight v x) ht
    exact ((lt_max_iff.mp hh).resolve_left (lt_irrefl _)).trans_le (min_le_right _ _)

/-- Pointwise differential comparison for the genuine discontinuous upper
flux primitive, away from the null axis and at differentiability points of
its three Lipschitz endpoint graphs. -/
theorem upperFlux_primitive_bound {u v:Space 7→ℝ} {x:Space 7}
    (hu:ContinuousAt u x) (hv:ContinuousAt v x) (huv:∀y,u y≤v y)
    (huU:U x<u x) (hqx:0<Cylindrical.radiusSq axis x)
    (hdu:DifferentiableAt ℝ u x) (hdv:DifferentiableAt ℝ v x)
    (hdw:DifferentiableAt ℝ (clampedHeight u seamHeight v) x) :
    divergence (verticalPotential upperFlux u v) x≤
      if u x<v x then ‖gradient v x‖^2+‖upperFlux (x,u x)‖^2-
        2*inner ℝ (upperFlux (x,u x)) (gradient u x) else 0 := by
  obtain ⟨K,hK,hKi,hKp,hKq⟩:=upperFlux_compact_tube (b:=v x) huU hqx
  obtain ⟨A,B,hA,hB,hAe,hBe⟩:=compact_branch_extensions hK hKp hKq
  have he:=primitive_eq_split_germ hu hv huv hKi hKp hKq hA.continuous hB.continuous hAe hBe
  have hed:divergence (verticalPotential upperFlux u v) x=
      divergence (splitGraphPotential A B u (clampedHeight u seamHeight v) v) x:=by
    unfold divergence; rw [he.fderiv_eq]
  rw [hed]
  let w:=clampedHeight u seamHeight v
  have huw:∀y,u y≤w y:=le_clampedHeight u seamHeight v
  have hwv:∀y,w y≤v y:=fun y=>clampedHeight_le (huv y)
  have hpoint (t:ℝ) (ht:t∈Icc (u x) (v x)):(x,t)∈interior K:=hKi ⟨rfl,ht⟩
  by_cases hlt:u x<v x
  · rw [ite_eq_left hlt]
    have hbA:∀s∈Ioo (u x) (w x),bulkExpression A (x,s)≤0:=by
      intro s hs
      exact exterior_extension_bulk hAe
        (hpoint s ⟨hs.1.le,hs.2.le.trans (hwv x)⟩) (huU.trans hs.1) hqx
        (below_clampedHeight hs.1 hs.2)
    have hbB:∀s∈Ioo (w x) (v x),bulkExpression B (x,s)≤0:=by
      intro s hs
      exact cap_extension_bulk hBe
        (hpoint s ⟨(huw x).trans hs.1.le,hs.2.le⟩)
        (huU.trans_le ((huw x).trans hs.1.le)) hqx (above_clampedHeight hs.1 hs.2)
    have hj:u x<w x → w x<v x → ‖B (x,w x)‖^2-‖A (x,w x)‖^2-
        2*inner ℝ (B (x,w x)-A (x,w x)) (gradient w x)≤0:=
      clamped_extension_jump hu hv huU hqx hAe hBe
        (interior_subset (hpoint (w x) ⟨huw x,hwv x⟩))
    have hbottom:(if u x=w x then B else A) (x,u x)=upperFlux (x,u x):=
      clamped_extension_bottom huU hqx hlt hAe hBe
        (interior_subset (hpoint (u x) ⟨le_rfl,hlt.le⟩))
    have hh:=split_graph_bound_open hA hB hdu hdw hdv huw hwv hbA hbB hj
    rwa [hbottom] at hh
  · rw [ite_eq_right hlt]
    have huvx:u x=v x:=le_antisymm (huv x) (not_lt.mp hlt)
    have hux:u x=w x:=le_antisymm (huw x) (by rw [huvx]; exact hwv x)
    have hwx:w x=v x:=hux.symm.trans huvx
    change divergence (fun y=>graphPotential A u w y+graphPotential B w v y) x≤0
    change DifferentiableAt ℝ w x at hdw
    rw [divergence_add (graphPotential_differentiableAt hA hdu hdw) (graphPotential_differentiableAt hB hdw hdv),
      graph_divergence_zero_contact hA hdu hdw huw hux,graph_divergence_zero_contact hB hdw hdv hwv hwx]
    norm_num
end Bernoulli.DeSilvaJerison

end
end

end OAI
