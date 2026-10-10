import OAI.Analysis.LienardCycles.BoundaryGerm

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScaledProfile ScalarArcs ArcFamilies PartialCalculus
noncomputable def φ (a : Fin 6 → ℝ) (h : ℝ) : ℝ := poly a (root h)
noncomputable def endpoint (a : Fin 6 → ℝ) (upper : Bool) (h t : ℝ) : ℝ :=
  if upper then ScalarArcs.upper (φ a) h t else lower (φ a) h t
noncomputable def branch (a : Fin 6 → ℝ) (upper : Bool) (q : ℝ×ℝ) : ℝ := endpoint a upper (q.2^2/2) q.1
noncomputable def axisEndpoint (a : Fin 6 → ℝ) (upper : Bool) (t : ℝ) : ℝ :=
  if upper then axisUpper (φ a) t else axisLower (φ a) t
lemma φ_continuous (a : Fin 6 → ℝ) : Continuous (φ a) := by
  unfold φ poly root
  fun_prop
lemma φ_smooth (a : Fin 6 → ℝ) : ContDiffOn ℝ 1 (φ a) (Ioi 0) := by
  intro h hh
  exact (((QuinticProfile.analytic a (q:=((0:ℝ),h)) hh).comp h
    (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
lemma φ_square (a : Fin 6 → ℝ) {x : ℝ} (hx : 0≤x) : φ a (x^2/2)=poly a x := by
  have he : 2*(x^2/2)=x^2 := by ring
  simp only [φ,root,he,Real.sqrt_sq hx]
lemma branch_analytic (a : Fin 6 → ℝ) (u : Bool) {t x : ℝ} (hx : 0<x) (ht : x^2/2<t) :
    ContDiffAt ℝ ω (branch a u) (t,x) := by
  have hh : 0<x^2/2 := div_pos (sq_pos_of_pos hx) (by norm_num)
  obtain ⟨hl,hr⟩ := PositiveVariation.endpoints (QuinticProfile.profile a)
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh ht
  have hc : ContDiffAt ℝ ω (fun q : ℝ×ℝ=>(((0:ℝ),q.1),q.2^2/2)) (t,x) := by fun_prop
  cases u
  · exact hl.comp (t,x) hc
  · exact hr.comp (t,x) hc
lemma branch_equation (a : Fin 6 → ℝ) (u : Bool) {t x : ℝ} (hx : 0<x) (ht : x^2/2<t) :
    HasDerivAt (fun s=>(s,branch a u (t,s))) (field a (x,branch a u (t,x))) x ∧
      (x,branch a u (t,x)) ∈ domain a := by
  have hh : 0<x^2/2 := div_pos (sq_pos_of_pos hx) (by norm_num)
  obtain ⟨hl,hr⟩ := PositiveVariation.base_derivatives (QuinticProfile.profile a)
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh ht
  have hd : HasDerivAt (fun s : ℝ=>s^2/2) x x := by convert! ((hasDerivAt_id x).pow 2).div_const 2 using 1; simp
  have hu := chosen_arch (positive_arch_exists (φ_smooth a) hh ht)
  have he : HasDerivAt (fun s=>branch a u (t,s)) (x/(poly a x-branch a u (t,x))) x := by
    cases u
    · convert! hl.comp x hd using 1
      change x/(poly a x-branch a false (t,x))=1/(φ a (x^2/2)-_) * x
      rw [φ_square a hx.le]
      change x/(poly a x-branch a false (t,x))=1/(poly a x-branch a false (t,x))*x
      ring
    · convert! hr.comp x hd using 1
      change x/(poly a x-branch a true (t,x))=1/(φ a (x^2/2)-_) * x
      rw [φ_square a hx.le]
      change x/(poly a x-branch a true (t,x))=1/(poly a x-branch a true (t,x))*x
      ring
  refine ⟨(hasDerivAt_id x).prodMk he,?_⟩
  cases u
  · exact ne_of_gt (by change 0<poly a x-_ ; rw [←φ_square a hx.le]; exact sub_pos.mpr hu.lower_transverse)
  · exact ne_of_lt (by change poly a x-_<0 ; rw [←φ_square a hx.le]; exact sub_neg.mpr hu.upper_transverse)
lemma branch_peak_sign (a : Fin 6 → ℝ) (u : Bool) {t x : ℝ} (hx : 0<x) (ht : x^2/2<t) :
    if u then 0<first (branch a u) (t,x) else first (branch a u) (t,x)<0 := by
  have hh : 0<x^2/2 := div_pos (sq_pos_of_pos hx) (by norm_num)
  obtain ⟨hl,hr⟩ := PositiveVariation.peak_signs (QuinticProfile.profile a)
    (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh ht
  have hd := (first_hasDerivAt ((branch_analytic a u hx ht).differentiableAt (by simp))).deriv
  cases u
  · change first (branch a false) (t,x)<0
    rw [←hd]
    exact hl
  · change 0<first (branch a true) (t,x)
    rw [←hd]
    exact hr
lemma branch_tendsto (a : Fin 6 → ℝ) (u : Bool) {t : ℝ} (ht : 0<t) :
    Tendsto (fun x=>branch a u (t,x)) (𝓝[>] 0) (𝓝 (axisEndpoint a u t)) := by
  have hc : Tendsto (fun x : ℝ=>x^2/2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hh := (((continuousAt_id.pow 2).div_const 2 : ContinuousAt (fun x : ℝ=>x^2/2) 0).tendsto).mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ) from inf_le_left)
    simpa only [Pi.pow_apply,id_eq,zero_pow (by norm_num : (2:ℕ)≠0),zero_div] using hh
  have he : ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), x^2/2 ∈ Ioi (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_pos (sq_pos_of_pos (show 0<x from hx)) (by norm_num)
  have hs : Tendsto (fun x : ℝ=>x^2/2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hc,he⟩
  cases u
  · exact (lower_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn ht).comp hs
  · exact (upper_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn ht).comp hs

theorem endpoint_germ (a : Fin 6 → ℝ) (u : Bool) {t : ℝ} (ht : 0<t)
    (htr : axisEndpoint a u t≠poly a 0) :
    ∃ G : ℝ×ℝ → ℝ, ContDiffAt ℝ ω G (t,0) ∧ G (t,0)=axisEndpoint a u t ∧
      (∀ᶠ q in 𝓝 (t,(0:ℝ)), 0<q.2 → G q=branch a u q) ∧
      (if u then 0<first G (t,0) else first G (t,0)<0) := by
  let T := Real.sqrt t
  have hT : 0<T := Real.sqrt_pos.mpr ht
  have hbound {x : ℝ} (hx : x ∈ Ioo 0 T) : x^2/2<t/2 := by
    have hs : x^2<T^2 := sq_lt_sq₀ hx.1.le hT.le |>.mpr hx.2
    dsimp only [T] at hs
    rw [Real.sq_sqrt ht.le] at hs
    linarith
  have hAU : (0,axisEndpoint a u t) ∈ domain a := sub_ne_zero.mpr htr.symm
  obtain ⟨G,hG,h0,he,δ,hδ,k,hk,hD⟩ := boundary_germ (V:=field a) (domain_open a)
    (fun z hz=>(field_analytic a hz).of_le (by simp) |>.contDiffWithinAt)
    (y:=branch a u) (J:=Ioi (t/2)) (Ioi_mem_nhds (by linarith)) hT
    (fun x hx=>branch_analytic a u hx.1 (by linarith [hbound hx]))
    (fun p hp x hx=>branch_equation a u hx.1 ((hbound hx).trans hp))
    (branch_tendsto a u ht) (local_flow a hAU) hAU
  refine ⟨G,hG,h0,he,?_⟩
  have hs := branch_peak_sign a u hδ.1 (show δ^2/2<t by linarith [hbound hδ])
  cases u
  · simp only [Bool.false_eq_true,↓reduceIte] at hs ⊢
    rw [hD]
    exact mul_neg_of_pos_of_neg hk hs
  · simp only [↓reduceIte] at hs ⊢
    rw [hD]
    exact mul_pos hk hs
end QuinticLienard.AxisFlow

end OAI
