import OAI.Analysis.NumericalRange.DiskMapping

namespace OAI

noncomputable section

universe u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
namespace CompleteCrouzeix

section

section

lemma analytic_chart_rescale_avoid {U : Set ℂ} {χ : ℂ → ℂ} {a : ℂ}
    (ha : AnalyticAt ℂ χ 0) (hd : deriv χ 0 ≠ 0)
    (hs : ∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im)
    (hb : ∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U)
    (hav : ∀ᶠ z : ℂ in 𝓝 0, χ z ≠ a) :
    ∃ ψ : ℂ → ℂ, ψ 0 = χ 0 ∧ AnalyticOnNhd ℂ ψ (ball 0 2) ∧
      InjOn ψ (ball 0 2) ∧ (∀ z ∈ ball 0 2, deriv ψ z ≠ 0) ∧
      (∀ z ∈ ball 0 2, ψ z ∈ U ↔ 0 < z.im) ∧
      (∀ z ∈ ball 0 2, z.im = 0 → ψ z ∈ frontier U) ∧
      (∀ z ∈ ball 0 2, ψ z ≠ a) := by
  have hi := ha.hasStrictDerivAt.eventually_left_inverse hd
  have hd' := ha.deriv.continuousAt.eventually_ne hd
  have hall := ha.eventually_analyticAt.and (hi.and (hd'.and (hs.and (hb.and hav))))
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp hall
  let b : ℝ := r/3
  have ha0 : 0 < b := by dsimp [b]; positivity
  have han : (b : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  let ψ : ℂ → ℂ := fun z => χ ((b : ℂ)*z)
  have hmul : ∀ z ∈ ball (0 : ℂ) 2, (b : ℂ)*z ∈ ball 0 r := by
    intro z hz
    rw [mem_ball_zero_iff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha0]
    have hz' : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
    dsimp [b]
    nlinarith
  refine ⟨ψ,by simp [ψ],?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact (hrall (hmul z hz)).1.comp (analyticAt_const.fun_mul analyticAt_id)
  · intro z hz w hw he
    have hzi := (hrall (hmul z hz)).2.1
    have hwi := (hrall (hmul w hw)).2.1
    apply mul_left_cancel₀ han
    rw [← hzi,← hwi]
    exact congrArg _ he
  · intro z hz
    have hdχ := (hrall (hmul z hz)).1.differentiableAt.hasDerivAt
    have hdd := hdχ.comp z ((hasDerivAt_id z).const_mul (b : ℂ))
    have he : deriv ψ z = deriv χ ((b : ℂ)*z)*((b : ℂ)*1) := hdd.deriv
    rw [he]
    exact mul_ne_zero (hrall (hmul z hz)).2.2.1 (mul_ne_zero han one_ne_zero)
  · intro z hz
    change χ ((b : ℂ)*z) ∈ U ↔ 0 < z.im
    rw [(hrall (hmul z hz)).2.2.2.1]
    simpa using mul_pos_iff_of_pos_left ha0
  · intro z hz him
    apply (hrall (hmul z hz)).2.2.2.2.1
    simp [him]
  · intro z hz
    exact (hrall (hmul z hz)).2.2.2.2.2


open Set Filter Metric Complex
open scoped Topology

def LocalAnalyticBoundary (U : Set ℂ) (p : ℂ) : Prop :=
  ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im) ∧
    (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U)

structure DiskCoordinate (U : Set ℂ) (a : ℂ) where
  outer : Set ℂ
  outer_open : IsOpen outer
  closure_subset : closure U ⊆ outer
  toDisk : ℂ → ℂ
  fromDisk : ℂ → ℂ
  analytic_to : AnalyticOnNhd ℂ toDisk outer
  injective_to : InjOn toDisk outer
  noncritical_to : ∀ z ∈ outer, deriv toDisk z ≠ 0
  image_open : IsOpen (toDisk '' outer)
  analytic_from : AnalyticOnNhd ℂ fromDisk (toDisk '' outer)
  inverse_map : MapsTo fromDisk (toDisk '' outer) outer
  left_inverse : ∀ z ∈ outer, fromDisk (toDisk z) = z
  right_inverse : ∀ w ∈ toDisk '' outer, toDisk (fromDisk w) = w
  closedDisk_subset : closedBall 0 1 ⊆ toDisk '' outer
  image_domain : toDisk '' U = ball 0 1
  base_zero : toDisk a = 0

lemma analytic_noncritical_set_open (F : ℂ → ℂ) :
    IsOpen {z | AnalyticAt ℂ F z ∧ deriv F z ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact hz.1.eventually_analyticAt.and (hz.1.deriv.continuousAt.eventually_ne hz.2)

theorem analytic_domain_disk_coordinate {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hUb : Bornology.IsBounded U) {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, LocalAnalyticBoundary U p) :
    Nonempty (DiskCoordinate U a) := by
  obtain ⟨f,hf,hdfa,hfimage⟩ := bounded_riemann_mapping hU hUc hUb ha
  have hfa : AnalyticOnNhd ℂ f U := hf.1.analyticOnNhd hU
  obtain ⟨g,hga,hgto,hgf,hfg,hfd⟩ := holomorphic_injective_inverse hU
    hUc.isPathConnected.isConnected.isPreconnected hfa hf.2.1 ha hdfa
  rw [hfimage] at hga hgto hfg
  have hloc : ∀ p ∈ frontier U, ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F V ∧ deriv F p ≠ 0 ∧ EqOn F f (V ∩ U) := by
    intro p hp
    obtain ⟨χ,hχ0,hχa,hχd,hχs,hχb⟩ := hchart p hp
    have hpa : p ≠ a := by
      intro he
      have hpnot : p ∉ U := by rw [hU.frontier_eq] at hp; exact hp.2
      exact hpnot (he ▸ ha)
    have hav : ∀ᶠ z : ℂ in 𝓝 0, χ z ≠ a := hχa.continuousAt.eventually_ne (hχ0 ▸ hpa)
    obtain ⟨ψ,hψ0,hψa,hψi,hψd,hψs,hψb,hψav⟩ :=
      analytic_chart_rescale_avoid hχa hχd hχs hχb hav
    have hn : ∀ z ∈ upperClosedDisk, 0 < z.im → f (ψ z) ≠ 0 := by
      intro z hz him he
      have hz2 : z ∈ ball (0 : ℂ) 2 := closedBall_subset_ball (by norm_num : (1 : ℝ)<2) hz.1
      have hpu := (hψs z hz2).mpr him
      apply hψav z hz2
      exact hf.2.1 hpu ha (he.trans hf.2.2.2.symm)
    obtain ⟨V,hVo,hpV,F,hFa,hFd,hFe⟩ := conformal_chart_extension hU hfa hf.2.2.1
      hga.continuousOn hgto hgf hψa hψi hψd hψs hψb hn
    have hψp : ψ 0 = p := hψ0.trans hχ0
    exact ⟨V,hVo,hψp ▸ hpV,F,hFa,hψp ▸ hFd,hFe⟩
  obtain ⟨W,hWo,hUW,F,hFa,hFe,hFd⟩ := analytic_boundary_patch hU hfa hfd hloc
  have hFc : AnalyticOnNhd ℂ F (closure U) := hFa.mono hUW
  have hFto : MapsTo F U (ball 0 1) := by intro z hz; rw [hFe hz]; exact hf.2.2.1 hz
  have hgF : ∀ z ∈ U, g (F z) = z := by intro z hz; rw [hFe hz]; exact hgf z hz
  have hFb : ∀ p ∈ frontier U, ‖F p‖ = 1 := by
    intro p hp
    exact conformal_extension_boundary_norm hU hf.2.2.1 hga.continuousOn hgto hgf hFe hp
      (hFc p hp.1).continuousAt
  have hFi := conformal_extension_injOn_closure hU hFto hgF hFb hFc hFd
  have hK : IsCompact (closure U) := isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure,hUb.closure⟩
  obtain ⟨V₀,hV₀o,hUV₀,hV₀i,hV₀a⟩ := analytic_compact_injective_collar hK hFc hFd hFi
  let V := V₀ ∩ {z | AnalyticAt ℂ F z ∧ deriv F z ≠ 0}
  have hVo : IsOpen V := hV₀o.inter (analytic_noncritical_set_open F)
  have hUV : closure U ⊆ V := fun z hz => ⟨hUV₀ hz,hFc z hz,hFd z hz⟩
  have hVi : InjOn F V := hV₀i.mono inter_subset_left
  have hVa : AnalyticOnNhd ℂ F V := hV₀a.mono inter_subset_left
  have hVd : ∀ z ∈ V, deriv F z ≠ 0 := fun z hz => hz.2.2
  obtain ⟨hFo,G,hGa,hGto,hGF,hFG⟩ := noncritical_holomorphic_inverse hVo hVa hVi hVd
  have hFimage : F '' U = ball 0 1 := by rw [hFe.image_eq,hfimage]
  have hcl : closedBall (0 : ℂ) 1 ⊆ F '' closure U := by
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),← hFimage]
    exact closure_minimal (image_mono subset_closure) (hK.image_of_continuousOn hFc.continuousOn).isClosed
  exact ⟨⟨V,hVo,hUV,F,G,hVa,hVi,hVd,hFo,hGa,hGto,hGF,hFG,
    hcl.trans (image_mono hUV),hFimage,(hFe ha).trans hf.2.2.2⟩⟩

end

open Set Filter Metric Complex
open scoped Topology
namespace DiskCoordinate
variable {U : Set ℂ} {a : ℂ} (D : DiskCoordinate U a)

lemma closure_maps : MapsTo D.toDisk (closure U) (closedBall 0 1) := by
  intro z hz
  have he := mem_closure_image (D.analytic_to z (D.closure_subset hz)).continuousAt hz
  rwa [D.image_domain,closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at he

lemma inverse_ball (w : ℂ) (hw : w ∈ ball 0 1) : D.fromDisk w ∈ U := by
  obtain ⟨z,hz,he⟩ := D.image_domain.symm ▸ hw
  rw [← he,D.left_inverse z (D.closure_subset (subset_closure hz))]
  exact hz

lemma inverse_image_ball : D.fromDisk '' ball 0 1 = U := by
  apply Subset.antisymm
  · rintro z ⟨w,hw,rfl⟩; exact D.inverse_ball w hw
  · intro z hz
    refine ⟨D.toDisk z,?_,D.left_inverse z (D.closure_subset (subset_closure hz))⟩
    exact D.image_domain ▸ mem_image_of_mem D.toDisk hz

lemma inverse_closed (w : ℂ) (hw : w ∈ closedBall 0 1) : D.fromDisk w ∈ closure U := by
  have he := mem_closure_image (D.analytic_from w (D.closedDisk_subset hw)).continuousAt
    (show w ∈ closure (ball (0 : ℂ) 1) by rwa [closure_ball (0 : ℂ) one_ne_zero])
  rwa [D.inverse_image_ball] at he

lemma inverse_injective : InjOn D.fromDisk (D.toDisk '' D.outer) := by
  intro w hw z hz he
  rw [← D.right_inverse w hw,← D.right_inverse z hz,he]

lemma inverse_noncritical (w : ℂ) (hw : w ∈ D.toDisk '' D.outer) : deriv D.fromDisk w ≠ 0 := by
  have hd := (D.analytic_to (D.fromDisk w) (D.inverse_map hw)).differentiableAt.hasDerivAt.comp w
    (D.analytic_from w hw).differentiableAt.hasDerivAt
  have he : (D.toDisk ∘ D.fromDisk) =ᶠ[𝓝 w] id := by
    filter_upwards [D.image_open.mem_nhds hw] with z hz
    exact D.right_inverse z hz
  have hed := hd.congr_of_eventuallyEq he.symm
  have hmul : deriv D.toDisk (D.fromDisk w)*deriv D.fromDisk w = 1 :=
    hed.unique (hasDerivAt_id w)
  intro hn
  simp [hn] at hmul

lemma exists_inverse_radius : ∃ R : ℝ, 1 < R ∧ ball (0 : ℂ) R ⊆ D.toDisk '' D.outer := by
  obtain ⟨δ,hδ,hδsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open
    D.image_open D.closedDisk_subset
  have he := thickening_closedBall hδ (by norm_num : (0 : ℝ) ≤ 1) (0 : ℂ)
  exact ⟨δ+1,by linarith,he ▸ hδsub⟩

lemma inverse_base (ha : a ∈ U) : D.fromDisk 0 = a := by
  rw [← D.base_zero,D.left_inverse a (D.closure_subset (subset_closure ha))]

lemma inverse_mem_domain_iff {w : ℂ} (hw : w ∈ D.toDisk '' D.outer) :
    D.fromDisk w ∈ U ↔ w ∈ ball 0 1 := by
  constructor
  · intro h
    have he := D.image_domain ▸ mem_image_of_mem D.toDisk h
    rwa [D.right_inverse w hw] at he
  · exact D.inverse_ball w

lemma inverse_mem_closure_iff {w : ℂ} (hw : w ∈ D.toDisk '' D.outer) :
    D.fromDisk w ∈ closure U ↔ w ∈ closedBall 0 1 := by
  constructor
  · intro h
    have he := D.closure_maps h
    rwa [D.right_inverse w hw] at he
  · exact D.inverse_closed w

lemma inverse_sphere_frontier (hU : IsOpen U) :
    D.fromDisk '' sphere 0 1 = frontier U := by
  apply Subset.antisymm
  · rintro z ⟨w,hw,rfl⟩
    rw [hU.frontier_eq]
    have hwc : w ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hw
    refine ⟨D.inverse_closed w hwc,?_⟩
    intro h
    have he := (D.inverse_mem_domain_iff (D.closedDisk_subset hwc)).mp h
    exact (not_lt_of_ge (le_of_eq (mem_sphere_zero_iff_norm.mp hw).symm)) (mem_ball_zero_iff.mp he)
  · intro z hz
    have hzo := D.closure_subset hz.1
    refine ⟨D.toDisk z,?_,D.left_inverse z hzo⟩
    rw [mem_sphere_zero_iff_norm]
    apply le_antisymm (mem_closedBall_zero_iff.mp (D.closure_maps hz.1))
    by_contra hn
    have ht : D.toDisk z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_not_ge hn)
    have hu := D.inverse_ball (D.toDisk z) ht
    rw [D.left_inverse z hzo] at hu
    exact (hU.frontier_eq ▸ hz).2 hu
end DiskCoordinate
end

open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate

def convexBarrier {ι : Type u_3} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (z : ℂ) : ℝ :=
  c * Complex.normSq z + ∑ i, Real.exp (l i z - a i)

lemma convexBarrier_continuous {ι : Type u_4} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) : Continuous (convexBarrier c l a) := by
  unfold convexBarrier
  fun_prop

lemma convexBarrier_quadratic_le {ι : Type u_5} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (z : ℂ) :
    c * ‖z‖^2 ≤ convexBarrier c l a z := by
  rw [Complex.sq_norm]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le)

lemma convexBarrier_exp_le {ι : Type u_6} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (i : ι) (z : ℂ) :
    Real.exp (l i z-a i) ≤ convexBarrier c l a z := by
  unfold convexBarrier
  refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg hc (Complex.normSq_nonneg z)))
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos (l j z-a j)).le) (Finset.mem_univ i)

lemma convexBarrier_convex {ι : Type u_7} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) : ConvexOn ℝ univ (convexBarrier c l a) := by
  have hq : ConvexOn ℝ univ (fun z : ℂ => c * Complex.normSq z) := by
    simpa only [smul_eq_mul,Pi.pow_apply,Complex.sq_norm] using
      ((convexOn_norm (s := (univ : Set ℂ)) convex_univ).pow (fun x _ => norm_nonneg x) 2).smul hc
  have he (i : ι) : ConvexOn ℝ univ (fun z => Real.exp (l i z-a i)) := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy α β hα hβ hab
    have hh := convexOn_exp.2 (mem_univ (l i x-a i)) (mem_univ (l i y-a i)) hα hβ hab
    simp only [map_add,map_smul,smul_eq_mul] at hh ⊢
    convert hh using 1
    congr 1
    linear_combination (a i) * hab
  refine hq.add ⟨convex_univ,?_⟩
  intro x hx y hy α β hα hβ hab
  simpa only [smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      (he i).2 hx hy hα hβ hab)

lemma finite_strict_separators {K U : Set ℂ} (hK : IsCompact K)
    (hKc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U) (R : ℝ) :
    ∃ (N : ℕ) (l : Fin N → ℂ →L[ℝ] ℝ) (a : Fin N → ℝ),
      (∀ i z, z ∈ K → l i z < a i) ∧
      ∀ z ∈ closedBall (0:ℂ) R, (∀ i, l i z ≤ a i) → z ∈ U := by
  classical
  let S := closedBall (0:ℂ) R \ U
  have hS : IsCompact S := (isCompact_closedBall (0:ℂ) R).diff hU
  have hsep (x : S) : ∃ (l : ℂ →L[ℝ] ℝ) (a : ℝ),
      (∀ z ∈ K, l z < a) ∧ a < l x := by
    exact geometric_hahn_banach_closed_point hKc hK.isClosed
      (fun hx => x.property.2 (hKU hx))
  choose l a hKa hal using hsep
  obtain ⟨s,hs⟩ := hS.elim_finite_subcover
    (fun x : S => {z : ℂ | a x < l x z})
    (fun x => isOpen_lt continuous_const (l x).continuous) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z,hz⟩,hal ⟨z,hz⟩⟩)
  let e := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s,fun i => l (e i),fun i => a (e i),?_,?_⟩
  · intro i z hz
    exact hKa (e i) z hz
  · intro z hz hza
    by_contra hzu
    have hh := hs ⟨hz,hzu⟩
    simp only [mem_iUnion] at hh
    obtain ⟨x,hx,hh⟩ := hh
    have hb := hza ((Fintype.equivFin s) ⟨x,hx⟩)
    simp only [e,Equiv.symm_apply_apply] at hb
    exact not_lt_of_ge hb hh

lemma separates_scaled_exp {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (l : ℂ →L[ℝ] ℝ) (a : ℝ) (ha : ∀ z ∈ K, l z < a)
    {ε : ℝ} (hε : 0 < ε) : ∃ t > 0, ∀ z ∈ K, Real.exp (t*(l z-a)) < ε := by
  obtain ⟨x,hx,hm⟩ := hK.exists_isMaxOn hne l.continuous.continuousOn
  have hn : l x-a < 0 := sub_neg.mpr (ha x hx)
  have ht : Tendsto (fun t : ℝ => Real.exp (t*(l x-a))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_neg hn).mpr tendsto_id)
  obtain ⟨t,htp,hte⟩ := ((eventually_gt_atTop (0:ℝ)).and (ht.eventually (gt_mem_nhds hε))).exists
  refine ⟨t,htp,fun z hz => ?_⟩
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right (hm hz) a) htp.le)).trans_lt hte

theorem exists_convex_barrier {K U : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hKc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (N : ℕ) (c : ℝ) (l : Fin N → ℂ →L[ℝ] ℝ) (a : Fin N → ℝ),
      0 < c ∧ (∀ z ∈ K, convexBarrier c l a z < 1) ∧
      {z | convexBarrier c l a z ≤ 1} ⊆ U := by
  classical
  obtain ⟨r,hr,hrK⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N,l,a,hla,hcover⟩ := finite_strict_separators hK hKc hU hKU (2*r)
  let ε : ℝ := 1/(4*((N:ℝ)+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ht (i : Fin N) : ∃ t > 0, ∀ z ∈ K, Real.exp (t*(l i z-a i)) < ε :=
    separates_scaled_exp hK hne (l i) (a i) (hla i) hε
  choose t htp hte using ht
  let c : ℝ := (4*r^2)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  let L : Fin N → ℂ →L[ℝ] ℝ := fun i => t i • l i
  let b : Fin N → ℝ := fun i => t i*a i
  have hLb (i : Fin N) (z : ℂ) : L i z-b i = t i*(l i z-a i) := by
    simp only [L,b,smul_apply,smul_eq_mul,mul_sub]
  refine ⟨N,c,L,b,hc,?_,?_⟩
  · intro z hz
    have hsq : c*Complex.normSq z ≤ 1/4 := by
      rw [← Complex.sq_norm]
      have hzr : ‖z‖^2 ≤ r^2 := (sq_le_sq₀ (norm_nonneg _) hr.le).mpr (hrK z hz)
      dsimp [c]
      have hr2 : 0 < r^2 := sq_pos_of_pos hr
      rw [inv_mul_eq_div]
      apply (div_le_iff₀ (by positivity : 0 < 4*r^2)).mpr
      nlinarith
    have heSum : (∑ i, Real.exp (L i z-b i)) ≤ (N:ℝ)*ε := by
      calc
        _ ≤ ∑ i : Fin N, ε := Finset.sum_le_sum (fun i _ => by rw [hLb]; exact (hte i z hz).le)
        _ = _ := by simp
    have heSmall : (N:ℝ)*ε < 1/4 := by
      dsimp [ε]
      rw [mul_one_div]
      apply (div_lt_iff₀ (by positivity : 0 < 4*((N:ℝ)+1))).mpr
      linarith
    unfold convexBarrier
    linarith
  · intro z hz
    have hq := (convexBarrier_quadratic_le c L b z).trans hz
    have hnorm : ‖z‖ ≤ 2*r := by
      dsimp [c] at hq
      rw [inv_mul_eq_div] at hq
      have hs := (div_le_iff₀ (by positivity : 0 < 4*r^2)).mp hq
      nlinarith [norm_nonneg z]
    apply hcover z (by simpa using hnorm)
    intro i
    have he := (convexBarrier_exp_le hc.le L b i z).trans hz
    have hh : L i z-b i ≤ 0 := Real.exp_le_one_iff.mp he
    rw [hLb] at hh
    have hneg : l i z-a i ≤ 0 := by nlinarith [htp i]
    exact sub_nonpos.mp hneg

lemma convexBarrier_analytic {ι : Type u_8} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) (z : ℂ) :
    AnalyticAt ℝ (convexBarrier c l a) z := by
  unfold convexBarrier
  simp only [Complex.normSq_apply]
  have hr : AnalyticAt ℝ (fun z : ℂ => z.re) z := Complex.reCLM.analyticAt z
  have hi : AnalyticAt ℝ (fun z : ℂ => z.im) z := Complex.imCLM.analyticAt z
  exact (analyticAt_const.fun_mul ((hr.fun_mul hr).fun_add (hi.fun_mul hi))).fun_add
    (Finset.analyticAt_fun_sum _ (fun i _ => ((l i).analyticAt z |>.fun_sub analyticAt_const).rexp))

lemma convexBarrier_sublevel_convex {ι : Type u_9} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) :
    Convex ℝ {z | convexBarrier c l a z < 1} := by
  simpa using (convexBarrier_convex hc l a).convex_lt 1

lemma convexBarrier_sublevel_open {ι : Type u_10} [Fintype ι] (c : ℝ)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) :
    IsOpen {z | convexBarrier c l a z < 1} :=
  isOpen_lt (convexBarrier_continuous c l a) continuous_const

lemma convexBarrier_sublevel_bounded {ι : Type u_11} [Fintype ι] {c : ℝ} (hc : 0 < c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) :
    Bornology.IsBounded {z | convexBarrier c l a z ≤ 1} := by
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := Real.sqrt (1/c))).subset
  intro z hz
  have hle := (convexBarrier_quadratic_le c l a z).trans hz
  have hs : ‖z‖^2 ≤ 1/c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hle)
  simpa using (Real.le_sqrt (norm_nonneg z) (by positivity) |>.mpr hs)

lemma convexOn_fderiv_support {q : ℂ → ℝ} (hq : ConvexOn ℝ univ q)
    {p : ℂ} (hd : DifferentiableAt ℝ q p) (x : ℂ) :
    fderiv ℝ q p (x-p) ≤ q x-q p := by
  have hc : ConvexOn ℝ univ (q ∘ (AffineMap.lineMap p x : ℝ →ᵃ[ℝ] ℂ)) := by
    simpa using ConvexOn.comp_affineMap (AffineMap.lineMap p x) hq
  have hder : HasDerivAt (q ∘ (AffineMap.lineMap p x : ℝ →ᵃ[ℝ] ℂ)) (fderiv ℝ q p (x-p)) 0 := by
    apply HasFDerivAt.comp_hasDerivAt
    · simpa only [AffineMap.lineMap_apply_zero] using hd.hasFDerivAt
    · exact AffineMap.hasDerivAt_lineMap
  simpa [slope] using hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hder

lemma convexBarrier_boundary_regular {ι : Type u_12} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) {x p : ℂ}
    (hx : convexBarrier c l a x < 1) (hp : convexBarrier c l a p = 1) :
    fderiv ℝ (convexBarrier c l a) p ≠ 0 := by
  have h := convexOn_fderiv_support (convexBarrier_convex hc l a)
    (convexBarrier_analytic c l a p).differentiableAt x
  intro hz
  rw [hz,zero_apply,hp] at h
  linarith

lemma convexOn_closure_sublevel {q : ℂ → ℝ} (hq : ConvexOn ℝ univ q)
    (hqc : Continuous q) {x : ℂ} (hx : q x < 1) :
    closure {z | q z < 1} = {z | q z ≤ 1} := by
  apply Subset.antisymm (closure_minimal (fun z (hz : q z < 1) => show q z ≤ 1 from hz.le) (isClosed_le hqc continuous_const))
  intro p hp
  change q p ≤ 1 at hp
  have ht : Tendsto (AffineMap.lineMap p x : ℝ → ℂ) (𝓝[>] 0) (𝓝 p) := by
    have hc : Continuous (AffineMap.lineMap p x : ℝ → ℂ) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact AffineMap.hasDerivAt_lineMap.continuousAt
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))] with t ht0 ht1
  change 0 < t at ht0
  have hc := hq.2 (mem_univ p) (mem_univ x) (show 0 ≤ 1-t by linarith) (le_of_lt ht0)
    (by ring : 1-t+t=1)
  simp only [smul_eq_mul] at hc
  rw [AffineMap.lineMap_apply_module]
  have hh : (1-t)*q p+t*q x < 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-t) (show 0 ≤ 1-q p by linarith)]
  exact hc.trans_lt hh

lemma convexOn_frontier_sublevel {q : ℂ → ℝ} (hq : ConvexOn ℝ univ q)
    (hqc : Continuous q) {x : ℂ} (hx : q x < 1) :
    frontier {z | q z < 1} = {z | q z = 1} := by
  rw [(isOpen_lt hqc continuous_const).frontier_eq,convexOn_closure_sublevel hq hqc hx]
  ext z
  simp only [Set.mem_sdiff,mem_ofPred_eq,not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2,fun h => ⟨h.le,h.ge⟩⟩

end CompleteCrouzeix

end

end OAI
