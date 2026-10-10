import OAI.Analysis.NumericalRange.AnalyticCharts

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_23 u_24 u_25

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
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate

section

lemma regular_real_normal_coordinates (D : ℂ →L[ℝ] ℝ) (hD : D ≠ 0) :
    ∃ u v : ℂ, ∃ d : ℝ, u ≠ 0 ∧ v = I*u ∧ d < 0 ∧ D u = 0 ∧ D v = d ∧
      (∀ z : ℂ, D (z*u) = d*z.im) := by
  let a := D 1
  let b := D I
  let u : ℂ := -b+a*I
  let v : ℂ := -a-b*I
  let d : ℝ := -(a^2+b^2)
  have hn : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hD
    apply ContinuousLinearMap.ext
    intro z
    rw [real_clm_complex_apply]
    change z.re*a+z.im*b=0
    simp [hh.1,hh.2]
  have hd : d < 0 := by
    dsimp [d]
    rcases hn with hn | hn
    · nlinarith [sq_pos_of_ne_zero hn,sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero hn,sq_nonneg a]
  have hu : u ≠ 0 := by
    intro hh
    have hr := congrArg Complex.re hh
    have hi := congrArg Complex.im hh
    simp [u] at hr hi
    rcases hn with hn | hn
    · exact hn hi
    · exact hn hr
  have hvI : v = I*u := by
    apply Complex.ext <;> simp [u,v]
  have hDu : D u = 0 := by rw [real_clm_complex_apply]; simp [u,a,b]; ring
  have hDv : D v = d := by rw [real_clm_complex_apply]; simp [v,d,a,b]; ring
  refine ⟨u,v,d,hu,hvI,hd,hDu,hDv,?_⟩
  intro z
  rw [real_clm_complex_apply]
  simp [u,a,b,d]
  ring

lemma convexBarrier_local_analytic_chart {ι : Type u_23} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) {x p : ℂ}
    (hx : convexBarrier c l a x < 1) (hp : convexBarrier c l a p = 1) :
    ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ {w | convexBarrier c l a w < 1} ↔ 0 < z.im) ∧
      (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier {w | convexBarrier c l a w < 1}) := by
  let q := convexBarrier c l a
  let D := fderiv ℝ q p
  have hreg : D ≠ 0 := convexBarrier_boundary_regular hc l a hx hp
  obtain ⟨u,v,d,hu,hvI,hd,hDu,hDv,hDmul⟩ := regular_real_normal_coordinates D hreg
  let H := barrierChartComplexification c l a p u v
  have hHa : AnalyticAt ℂ H 0 := barrierChartComplexification_analytic c l a p u v
  have hHr : ∀ t s : ℝ, H ((t : ℂ),(s : ℂ)) = (q (p+t • u+s • v)-1 : ℝ) :=
    barrierChartComplexification_real c l a p u v
  have hH0 : H 0 = 0 := by
    have hp' : q p = 1 := hp
    simpa only [ofReal_zero,zero_smul,add_zero,hp',sub_self,Prod.mk_zero_zero] using hHr 0 0
  have hHD : HasFDerivAt H ((d : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0 :=
    analytic_real_complexification_deriv (convexBarrier_analytic c l a p).differentiableAt hHa hHr hDu hDv
  obtain ⟨φ,hφa,hφ0,hφD,hgraph,hreal⟩ := analytic_implicit_real_graph hd.ne hHa hH0 hHD
    (barrierChartComplexification_conj c l a p u v)
  let χ : ℂ → ℂ := fun z => p+z*u+φ z*v
  have hχ0 : χ 0 = p := by simp [χ,hφ0]
  have hχa : AnalyticAt ℂ χ 0 :=
    (analyticAt_const.fun_add (analyticAt_id.fun_mul analyticAt_const)).fun_add (hφa.fun_mul analyticAt_const)
  have hχD : HasDerivAt χ u 0 := by
    convert! (((hasDerivAt_id (0 : ℂ)).mul_const u).const_add p).add (hφD.mul_const v) using 1 ; simp
  have hχne : deriv χ 0 ≠ 0 := by rwa [hχD.deriv]
  have hcont : ContinuousAt (fun z : ℂ => (z.re : ℂ)) 0 := by fun_prop
  have haxis : ∀ᶠ z : ℂ in 𝓝 0, q (χ (z.re : ℂ)) = 1 := by
    have hg := hcont.tendsto.eventually hgraph
    have hr := hcont.tendsto.eventually hreal
    filter_upwards [hg,hr] with z hg hr
    have hφim : (φ (z.re : ℂ)).im = 0 := hr (by simp)
    have hφr : ((φ (z.re : ℂ)).re : ℂ) = φ (z.re : ℂ) := by apply Complex.ext <;> simp [hφim]
    have he := hHr z.re (φ (z.re : ℂ)).re
    rw [hφr,hg] at he
    have he' : q (p+z.re • u+(φ (z.re : ℂ)).re • v)-1 = 0 :=
      Complex.ofReal_injective he.symm
    simpa only [χ,Complex.real_smul,hφr] using sub_eq_zero.mp he'
  have hqa : AnalyticAt ℝ q p := convexBarrier_analytic c l a p
  have hqχa : AnalyticAt ℝ (q ∘ χ) 0 := hqa.comp_of_eq (hχa.restrictScalars) hχ0
  have hqD : HasFDerivAt q D (χ 0) := by simpa only [hχ0] using hqa.differentiableAt.hasFDerivAt
  have hqχD : HasFDerivAt (q ∘ χ) (d • Complex.imCLM) 0 := by
    convert! hqD.comp 0 (hχD.hasFDerivAt.restrictScalars ℝ) using 1
    apply ContinuousLinearMap.ext
    intro z
    change d*z.im = D (z*u)
    exact (hDmul z).symm
  have hstrict : HasStrictFDerivAt (q ∘ χ) (d • Complex.imCLM) 0 := by
    rw [← hqχD.fderiv]
    exact hqχa.hasStrictFDerivAt
  have hside := local_normal_side hd hstrict haxis
  refine ⟨χ,hχ0,hχa,hχne,?_,?_⟩
  · filter_upwards [hside] with z hz
    exact hz.1
  · filter_upwards [hside] with z hz
    intro him
    rw [convexOn_frontier_sublevel (convexBarrier_convex hc l a) (convexBarrier_continuous c l a) hx]
    exact hz.2 him

lemma convexBarrier_local_analytic_closed_chart {ι : Type u_24} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) {x p : ℂ}
    (hx : convexBarrier c l a x < 1) (hp : convexBarrier c l a p = 1) :
    ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ {w | convexBarrier c l a w < 1} ↔ 0 < z.im) ∧
      (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier {w | convexBarrier c l a w < 1}) ∧
      (∀ᶠ z : ℂ in 𝓝 0, convexBarrier c l a (χ z) ≤ 1 ↔ 0 ≤ z.im) := by
  let q := convexBarrier c l a
  let D := fderiv ℝ q p
  have hreg : D ≠ 0 := convexBarrier_boundary_regular hc l a hx hp
  obtain ⟨u,v,d,hu,hvI,hd,hDu,hDv,hDmul⟩ := regular_real_normal_coordinates D hreg
  let H := barrierChartComplexification c l a p u v
  have hHa : AnalyticAt ℂ H 0 := barrierChartComplexification_analytic c l a p u v
  have hHr : ∀ t s : ℝ, H ((t : ℂ),(s : ℂ)) = (q (p+t • u+s • v)-1 : ℝ) :=
    barrierChartComplexification_real c l a p u v
  have hH0 : H 0 = 0 := by
    have hp' : q p = 1 := hp
    simpa only [ofReal_zero,zero_smul,add_zero,hp',sub_self,Prod.mk_zero_zero] using hHr 0 0
  have hHD : HasFDerivAt H ((d : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0 :=
    analytic_real_complexification_deriv (convexBarrier_analytic c l a p).differentiableAt hHa hHr hDu hDv
  obtain ⟨φ,hφa,hφ0,hφD,hgraph,hreal⟩ := analytic_implicit_real_graph hd.ne hHa hH0 hHD
    (barrierChartComplexification_conj c l a p u v)
  let χ : ℂ → ℂ := fun z => p+z*u+φ z*v
  have hχ0 : χ 0 = p := by simp [χ,hφ0]
  have hχa : AnalyticAt ℂ χ 0 :=
    (analyticAt_const.fun_add (analyticAt_id.fun_mul analyticAt_const)).fun_add (hφa.fun_mul analyticAt_const)
  have hχD : HasDerivAt χ u 0 := by
    convert! (((hasDerivAt_id (0 : ℂ)).mul_const u).const_add p).add (hφD.mul_const v) using 1 ; simp
  have hχne : deriv χ 0 ≠ 0 := by rwa [hχD.deriv]
  have hcont : ContinuousAt (fun z : ℂ => (z.re : ℂ)) 0 := by fun_prop
  have haxis : ∀ᶠ z : ℂ in 𝓝 0, q (χ (z.re : ℂ)) = 1 := by
    have hg := hcont.tendsto.eventually hgraph
    have hr := hcont.tendsto.eventually hreal
    filter_upwards [hg,hr] with z hg hr
    have hφim : (φ (z.re : ℂ)).im = 0 := hr (by simp)
    have hφr : ((φ (z.re : ℂ)).re : ℂ) = φ (z.re : ℂ) := by apply Complex.ext <;> simp [hφim]
    have he := hHr z.re (φ (z.re : ℂ)).re
    rw [hφr,hg] at he
    have he' : q (p+z.re • u+(φ (z.re : ℂ)).re • v)-1 = 0 :=
      Complex.ofReal_injective he.symm
    simpa only [χ,Complex.real_smul,hφr] using sub_eq_zero.mp he'
  have hqa : AnalyticAt ℝ q p := convexBarrier_analytic c l a p
  have hqχa : AnalyticAt ℝ (q ∘ χ) 0 := hqa.comp_of_eq (hχa.restrictScalars) hχ0
  have hqD : HasFDerivAt q D (χ 0) := by simpa only [hχ0] using hqa.differentiableAt.hasFDerivAt
  have hqχD : HasFDerivAt (q ∘ χ) (d • Complex.imCLM) 0 := by
    convert! hqD.comp 0 (hχD.hasFDerivAt.restrictScalars ℝ) using 1
    apply ContinuousLinearMap.ext
    intro z
    change d*z.im = D (z*u)
    exact (hDmul z).symm
  have hstrict : HasStrictFDerivAt (q ∘ χ) (d • Complex.imCLM) 0 := by
    rw [← hqχD.fderiv]
    exact hqχa.hasStrictFDerivAt
  have hside := local_normal_side hd hstrict haxis
  refine ⟨χ,hχ0,hχa,hχne,?_,?_,?_⟩
  · filter_upwards [hside] with z hz
    exact hz.1
  · filter_upwards [hside] with z hz
    intro him
    rw [convexOn_frontier_sublevel (convexBarrier_convex hc l a) (convexBarrier_continuous c l a) hx]
    exact hz.2 him

  · exact local_normal_le_side hd hstrict haxis

lemma convexBarrier_analytic_chart {ι : Type u_25} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) {x p : ℂ}
    (hx : convexBarrier c l a x < 1) (hp : convexBarrier c l a p = 1) :
    ∃ ψ : ℂ → ℂ, ψ 0 = p ∧ AnalyticOnNhd ℂ ψ (ball 0 2) ∧
      InjOn ψ (ball 0 2) ∧ (∀ z ∈ ball 0 2, deriv ψ z ≠ 0) ∧
      (∀ z ∈ ball 0 2, ψ z ∈ {w | convexBarrier c l a w < 1} ↔ 0 < z.im) ∧
      (∀ z ∈ ball 0 2, z.im = 0 → ψ z ∈ frontier {w | convexBarrier c l a w < 1}) := by
  obtain ⟨χ,hχ0,ha,hd,hs,hb⟩ := convexBarrier_local_analytic_chart hc l a hx hp
  obtain ⟨ψ,hψ0,ha,hi,hd,hs,hb⟩ := analytic_chart_rescale ha hd hs hb
  exact ⟨ψ,hψ0.trans hχ0,ha,hi,hd,hs,hb⟩

end

open Set Filter Metric Complex
open scoped Topology
section

def invertedExterior (K : Set ℂ) (a : ℂ) : Set ℂ :=
  {w | w = 0 ∨ a+w⁻¹ ∉ K}

@[simp] lemma zero_mem_invertedExterior (K : Set ℂ) (a : ℂ) :
    0 ∈ invertedExterior K a := Or.inl rfl

lemma invertedExterior_open {K : Set ℂ} {a : ℂ}
    (hK : IsCompact K) : IsOpen (invertedExterior K a) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  by_cases hw0 : w = 0
  · subst w
    obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℂ)
    let r : ℝ := (R+‖a‖+1)⁻¹
    have hden : 0 < R+‖a‖+1 := by positivity
    have hr : 0 < r := inv_pos.mpr hden
    apply mem_of_superset (ball_mem_nhds 0 hr)
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      intro hk
      have he := mem_ball_zero_iff.mp (hKR hk)
      have hb := norm_sub_le (a+z⁻¹) a
      have hl : R+‖a‖+1 < ‖z⁻¹‖ := by
        rw [norm_inv]
        have hz' : ‖z‖ < (R+‖a‖+1)⁻¹ := mem_ball_zero_iff.mp hz
        exact (lt_inv_comm₀ hden (norm_pos_iff.mpr hz0)).mpr hz'
      have hsub : a+z⁻¹-a = z⁻¹ := by ring
      rw [hsub] at hb
      linarith
  · have hw := hw.resolve_left hw0
    have hc : ContinuousAt (fun z : ℂ => a+z⁻¹) w := continuousAt_const.add (continuousAt_inv₀ hw0)
    exact mem_of_superset (hc.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hw))
      (fun z hz => Or.inr hz)

lemma invertedExterior_bounded {K : Set ℂ} {a : ℂ}
    (ha : a ∈ interior K) : Bornology.IsBounded (invertedExterior K a) := by
  obtain ⟨r,hr,hrK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := r⁻¹)).subset
  intro w hw
  rw [mem_closedBall_zero_iff]
  by_cases hw0 : w = 0
  · simp [hw0,hr.le]
  · by_contra hn
    have hn' : r⁻¹ < ‖w‖ := lt_of_not_ge hn
    apply hw.resolve_left hw0
    apply hrK
    rw [mem_ball,dist_eq_norm]
    have he : a+w⁻¹-a = w⁻¹ := by ring
    rw [he,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr hw0) hr).mpr hn'

lemma invertedExterior_starConvex {K : Set ℂ} {a : ℂ}
    (hK : Convex ℝ K) (ha : a ∈ K) : StarConvex ℝ 0 (invertedExterior K a) := by
  intro w hw s t hs ht hst
  simp only [smul_zero,zero_add]
  by_cases ht0 : t = 0
  · simp [ht0]
  by_cases hw0 : w = 0
  · simp [hw0]
  right
  intro hz
  apply hw.resolve_left hw0
  have ht1 : t ≤ 1 := by linarith
  have hb := hK ha hz (sub_nonneg.mpr ht1) ht (by ring : 1-t+t=1)
  convert hb using 1
  simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  field_simp [htc, hw0]
  ring

lemma invertedExterior_simplyConnected {K : Set ℂ} {a : ℂ}
    (hK : Convex ℝ K) (ha : a ∈ K) : SimplyConnectedSpace (invertedExterior K a) := by
  let := (invertedExterior_starConvex hK ha).contractibleSpace ⟨0,zero_mem_invertedExterior K a⟩
  infer_instance

lemma invertedExterior_frontier {U : Set ℂ} {a p : ℂ}
    (hU : IsOpen U) (hK : IsCompact (closure U)) (_ha : a ∈ U)
    (hp : p ∈ frontier (invertedExterior (closure U) a)) :
    p ≠ 0 ∧ a+p⁻¹ ∈ frontier U := by
  have hV := invertedExterior_open (a := a) hK
  have hpnot : p ∉ invertedExterior (closure U) a := by rw [hV.frontier_eq] at hp; exact hp.2
  have hp0 : p ≠ 0 := fun he => hpnot (he ▸ zero_mem_invertedExterior (closure U) a)
  have hpK : a+p⁻¹ ∈ closure U := not_not.mp (fun hn => hpnot (Or.inr hn))
  refine ⟨hp0,?_⟩
  rw [hU.frontier_eq]
  refine ⟨hpK,?_⟩
  intro hpu
  have hc : ContinuousAt (fun z : ℂ => a+z⁻¹) p := continuousAt_const.add (continuousAt_inv₀ hp0)
  have he := hc.preimage_mem_nhds (hU.mem_nhds hpu)
  have hne : ∀ᶠ z : ℂ in 𝓝 p, z ≠ 0 := eventually_ne_nhds hp0
  have hass : ∀ᶠ z : ℂ in 𝓝 p, z ∉ invertedExterior (closure U) a := by
    filter_upwards [he,hne] with z hz hn
    exact fun h => h.resolve_left hn (subset_closure hz)
  exact (mem_closure_iff_frequently.mp hp.1).and_eventually hass |>.exists |>.elim
    (fun z hz => hz.2 hz.1)


lemma local_side_frontier {U : Set ℂ} (hU : IsOpen U) {χ : ℂ → ℂ}
    (ha : ∀ᶠ z : ℂ in 𝓝 0, ContinuousAt χ z)
    (hs : ∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im) :
    ∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U := by
  obtain ⟨r,hr,hrall⟩ := Metric.mem_nhds_iff.mp (ha.and hs)
  apply mem_of_superset (ball_mem_nhds 0 hr)
  intro z hz him
  rw [hU.frontier_eq]
  refine ⟨?_,fun h => by simpa [him] using (hrall hz).2.mp h⟩
  have hzc : z ∈ closure {w : ℂ | 0 < w.im} := by simp [him]
  have hzbc : z ∈ closure (ball (0 : ℂ) r ∩ {w : ℂ | 0 < w.im}) :=
    mem_closure_iff_frequently.mpr (((mem_closure_iff_frequently.mp hzc).and_eventually
      (isOpen_ball.mem_nhds hz)).mono (fun w hw => ⟨hw.2,hw.1⟩))
  have he := mem_closure_image (hrall hz).1 hzbc
  exact closure_mono (by rintro w ⟨v,hv,rfl⟩; exact (hrall hv.1).2.mpr hv.2) he
end

lemma invertedExterior_mem_closure_iff {K : Set ℂ} {a w : ℂ} (hw : w ≠ 0) :
    w ∈ closure (invertedExterior K a) ↔ a+w⁻¹ ∉ interior K := by
  constructor
  · intro h hib
    have hc : ContinuousAt (fun z : ℂ => a+z⁻¹) w := continuousAt_const.add (continuousAt_inv₀ hw)
    have hb := hc.preimage_mem_nhds (isOpen_interior.mem_nhds hib)
    have hn := eventually_ne_nhds hw
    have he : ∀ᶠ z : ℂ in 𝓝 w, z ∉ invertedExterior K a := by
      filter_upwards [hb,hn] with z hz hzn
      exact fun h => h.resolve_left hzn (interior_subset hz)
    obtain ⟨z,hz,hzn⟩ := ((mem_closure_iff_frequently.mp h).and_eventually he).exists
    exact hzn hz
  · intro h
    have hc : ContinuousAt (fun z : ℂ => (z-a)⁻¹) (a+w⁻¹) :=
      (continuousAt_id.sub continuousAt_const).inv₀ (by simpa using inv_ne_zero hw)
    have hz : a+w⁻¹ ∈ closure Kᶜ := by simpa only [closure_compl,mem_compl_iff] using h
    have he := mem_closure_image hc hz
    have hsub : (fun z : ℂ => (z-a)⁻¹) '' Kᶜ ⊆ invertedExterior K a := by
      rintro z ⟨v,hv,rfl⟩
      right
      simpa only [inv_inv,add_sub_cancel,mem_compl_iff] using hv
    have hm := closure_mono hsub he
    simpa using hm

lemma invertedExterior_frontier_iff {U : Set ℂ} {a w : ℂ}
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hreg : interior (closure U) = U)
    (hw : w ≠ 0) :
    w ∈ frontier (invertedExterior (closure U) a) ↔ a+w⁻¹ ∈ frontier U := by
  rw [(invertedExterior_open (a := a) hK).frontier_eq,hU.frontier_eq]
  change (w ∈ closure (invertedExterior (closure U) a) ∧ ¬ (w=0 ∨ a+w⁻¹ ∉ closure U)) ↔ _
  rw [invertedExterior_mem_closure_iff hw,hreg,or_iff_right hw]
  simp only [not_not,Set.mem_sdiff]
  exact and_comm

end CompleteCrouzeix

end

end OAI
