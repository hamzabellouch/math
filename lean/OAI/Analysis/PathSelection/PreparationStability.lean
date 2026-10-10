import Mathlib
import OAI.Analysis.PathSelection.JointPreparation
import OAI.Analysis.PathSelection.PreparationLimits

namespace OAI

/-! Normalized preparation stability and common parameter domains. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

namespace PathSelection.PreparationLimit

open PathSelection.Preparation

theorem normalized_preparation_stability {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {r : ℝ} {d : ℕ}
    (hU : IsOpen U) (hr : 0<r) (hKU : closedBall (0:ℂ) r⊆U)
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) U)
    (hf : AnalyticOnNhd ℂ f U)
    (hnz : ∀ z∈sphere (0:ℂ) r, f z≠0)
    (hcount : contourPowerSum f r 0=(d:ℂ))
    (h : TendstoLocallyUniformlyOn F f l U) :
    let W := fun i => preparationPolynomial (F i) r d
    let W₀ := preparationPolynomial f r d
    (∀ᶠ i in l, (W i).Monic ∧ (W i).natDegree=d ∧
      (∀ z : ℂ, (W i).eval z=0 → z∈ball 0 r) ∧
      AnalyticOnNhd ℂ (divisionQuotient (F i) (W i) r) (ball 0 r) ∧
      (∀ z∈ball (0:ℂ) r, divisionQuotient (F i) (W i) r z≠0) ∧
      EqOn (F i) (fun z => (W i).eval z * divisionQuotient (F i) (W i) r z) (ball 0 r)) ∧
    (∀ k, Tendsto (fun i => (W i).coeff k) l (𝓝 (W₀.coeff k))) ∧
    TendstoLocallyUniformlyOn (fun i z => (W i).eval z) W₀.eval l univ ∧
    TendstoLocallyUniformlyOn (fun i z => divisionQuotient (F i) (W i) r z)
      (divisionQuotient f W₀ r) l (ball 0 r) := by
  dsimp only
  have hSU : sphere (0:ℂ) r⊆U := sphere_subset_closedBall.trans hKU
  have hlim := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_sphere (0:ℂ) r)).mp (h.mono hSU)
  have hFn := eventual_uniform_nonzero (isCompact_sphere (0:ℂ) r)
    (hf.continuousOn.mono hSU) hnz hlim
  have hFc := eventually_count_eq hr (hF.mono (fun i hi => hi.mono hKU))
    (hf.mono hKU) hnz hlim
  have hsp := tendstoPowerSum hU hr hSU hF hf hnz h
  have hwlim := tendsto_preparation_eval hsp d
  have hfprep := fixed_contour_preparation_of_count hr (hf.mono hKU) hnz hcount
  have hWnz : ∀ z∈sphere (0:ℂ) r, (preparationPolynomial f r d).eval z≠0 := by
    intro z hz he
    exact (ne_of_lt (mem_ball_zero_iff.mp (hfprep.2.2.1 z he)))
      (mem_sphere_zero_iff_norm.mp hz)
  refine ⟨?_,tendsto_preparation_coeff hsp d,hwlim,?_⟩
  · filter_upwards [hF,hFn,hFc] with i hi hin hic
    exact fixed_contour_preparation_of_count hr (hi.mono hKU) hin (hic.trans hcount)
  · exact tendsto_divisionQuotient hr
      (hF.mono (fun i hi => hi.continuousOn.mono hSU))
      (hf.continuousOn.mono hSU) hWnz hlim
      ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        (isCompact_sphere (0:ℂ) r)).mp (hwlim.mono (subset_univ _)))

 

theorem normalized_division_stability {ι : Type*} {l : Filter ι}
    {F G : ι → ℂ → ℂ} {f g : ℂ → ℂ} {U : Set ℂ} {r : ℝ} {d : ℕ}
    (hU : IsOpen U) (hr : 0<r) (hKU : closedBall (0:ℂ) r⊆U)
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) U)
    (hf : AnalyticOnNhd ℂ f U)
    (hnz : ∀ z∈sphere (0:ℂ) r, f z≠0)
    (hcount : contourPowerSum f r 0=(d:ℂ))
    (h : TendstoLocallyUniformlyOn F f l U)
    (hG : ∀ᶠ i in l, AnalyticOnNhd ℂ (G i) U)
    (hg : AnalyticOnNhd ℂ g U)
    (h' : TendstoLocallyUniformlyOn G g l U) :
    let W := fun i => preparationPolynomial (F i) r d
    let W₀ := preparationPolynomial f r d
    TendstoLocallyUniformlyOn (fun i z => divisionQuotient (G i) (W i) r z)
      (divisionQuotient g W₀ r) l (ball 0 r) ∧
    (∀ k, Tendsto (fun i => (divisionRemainder (G i) (W i) r).coeff k) l
      (𝓝 ((divisionRemainder g W₀ r).coeff k))) ∧
    (∀ᶠ i in l,
      (divisionRemainder (G i) (W i) r).degree<d ∧
      EqOn (G i) (fun z => (W i).eval z * divisionQuotient (G i) (W i) r z +
        (divisionRemainder (G i) (W i) r).eval z) (ball 0 r)) := by
  dsimp only
  obtain ⟨hprep,hcoeff,hwlim,hunit⟩ := normalized_preparation_stability
    hU hr hKU hF hf hnz hcount h
  have hfprep := fixed_contour_preparation_of_count hr (hf.mono hKU) hnz hcount
  have hWnz : ∀ z∈sphere (0:ℂ) r, (preparationPolynomial f r d).eval z≠0 := by
    intro z hz he
    exact (ne_of_lt (mem_ball_zero_iff.mp (hfprep.2.2.1 z he)))
      (mem_sphere_zero_iff_norm.mp hz)
  have hSU : sphere (0:ℂ) r⊆U := sphere_subset_closedBall.trans hKU
  have hlimG := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_sphere (0:ℂ) r)).mp (h'.mono hSU)
  have hlimW := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_sphere (0:ℂ) r)).mp (hwlim.mono (subset_univ _))
  have hGcont := hG.mono (fun i hi => hi.continuousOn.mono hSU)
  have hgcont := hg.continuousOn.mono hSU
  refine ⟨tendsto_divisionQuotient hr hGcont hgcont hWnz hlimG hlimW,?_,?_⟩
  · exact tendsto_divisionRemainder_coeff hr hGcont hgcont hWnz hlimG hlimW hcoeff
      (hprep.mono (fun i hi => hi.2.1.trans hfprep.2.1.symm))
  · filter_upwards [hprep,hG] with i hi hiG
    have hiWnz : ∀ z∈sphere (0:ℂ) r, (preparationPolynomial (F i) r d).eval z≠0 := by
      intro z hz he
      exact (ne_of_lt (mem_ball_zero_iff.mp (hi.2.2.1 z he)))
        (mem_sphere_zero_iff_norm.mp hz)
    have hdiv := fixed_disc_division (G := G i)
      (P := preparationPolynomial (F i) r d) hr (hiG.mono hKU) hiWnz
    refine ⟨?_,hdiv.2.2⟩
    simpa only [hi.2.1] using hdiv.2.1

 

theorem normalized_unit_all_orders {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} {r : ℝ} {d : ℕ}
    (hU : IsOpen U) (hr : 0<r) (hKU : closedBall (0:ℂ) r⊆U)
    (hF : ∀ᶠ i in l, AnalyticOnNhd ℂ (F i) U)
    (hf : AnalyticOnNhd ℂ f U)
    (hnz : ∀ z∈sphere (0:ℂ) r, f z≠0)
    (hcount : contourPowerSum f r 0=(d:ℂ))
    (h : TendstoLocallyUniformlyOn F f l U) :
    let Q := fun i => divisionQuotient (F i) (preparationPolynomial (F i) r d) r
    let Q₀ := divisionQuotient f (preparationPolynomial f r d) r
    (∀ᶠ i in l, ∀ n, AnalyticOnNhd ℂ (iteratedDeriv n (Q i)) (ball 0 r)) ∧
    (∀ n, TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (Q i))
      (iteratedDeriv n Q₀) l (ball 0 r)) := by
  dsimp only
  have hp := normalized_preparation_stability hU hr hKU hF hf hnz hcount h
  have hqa := hp.1.mono (fun i hi => hi.2.2.2.1)
  exact ⟨hqa.mono (fun i hi n => analyticOnNhd_iteratedDeriv hi n),
    tendstoLocallyUniformlyOn_iteratedDeriv isOpen_ball hqa hp.2.2.2⟩

 

theorem joint_preparation_from_regular_germ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {F : E × ℂ → ℂ} {a₀ : E} {d : ℕ}
    (hF : AnalyticAt ℂ F (a₀,0))
    (horder : analyticOrderAt (fun z => F (a₀,z)) 0=(d:ℕ∞)) :
    ∃ δ r : ℝ, 0<δ ∧ 0<r ∧
      let U := ball a₀ δ
      let W := fun a => preparationPolynomial (fun z => F (a,z)) r d
      let u := fun p : E × ℂ => divisionQuotient (fun z => F (p.1,z)) (W p.1) r p.2
      (∀ a∈U, (W a).Monic ∧ (W a).natDegree=d ∧
        ∀ z, (W a).eval z=0 → z∈ball 0 r) ∧
      (∀ n, AnalyticOnNhd ℂ (fun a => (W a).coeff n) U) ∧
      AnalyticOnNhd ℂ (fun p : E × ℂ => (W p.1).eval p.2) (U ×ˢ univ) ∧
      AnalyticOnNhd ℂ u (U ×ˢ ball 0 r) ∧
      (∀ p∈U ×ˢ ball (0:ℂ) r, u p≠0) ∧
      EqOn F (fun p => (W p.1).eval p.2*u p) (U ×ˢ ball 0 r) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨S,hS,T,hT,hST⟩ := mem_nhds_prod_iff.mp hF.eventually_analyticAt
  obtain ⟨ε,hε,hεS⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨ρ,hρ,hρT⟩ := Metric.mem_nhds_iff.mp hT
  have hFa : AnalyticOnNhd ℂ F (ball a₀ ε ×ˢ ball 0 ρ) := by
    intro p hp
    exact hST ⟨hεS hp.1,hρT hp.2⟩
  have hf : AnalyticAt ℂ (fun z => F (a₀,z)) 0 :=
    hF.comp (analyticAt_const.prod analyticAt_id)
  obtain ⟨r,hr,hrρ,hfr,hnz,hcount⟩ := exists_preparation_circle
    (isOpen_ball.mem_nhds (mem_ball_self hρ)) hf horder
  have hev : ∀ᶠ a in 𝓝 a₀, ∀ z∈sphere (0:ℂ) r, F (a,z)≠0 := by
    apply (isCompact_sphere (0:ℂ) r).eventually_forall_of_forall_eventually
    intro z hz
    exact (hFa (a₀,z) ⟨mem_ball_self hε,hrρ (sphere_subset_closedBall hz)⟩).continuousAt.eventually_ne
      (hnz z hz)
  have hb : ∀ᶠ a in 𝓝 a₀, a∈ball a₀ ε := isOpen_ball.mem_nhds (mem_ball_self hε)
  have hev' : ∀ᶠ a in 𝓝 a₀, a∈ball a₀ ε ∧ ∀ z∈sphere (0:ℂ) r, F (a,z)≠0 :=
    hb.and hev
  obtain ⟨δ,hδ,hδs⟩ := Metric.mem_nhds_iff.mp hev'
  have hF' : AnalyticOnNhd ℂ F (ball a₀ δ ×ˢ closedBall 0 r) := by
    intro p hp
    exact hFa p ⟨(hδs hp.1).1,hrρ hp.2⟩
  have hnz' : ∀ p∈ball a₀ δ ×ˢ sphere (0:ℂ) r, F p≠0 := by
    intro p hp
    exact (hδs hp.1).2 p.2 hp.2
  have hp := JointPreparation.joint_fixed_contour_preparation isOpen_ball
    (convex_ball a₀ δ).isPreconnected (mem_ball_self hδ) hr hF' hnz' hcount
  refine ⟨δ,r,hδ,hr,hp.1,?_,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
  exact JointPreparation.analyticOnNhd_preparation_coeff isOpen_ball hr.le
    (hF'.mono (prod_mono Subset.rfl sphere_subset_closedBall)) hnz' d

 

theorem common_preparation_domain {E J : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [Finite J] {F : E × ℂ → ℂ} {G : J → E × ℂ → ℂ}
    {a₀ : E} {d : ℕ} (hF : AnalyticAt ℂ F (a₀,0))
    (hG : ∀ j, AnalyticAt ℂ (G j) (a₀,0))
    (horder : analyticOrderAt (fun z => F (a₀,z)) 0=(d:ℕ∞)) :
    ∃ δ r : ℝ, 0<δ ∧ 0<r ∧
      AnalyticOnNhd ℂ F (ball a₀ δ ×ˢ closedBall 0 r) ∧
      (∀ j, AnalyticOnNhd ℂ (G j) (ball a₀ δ ×ˢ closedBall 0 r)) ∧
      (∀ p∈ball a₀ δ ×ˢ sphere (0:ℂ) r, F p≠0) ∧
      contourPowerSum (fun z => F (a₀,z)) r 0=(d:ℂ) := by
  have hGa : ∀ᶠ p in 𝓝 (a₀,(0:ℂ)), ∀ j, AnalyticAt ℂ (G j) p :=
    Filter.eventually_all.mpr (fun j => (hG j).eventually_analyticAt)
  obtain ⟨S,hS,T,hT,hST⟩ := mem_nhds_prod_iff.mp (hF.eventually_analyticAt.and hGa)
  obtain ⟨ε,hε,hεS⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨ρ,hρ,hρT⟩ := Metric.mem_nhds_iff.mp hT
  have hFa : AnalyticOnNhd ℂ F (ball a₀ ε ×ˢ ball 0 ρ) := by
    intro p hp
    exact (hST ⟨hεS hp.1,hρT hp.2⟩).1
  have hGa' : ∀ j, AnalyticOnNhd ℂ (G j) (ball a₀ ε ×ˢ ball 0 ρ) := by
    intro j p hp
    exact (hST ⟨hεS hp.1,hρT hp.2⟩).2 j
  have hf : AnalyticAt ℂ (fun z => F (a₀,z)) 0 :=
    hF.comp (analyticAt_const.prod analyticAt_id)
  obtain ⟨r,hr,hrρ,hfr,hnz,hcount⟩ := exists_preparation_circle
    (isOpen_ball.mem_nhds (mem_ball_self hρ)) hf horder
  have hev : ∀ᶠ a in 𝓝 a₀, ∀ z∈sphere (0:ℂ) r, F (a,z)≠0 := by
    apply (isCompact_sphere (0:ℂ) r).eventually_forall_of_forall_eventually
    intro z hz
    exact (hFa (a₀,z) ⟨mem_ball_self hε,hrρ (sphere_subset_closedBall hz)⟩).continuousAt.eventually_ne
      (hnz z hz)
  have hb : ∀ᶠ a in 𝓝 a₀, a∈ball a₀ ε := isOpen_ball.mem_nhds (mem_ball_self hε)
  obtain ⟨δ,hδ,hδs⟩ := Metric.mem_nhds_iff.mp (hb.and hev)
  refine ⟨δ,r,hδ,hr,?_,?_,?_,hcount⟩
  · intro p hp
    exact hFa p ⟨(hδs hp.1).1,hrρ hp.2⟩
  · intro j p hp
    exact hGa' j p ⟨(hδs hp.1).1,hrρ hp.2⟩
  · intro p hp
    exact (hδs hp.1).2 p.2 hp.2

 

theorem joint_preparation_and_divisions_from_germs {E J : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [Finite J] {F : E × ℂ → ℂ} {G : J → E × ℂ → ℂ}
    {a₀ : E} {d : ℕ} (hF : AnalyticAt ℂ F (a₀,0))
    (hG : ∀ j, AnalyticAt ℂ (G j) (a₀,0))
    (horder : analyticOrderAt (fun z => F (a₀,z)) 0=(d:ℕ∞)) :
    ∃ δ r : ℝ, 0<δ ∧ 0<r ∧
      let U := ball a₀ δ
      let W := fun a => preparationPolynomial (fun z => F (a,z)) r d
      let u := fun p : E × ℂ => divisionQuotient (fun z => F (p.1,z)) (W p.1) r p.2
      (∀ a∈U, (W a).Monic ∧ (W a).natDegree=d ∧
        ∀ z, (W a).eval z=0 → z∈ball 0 r) ∧
      (∀ n, AnalyticOnNhd ℂ (fun a => (W a).coeff n) U) ∧
      AnalyticOnNhd ℂ u (U ×ˢ ball 0 r) ∧
      (∀ p∈U ×ˢ ball (0:ℂ) r, u p≠0) ∧
      EqOn F (fun p => (W p.1).eval p.2*u p) (U ×ˢ ball 0 r) ∧
      (∀ j, let Q := fun p : E × ℂ => divisionQuotient (fun z => G j (p.1,z)) (W p.1) r p.2
        let R := fun a => divisionRemainder (fun z => G j (a,z)) (W a) r
        AnalyticOnNhd ℂ Q (U ×ˢ ball 0 r) ∧
        (∀ n, AnalyticOnNhd ℂ (fun a => (R a).coeff n) U) ∧
        (∀ a∈U, (R a).degree<d) ∧
        EqOn (G j) (fun p => (W p.1).eval p.2*Q p+(R p.1).eval p.2) (U ×ˢ ball 0 r)) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨δ,r,hδ,hr,hFa,hGa,hnz,hcount⟩ := common_preparation_domain hF hG horder
  have hp := JointPreparation.joint_fixed_contour_preparation isOpen_ball
    (convex_ball a₀ δ).isPreconnected (mem_ball_self hδ) hr hFa hnz hcount
  have hc := JointPreparation.analyticOnNhd_preparation_coeff isOpen_ball hr.le
    (hFa.mono (prod_mono Subset.rfl sphere_subset_closedBall)) hnz d
  refine ⟨δ,r,hδ,hr,hp.1,hc,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2,?_⟩
  intro j
  apply JointPreparation.joint_fixed_contour_division isOpen_ball hr (hGa j)
    (hp.2.1.mono (prod_mono Subset.rfl (subset_univ _))) hc
    (fun a ha => (hp.1 a ha).2.1)
  intro a ha z hz he
  exact (ne_of_lt (mem_ball_zero_iff.mp ((hp.1 a ha).2.2 z he)))
    (mem_sphere_zero_iff_norm.mp hz)

end PathSelection.PreparationLimit
end

end OAI
