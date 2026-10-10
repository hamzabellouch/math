import OAI.Analysis.NumericalRange.ConformalGluing

namespace OAI

noncomputable section

namespace CompleteCrouzeix

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
section

def diskAut (b z : ℂ) : ℂ := (z-b)/(1-star b*z)

lemma diskAut_den_ne {b z : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ < 1) :
    1-star b*z ≠ 0 := by
  have h : ‖star b*z‖ < 1 := by
    rw [norm_mul, norm_star]
    nlinarith [norm_nonneg b,norm_nonneg z]
  exact sub_ne_zero.mpr (by intro he; rw [← he, norm_one] at h; exact (lt_irrefl _ h))

lemma diskAut_normSq_identity (b z : ℂ) :
    Complex.normSq (1-star b*z)-Complex.normSq (z-b) =
      (1-Complex.normSq b)*(1-Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

lemma diskAut_maps {b z : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskAut b z‖ < 1 := by
  have hden := diskAut_den_ne hb hz
  have he := diskAut_normSq_identity b z
  simp only [Complex.normSq_eq_norm_sq] at he
  have hpos : 0 < (1-‖b‖^2)*(1-‖z‖^2) := by
    apply mul_pos <;> nlinarith [norm_nonneg b,norm_nonneg z]
  rw [diskAut, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  nlinarith [norm_nonneg (1-star b*z),norm_nonneg (z-b)]

lemma diskAut_inj {b : ℂ} (hb : ‖b‖ < 1) : InjOn (diskAut b) (ball 0 1) := by
  intro z hz w hw he
  rw [mem_ball_zero_iff] at hz hw
  have hdenz := diskAut_den_ne hb hz
  have hdenw := diskAut_den_ne hb hw
  have hbb := diskAut_den_ne hb hb
  have he' : (z-b)*(1-star b*w) = (w-b)*(1-star b*z) :=
    (div_eq_div_iff hdenz hdenw).mp he
  have hm : (1-star b*b)*(z-w) = 0 := by linear_combination he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hbb)

lemma diskAut_deriv {b z : ℂ} (hb : ‖b‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (diskAut b) ((1-star b*b)/(1-star b*z)^2) z := by
  have hd : HasDerivAt (diskAut b)
      ((1 * (1-star b*z)-(z-b)*(0-star b*1))/(1-star b*z)^2) z :=
    (((hasDerivAt_id z).sub_const b).div
      ((hasDerivAt_const z (1:ℂ)).sub ((hasDerivAt_id z).const_mul (star b)))
      (diskAut_den_ne hb hz))
  convert hd using 1 ; ring

lemma diskAut_zero (b : ℂ) : diskAut b 0 = -b := by simp [diskAut]
lemma diskAut_self (b : ℂ) : diskAut b b = 0 := by simp [diskAut]

lemma diskAut_deriv_zero_norm {b : ℂ} (hb : ‖b‖ < 1) :
    ‖deriv (diskAut b) 0‖ = 1-‖b‖^2 := by
  rw [(diskAut_deriv hb (by simp : ‖(0:ℂ)‖ < 1)).deriv]
  have he : star b*b = (‖b‖^2 : ℝ) := by
    change (starRingEnd ℂ) b*b = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [he]
  simp only [mul_zero, sub_zero, one_pow, div_one]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_of_nonneg]
  nlinarith [norm_nonneg b]

lemma diskAut_deriv_self_norm {b : ℂ} (hb : ‖b‖ < 1) :
    ‖deriv (diskAut b) b‖ = (1-‖b‖^2)⁻¹ := by
  rw [(diskAut_deriv hb hb).deriv]
  have hden := diskAut_den_ne hb hb
  have hs : (1-star b*b)/(1-star b*b)^2 = (1-star b*b)⁻¹ := by
    rw [pow_two, div_mul_eq_div_div, div_self hden, one_div]
  rw [hs,norm_inv]
  have hh := diskAut_deriv_zero_norm hb
  rw [(diskAut_deriv hb (by simp : ‖(0:ℂ)‖ < 1)).deriv] at hh
  simpa using congrArg Inv.inv hh

lemma holomorphic_square_root {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) :
    ∃ g, DifferentiableOn ℂ g U ∧ (∀ z, g z ^ 2 = f z) ∧
      ∀ z ∈ U, HasDerivAt g (deriv f z / (2*g z)) z := by
  obtain ⟨g,hgc,hg⟩ := Complex.exists_continuousOn_pow_eq hUc hU hf.continuousOn
    (by rintro ⟨z,hz,he⟩; exact hf0 z hz he) two_ne_zero
  have hg0 : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz he
    exact hf0 z hz (by rw [← hg z,he]; simp)
  have hd : ∀ z ∈ U, HasDerivAt g (deriv f z / (2*g z)) z := by
    intro z hz
    have hh := HasDerivAt.of_comp_left (hgc.continuousAt (hU.mem_nhds hz))
      (hasDerivAt_pow 2 (g z)) ((hf z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
      (by simpa using mul_ne_zero (two_ne_zero : (2:ℂ) ≠ 0) (hg0 z hz))
      (Eventually.of_forall hg)
    simpa using hh
  exact ⟨g,(fun z hz => (hd z hz).differentiableAt.differentiableWithinAt),hg,hd⟩


lemma square_root_improvement {U : Set ℂ} (hU : IsOpen U) (hUc : IsSimplyConnected U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedUnivalent U a f)
    (hdf : deriv f a ≠ 0) {b : ℂ} (hb : b ∈ ball 0 1) (hbout : b ∉ f '' U) :
    ∃ ψ, NormalizedUnivalent U a ψ ∧ ‖deriv f a‖ < ‖deriv ψ a‖ := by
  have hbn : ‖b‖ < 1 := mem_ball_zero_iff.mp hb
  have hfn : ∀ z ∈ U, ‖f z‖ < 1 := fun z hz => mem_ball_zero_iff.mp (hf.2.2.1 hz)
  have hb0 : b ≠ 0 := by
    intro he
    exact hbout ⟨a,ha,hf.2.2.2.trans he.symm⟩
  let k : ℂ → ℂ := diskAut b ∘ f
  have hkd : ∀ z ∈ U, HasDerivAt k
      (deriv (diskAut b) (f z) * deriv f z) z := by
    intro z hz
    exact (diskAut_deriv hbn (hfn z hz)).differentiableAt.hasDerivAt.comp z
      ((hf.1 z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hk : DifferentiableOn ℂ k U := fun z hz =>
    (hkd z hz).differentiableAt.differentiableWithinAt
  have hk0 : ∀ z ∈ U, k z ≠ 0 := by
    intro z hz he
    have : f z = b := sub_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right
      (diskAut_den_ne hbn (hfn z hz)))
    exact hbout ⟨z,hz,this⟩
  obtain ⟨g,hgd,hg,hgder⟩ := holomorphic_square_root hU hUc hk hk0
  have hgn : ∀ z ∈ U, ‖g z‖ < 1 := by
    intro z hz
    have he : ‖g z‖^2 = ‖k z‖ := by simpa only [norm_pow] using congrArg norm (hg z)
    have hklt : ‖k z‖ < 1 := diskAut_maps hbn (hfn z hz)
    nlinarith [norm_nonneg (g z)]
  have hginj : InjOn g U := by
    intro z hz w hw he
    apply hf.2.1 hz hw
    apply diskAut_inj hbn (hf.2.2.1 hz) (hf.2.2.1 hw)
    change k z = k w
    rw [← hg z, ← hg w,he]
  let β := g a
  have hβ : ‖β‖ < 1 := hgn a ha
  have hβsq : ‖β‖^2 = ‖b‖ := by
    have he := congrArg norm (hg a)
    simpa only [norm_pow,k,Function.comp_apply,hf.2.2.2,diskAut_zero,norm_neg] using he
  have hβpos : 0 < ‖β‖ := by
    have := norm_pos_iff.mpr hb0
    nlinarith [norm_nonneg β]
  let ψ : ℂ → ℂ := diskAut β ∘ g
  have hψder : ∀ z ∈ U, HasDerivAt ψ
      (deriv (diskAut β) (g z) * deriv g z) z := by
    intro z hz
    exact (diskAut_deriv hβ (hgn z hz)).differentiableAt.hasDerivAt.comp z
      ((hgd z hz).differentiableAt (hU.mem_nhds hz)).hasDerivAt
  refine ⟨ψ,⟨(fun z hz => (hψder z hz).differentiableAt.differentiableWithinAt),?_,?_,?_⟩,?_⟩
  · exact (diskAut_inj hβ).comp hginj (fun z hz => mem_ball_zero_iff.mpr (hgn z hz))
  · intro z hz
    exact mem_ball_zero_iff.mpr (diskAut_maps hβ (hgn z hz))
  · exact diskAut_self β
  · have hkda : ‖deriv k a‖ = (1-‖b‖^2)*‖deriv f a‖ := by
      rw [(hkd a ha).deriv,norm_mul,hf.2.2.2,diskAut_deriv_zero_norm hbn]
    have he : ‖deriv ψ a‖ = (1-‖β‖^2)⁻¹ *
        ((1-‖b‖^2)*‖deriv f a‖/(2*‖β‖)) := by
      rw [(hψder a ha).deriv,norm_mul]
      change ‖deriv (diskAut β) β‖ * ‖deriv g a‖ = _
      rw [diskAut_deriv_self_norm hβ,(hgder a ha).deriv,norm_div,norm_mul]
      rw [hkda]
      norm_num [β]
    have hpos : 0 < 1-‖β‖^2 := by nlinarith [norm_nonneg β]
    have hratio : (1-‖β‖^2)⁻¹ * ((1-‖b‖^2)*‖deriv f a‖/(2*‖β‖)) =
        ((1+‖β‖^2)/(2*‖β‖))*‖deriv f a‖ := by
      rw [← hβsq]
      field_simp
      ring
    rw [he,hratio]
    have hr : 1 < (1+‖β‖^2)/(2*‖β‖) := by
      rw [one_lt_div (by positivity)]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hβ)]
    exact lt_mul_of_one_lt_left (norm_pos_iff.mpr hdf) hr

theorem bounded_riemann_mapping {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hUb : Bornology.IsBounded U) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedUnivalent U a f ∧ deriv f a ≠ 0 ∧ f '' U = ball 0 1 := by
  obtain ⟨f,hf,hdf,hext⟩ := exists_extremal_univalent hU
    hUc.isPathConnected.isConnected.isPreconnected hUb ha
  refine ⟨f,hf,hdf,Subset.antisymm hf.2.2.1.image_subset ?_⟩
  intro b hb
  by_contra hbout
  obtain ⟨ψ,hψ,hlt⟩ := square_root_improvement hU hUc ha hf hdf hb hbout
  exact not_lt_of_ge (hext ψ hψ) hlt

end

open Set Filter Topology Complex

section

theorem partialHomeomorph_analytic_inverse
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : AnalyticOnNhd ℂ (e : ℂ → ℂ) e.source)
    (hconn : IsPreconnected e.source) {a : ℂ} (ha : a ∈ e.source)
    (hda : deriv (e : ℂ → ℂ) a ≠ 0) :
    AnalyticOnNhd ℂ (e.symm : ℂ → ℂ) e.target := by
  intro w hw
  let z := e.symm w
  have hz : z ∈ e.source := e.map_target hw
  have hzw : e z = w := e.right_inv hw
  have hcrit : ∀ᶠ u in 𝓝[≠] z, deriv (e : ℂ → ℂ) u ≠ 0 := by
    rcases (he.deriv z hz).eventually_eq_zero_or_eventually_ne_zero with hc | hc
    · exfalso
      exact hda (he.deriv.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz hc ha)
    · exact hc
  have hinv : Tendsto (e.symm : ℂ → ℂ) (𝓝[≠] w) (𝓝[≠] z) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(e.continuousAt_symm hw).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    simpa only [mem_compl_iff, mem_singleton_iff, z] using e.symm.eventually_ne_nhdsWithin hw
  have hne := hinv.eventually hcrit
  have hmem : ∀ᶠ u in 𝓝[≠] w, u ∈ e.target :=
    eventually_nhdsWithin_of_eventually_nhds (e.open_target.mem_nhds hw)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _
    (e.continuousAt_symm hw)
  filter_upwards [hne, hmem] with u hdu hu
  have hv := e.map_target hu
  have hi := (he (e.symm u) hv).hasStrictDerivAt.to_local_left_inverse hdu
    (e.eventually_left_inverse hv)
  simpa only [e.right_inv hu] using hi.hasDerivAt.differentiableAt

theorem partialHomeomorph_deriv_ne_zero
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he : AnalyticOnNhd ℂ (e : ℂ → ℂ) e.source)
    (hconn : IsPreconnected e.source) {a : ℂ} (ha : a ∈ e.source)
    (hda : deriv (e : ℂ → ℂ) a ≠ 0) {z : ℂ} (hz : z ∈ e.source) :
    deriv (e : ℂ → ℂ) z ≠ 0 := by
  have hi := partialHomeomorph_analytic_inverse e he hconn ha hda
  have hc := (hi (e z) (e.map_source hz)).hasStrictDerivAt.hasDerivAt.comp z (he z hz).hasStrictDerivAt.hasDerivAt
  have heq : (e.symm ∘ e : ℂ → ℂ) =ᶠ[𝓝 z] id := e.eventually_left_inverse hz
  have hn : deriv (e.symm : ℂ → ℂ) (e z) * deriv (e : ℂ → ℂ) z = 1 :=
    (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
  intro h
  simp [h] at hn

theorem holomorphic_injective_inverse {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) (hinj : InjOn f U)
    {a : ℂ} (ha : a ∈ U) (hda : deriv f a ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (f '' U) ∧
      MapsTo g (f '' U) U ∧ (∀ z ∈ U, g (f z) = z) ∧
      (∀ w ∈ f '' U, f (g w) = w) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  classical
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) := by
    rcases hf.is_constant_or_isOpen hconn with hc | hc
    · rcases hc with ⟨c, hc⟩
      have heq : f =ᶠ[𝓝 a] fun _ => c :=
        (hU.eventually_mem ha).mono fun z hz => hc z hz
      exact False.elim (hda ((hasDerivAt_const a c).congr_of_eventuallyEq heq).deriv)
    · exact hc
  let e₀ := hinj.toPartialEquiv f U
  have ho : IsOpenMap (e₀.source.domRestrict e₀) := by
    intro s hs
    have hsub : (Subtype.val '' s : Set ℂ) ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact z.property
    have hh := hopen (Subtype.val '' s) hsub (hU.isOpenMap_subtype_val s hs)
    convert hh using 1
    exact (Set.image_image f Subtype.val s).symm
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict e₀ hf.continuousOn ho hU
  refine ⟨e.symm, partialHomeomorph_analytic_inverse e hf hconn ha hda,
    e.symm.mapsTo, ?_, ?_, ?_⟩
  · intro z hz
    exact e.left_inv hz
  · intro w hw
    exact e.right_inv hw
  · intro z hz
    exact partialHomeomorph_deriv_ne_zero e hf hconn ha hda hz

end

open Complex
lemma analytic_local_inverse_neighborhood {F : ℂ → ℂ} {p : ℂ}
    (ha : AnalyticAt ℂ F p) (hd : deriv F p ≠ 0) :
    ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧ IsOpen (F '' V) ∧
      ∃ ψ : ℂ → ℂ, AnalyticOnNhd ℂ ψ (F '' V) ∧
        (∀ z ∈ V, ψ (F z) = z) ∧ (∀ w ∈ F '' V, F (ψ w) = w) := by
  have he : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ F z ∧ deriv F z ≠ 0 ∧
      ha.hasStrictDerivAt.localInverse F (deriv F p) p hd (F z) = z := by
    filter_upwards [ha.eventually_analyticAt,ha.deriv.continuousAt.eventually_ne hd,
      ha.hasStrictDerivAt.eventually_left_inverse hd] with z hza hzd hze
    exact ⟨hza,hzd,hze⟩
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp he
  have hi : InjOn F (ball p r) := by
    intro x hx y hy hxy
    rw [← (hrV hx).2.2, ← (hrV hy).2.2,hxy]
  obtain ⟨ho,ψ,hψa,hψto,hψF,hFψ⟩ := noncritical_holomorphic_inverse
    isOpen_ball (fun z hz => (hrV hz).1) hi (fun z hz => (hrV hz).2.1)
  exact ⟨ball p r,isOpen_ball,mem_ball_self hr,ho,ψ,hψa,hψF,hFψ⟩

lemma conformal_extension_boundary_norm {U : Set ℂ} (hU : IsOpen U)
    {f g F : ℂ → ℂ} (hf : MapsTo f U (ball 0 1))
    (hg : ContinuousOn g (ball 0 1)) (hgU : MapsTo g (ball 0 1) U)
    (hgf : ∀ z ∈ U, g (f z) = z) (he : EqOn F f U)
    {p : ℂ} (hp : p ∈ frontier U) (hFc : ContinuousAt F p) : ‖F p‖ = 1 := by
  have := mem_closure_iff_nhdsWithin_neBot.mp hp.1
  have hlim := conformal_modulus_boundary hU hf hg hgU hgf hp
  have heq : (fun z => ‖F z‖) =ᶠ[𝓝[U] p] (fun z => ‖f z‖) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [he hz]
  exact tendsto_nhds_unique (hFc.norm.tendsto.mono_left nhdsWithin_le_nhds)
    (hlim.congr' heq.symm)

theorem conformal_inverse_boundary_limit {U : Set ℂ} (hU : IsOpen U)
    {F g : ℂ → ℂ} (hf : MapsTo F U (ball 0 1))
    (hgf : ∀ z ∈ U, g (F z) = z)
    (hb : ∀ z ∈ frontier U, ‖F z‖ = 1)
    {p : ℂ} (hp : p ∈ frontier U) (ha : AnalyticAt ℂ F p)
    (hd : deriv F p ≠ 0) : Tendsto g (𝓝[ball 0 1] (F p)) (𝓝 p) := by
  obtain ⟨V,hVo,hpV,hWo,ψ,hψa,hψF,hFψ⟩ := analytic_local_inverse_neighborhood ha hd
  have hpW : F p ∈ F '' V := ⟨p,hpV,rfl⟩
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hWo (F p) hpW
  let L := ball (F p) r ∩ ball (0 : ℂ) 1
  have hLc : IsPreconnected L := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hψc : ContinuousOn ψ L := hψa.continuousOn.mono (fun _ hz => hrW hz.1)
  have hpc : IsPreconnected (ψ '' L) := hLc.image ψ hψc
  have hmeet : (ψ '' L ∩ U).Nonempty := by
    have hN : V ∩ F ⁻¹' ball (F p) r ∈ 𝓝 p :=
      inter_mem (hVo.mem_nhds hpV) (ha.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr)))
    obtain ⟨z,hz,hzu⟩ := mem_closure_iff_nhds.mp hp.1 _ hN
    refine ⟨z,⟨F z,⟨hz.2,hf hzu⟩,hψF z hz.1⟩,hzu⟩
  have hto : MapsTo ψ L U := by
    have hs : ψ '' L ⊆ U := hpc.subset_of_closure_inter_subset hU hmeet (by
      rintro z ⟨hzc,ζ,hζ,rfl⟩
      by_contra hn
      have hzb : ψ ζ ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hzc,hn⟩
      have hh := hb _ hzb
      rw [hFψ ζ (hrW hζ.1)] at hh
      have hl := mem_ball_zero_iff.mp hζ.2
      linarith)
    exact fun z hz => hs ⟨z,hz,rfl⟩
  have he : g =ᶠ[𝓝[ball 0 1] (F p)] ψ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))] with z hz hzr
    have hh := hgf (ψ z) (hto ⟨hzr,hz⟩)
    rwa [hFψ z (hrW hzr)] at hh
  have hlim := (hψa _ hpW).continuousAt.tendsto.mono_left
    (show 𝓝[ball 0 1] (F p) ≤ 𝓝 (F p) from nhdsWithin_le_nhds)
  rw [hψF p hpV] at hlim
  exact hlim.congr' he.symm

theorem conformal_extension_injOn_closure {U : Set ℂ} (hU : IsOpen U)
    {F g : ℂ → ℂ} (hf : MapsTo F U (ball 0 1))
    (hgf : ∀ z ∈ U, g (F z) = z)
    (hb : ∀ z ∈ frontier U, ‖F z‖ = 1)
    (ha : AnalyticOnNhd ℂ F (closure U)) (hd : ∀ z ∈ closure U, deriv F z ≠ 0) :
    InjOn F (closure U) := by
  intro p hp q hq he
  by_cases hpu : p ∈ U
  · by_cases hqu : q ∈ U
    · rw [← hgf p hpu, ← hgf q hqu,he]
    · have hqb : q ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hq,hqu⟩
      have hh := mem_ball_zero_iff.mp (hf hpu)
      rw [he,hb q hqb] at hh
      exact (lt_irrefl _ hh).elim
  · have hpb : p ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hp,hpu⟩
    by_cases hqu : q ∈ U
    · have hh := mem_ball_zero_iff.mp (hf hqu)
      rw [← he,hb p hpb] at hh
      exact (lt_irrefl _ hh).elim
    · have hqb : q ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hq,hqu⟩
      have hFp : F p ∈ closure (ball (0 : ℂ) 1) := by
        rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
        simp [hb p hpb]
      have := mem_closure_iff_nhdsWithin_neBot.mp hFp
      have hlp := conformal_inverse_boundary_limit hU hf hgf hb hpb (ha p hp) (hd p hp)
      have hlq := conformal_inverse_boundary_limit hU hf hgf hb hqb (ha q hq) (hd q hq)
      rw [← he] at hlq
      exact tendsto_nhds_unique hlp hlq


end CompleteCrouzeix

end

end OAI
