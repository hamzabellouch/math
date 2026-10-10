import OAI.Analysis.NumericalRange.HerglotzReflection

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_1 u_2

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
section

theorem analytic_open_gluing {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g V)
    (he : EqOn f g (U ∩ V)) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q (U ∪ V) ∧ EqOn q f U ∧ EqOn q g V := by
  classical
  let q := fun z => if z ∈ U then f z else g z
  have hqf : EqOn q f U := fun _ hz => ite_eq_left hz
  have hqg : EqOn q g V := by
    intro z hz
    dsimp [q]
    split_ifs with hi
    · exact he ⟨hi,hz⟩
    · rfl
  refine ⟨q,?_,hqf,hqg⟩
  intro z hz
  rcases hz with hz | hz
  · apply (hf z hz).congr
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hqf hw).symm
  · apply (hg z hz).congr
    filter_upwards [hV.mem_nhds hz] with w hw
    exact (hqg hw).symm

theorem noncritical_holomorphic_inverse {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hinj : InjOn f U)
    (hd : ∀ z ∈ U, deriv f z ≠ 0) :
    IsOpen (f '' U) ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (f '' U) ∧
      MapsTo g (f '' U) U ∧ (∀ z ∈ U, g (f z) = z) ∧
      (∀ w ∈ f '' U, f (g w) = w) := by
  classical
  have hopen : ∀ s ⊆ U, IsOpen s → IsOpen (f '' s) := by
    intro s hsU hs
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z,hz,rfl⟩
    rw [← (hf z (hsU hz)).hasStrictDerivAt.map_nhds_eq (hd z (hsU hz))]
    exact image_mem_map (hs.mem_nhds hz)
  let e₀ := hinj.toPartialEquiv f U
  have ho : IsOpenMap (e₀.source.domRestrict e₀) := by
    intro s hs
    have hsub : (Subtype.val '' s : Set ℂ) ⊆ U := by
      rintro _ ⟨z,hz,rfl⟩
      exact z.property
    have hh := hopen (Subtype.val '' s) hsub (hU.isOpenMap_subtype_val s hs)
    convert hh using 1
    exact (Set.image_image f Subtype.val s).symm
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict e₀ hf.continuousOn ho hU
  have hg : AnalyticOnNhd ℂ (e.symm : ℂ → ℂ) e.target := by
    apply DifferentiableOn.analyticOnNhd _ e.open_target
    intro w hw
    have hz := e.map_target hw
    have hi := (hf (e.symm w) hz).hasStrictDerivAt.to_local_left_inverse
      (hd _ hz) (e.eventually_left_inverse hz)
    have hew : f (e.symm w) = w := e.right_inv hw
    rw [hew] at hi
    exact hi.hasDerivAt.differentiableAt.differentiableWithinAt
  exact ⟨hopen U Subset.rfl hU,e.symm,hg,e.symm.mapsTo,(fun z hz => e.left_inv hz),(fun w hw => e.right_inv hw)⟩


open Set Filter Metric Complex
open scoped Topology

theorem conformal_chart_extension {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f U)
    (hf : MapsTo f U (ball 0 1)) (hg : ContinuousOn g (ball 0 1))
    (hgU : MapsTo g (ball 0 1) U) (hgf : ∀ z ∈ U, g (f z) = z)
    {χ : ℂ → ℂ} (hχa : AnalyticOnNhd ℂ χ (ball 0 2))
    (hχi : InjOn χ (ball 0 2)) (hχd : ∀ z ∈ ball 0 2, deriv χ z ≠ 0)
    (hside : ∀ z ∈ ball 0 2, χ z ∈ U ↔ 0 < z.im)
    (hboundary : ∀ z ∈ ball 0 2, z.im = 0 → χ z ∈ frontier U)
    (hn : ∀ z ∈ upperClosedDisk, 0 < z.im → f (χ z) ≠ 0) :
    ∃ V : Set ℂ, IsOpen V ∧ χ 0 ∈ V ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F V ∧ deriv F (χ 0) ≠ 0 ∧
        EqOn F f (V ∩ U) := by
  have h12 : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
  have hca : ∀ z ∈ upperClosedDisk, 0 < z.im → AnalyticAt ℂ (f ∘ χ) z := by
    intro z hz him
    exact (hfa _ ((hside z (h12 hz.1)).mpr him)).comp (hχa z (h12 hz.1))
  obtain ⟨G,hGa,hGn,hGd,hGe⟩ := conformal_reflection_upperDisk hca hn
    (fun z hz him => mem_ball_zero_iff.mp (hf ((hside z (h12 hz.1)).mpr him))) (by
      intro p hp hpi
      have hp2 := h12 hp.1
      have hb := conformal_modulus_boundary hU hf hg hgU hgf (hboundary p hp2 hpi)
      apply hb.comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hχa p hp2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hp2)] with z him hz
      exact (hside z hz).mpr him)
  obtain ⟨ho,ψ,hψa,hψto,hψχ,hχψ⟩ := noncritical_holomorphic_inverse isOpen_ball hχa hχi hχd
  let V := χ '' ball (0 : ℂ) 1
  have hVsub : V ⊆ χ '' ball 0 2 := image_mono (ball_subset_ball (by norm_num))
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z,hz,rfl⟩
    have hz2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hz
    rw [← (hχa z hz2).hasStrictDerivAt.map_nhds_eq (hχd z hz2)]
    exact image_mem_map (isOpen_ball.mem_nhds hz)
  have h02 : (0 : ℂ) ∈ ball 0 2 := by simp
  have hψ0 : ψ (χ 0) = 0 := hψχ 0 h02
  have hpV : χ 0 ∈ V := ⟨0,by simp,rfl⟩
  have hψd : deriv ψ (χ 0) ≠ 0 := by
    have hc := ((hψa _ (hVsub hpV)).differentiableAt.hasDerivAt).comp 0
      ((hχa 0 h02).differentiableAt.hasDerivAt)
    have he : (ψ ∘ χ) =ᶠ[𝓝 (0 : ℂ)] id := by
      filter_upwards [isOpen_ball.mem_nhds h02] with z hz
      exact hψχ z hz
    have hd := (hc.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id 0)
    intro h
    simp [h] at hd
  refine ⟨V,hVo,hpV,G ∘ ψ,?_,?_,?_⟩
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := hz
    have hw2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
    apply (hGa w hw).comp_of_eq (hψa _ ⟨w,hw2,rfl⟩)
    exact hψχ w hw2
  · have hd := ((hGa 0 (by simp)).differentiableAt.hasDerivAt).comp_of_eq (χ 0)
      ((hψa _ (hVsub hpV)).differentiableAt.hasDerivAt) hψ0.symm
    rw [hd.deriv]
    exact mul_ne_zero hGd hψd
  · rintro z ⟨⟨w,hw,rfl⟩,hwu⟩
    have hw2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hw
    dsimp only [Function.comp_def]
    rw [hψχ w hw2]
    exact hGe ⟨hw,(hside w hw2).mp hwu⟩

end

open Set Filter Metric Complex
open scoped Topology
section

theorem analytic_family_gluing {ι : Type u_1} (U : ι → Set ℂ)
    (hU : ∀ i, IsOpen (U i)) (f : ι → ℂ → ℂ)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (he : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (⋃ i, U i) ∧ ∀ i, EqOn F (f i) (U i) := by
  classical
  let F : ℂ → ℂ := fun z => if h : ∃ i, z ∈ U i then f h.choose z else 0
  have hFe (i : ι) : EqOn F (f i) (U i) := by
    intro z hz
    have hh : ∃ i, z ∈ U i := ⟨i,hz⟩
    rw [show F z = f hh.choose z by simp only [F,dite_eq_left hh]]
    exact he hh.choose i ⟨hh.choose_spec,hz⟩
  refine ⟨F,?_,hFe⟩
  intro z hz
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  apply (hf i z hi).congr
  filter_upwards [(hU i).mem_nhds hi] with w hw
  exact (hFe i hw).symm

lemma analytic_boundary_lens_agreement {U : Set ℂ} (hU : IsOpen U)
    {p q : ℂ} (hp : p ∈ frontier U) (hq : q ∈ frontier U)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {F G f : ℂ → ℂ} (hFa : AnalyticOnNhd ℂ F (ball p r))
    (hGa : AnalyticOnNhd ℂ G (ball q s))
    (hFe : EqOn F f (ball p r ∩ U)) (hGe : EqOn G f (ball q s ∩ U))
    (hm : (ball p (r/3) ∩ ball q (s/3)).Nonempty) :
    EqOn F G (ball p r ∩ ball q s) := by
  have hc : IsPreconnected (ball p r ∩ ball q s) :=
    ((convex_ball p r).inter (convex_ball q s)).isPreconnected
  have hopen : IsOpen (ball p r ∩ ball q s) := isOpen_ball.inter isOpen_ball
  have hmeet : (ball p r ∩ ball q s ∩ U).Nonempty := by
    obtain ⟨z,hzp,hzq⟩ := hm
    have hpq : dist p q < (r+s)/3 := by
      calc dist p q ≤ dist p z + dist z q := dist_triangle _ _ _
        _ < r/3+s/3 := add_lt_add (by simpa only [mem_ball,dist_comm] using hzp) hzq
        _ = (r+s)/3 := by ring
    rcases le_total s r with hsr | hrs
    · have hmem : q ∈ ball p r ∩ ball q s := by
        constructor
        · rw [mem_ball,dist_comm]
          linarith
        · exact mem_ball_self hs
      exact (mem_closure_iff.mp hq.1 _ hopen hmem)
    · have hmem : p ∈ ball p r ∩ ball q s := by
        constructor
        · exact mem_ball_self hr
        · rw [mem_ball]
          linarith
      exact (mem_closure_iff.mp hp.1 _ hopen hmem)
  obtain ⟨z,hz,hzu⟩ := hmeet
  apply (hFa.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hGa.mono inter_subset_right) hc hz
  filter_upwards [(hopen.inter hU).mem_nhds ⟨hz,hzu⟩] with w hw
  exact (hFe ⟨hw.1.1,hw.2⟩).trans (hGe ⟨hw.1.2,hw.2⟩).symm

theorem analytic_boundary_patch {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hd : ∀ z ∈ U, deriv f z ≠ 0)
    (hloc : ∀ p ∈ frontier U, ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F V ∧ deriv F p ≠ 0 ∧ EqOn F f (V ∩ U)) :
    ∃ W : Set ℂ, IsOpen W ∧ closure U ⊆ W ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F W ∧ EqOn F f U ∧ ∀ z ∈ closure U, deriv F z ≠ 0 := by
  classical
  have hballs (p : frontier U) : ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (ball (p : ℂ) r) ∧ deriv F p ≠ 0 ∧
      EqOn F f (ball (p : ℂ) r ∩ U) := by
    obtain ⟨V,hVo,hp,F,hFa,hFd,hFe⟩ := hloc p p.property
    obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hVo p hp
    exact ⟨r,hr,F,hFa.mono hrV,hFd,fun z hz => hFe ⟨hrV hz.1,hz.2⟩⟩
  choose r hr g hga hgd hge using hballs
  let V : Option (frontier U) → Set ℂ := fun i => match i with
    | none => U
    | some p => ball (p : ℂ) (r p/3)
  let G : Option (frontier U) → ℂ → ℂ := fun i => match i with
    | none => f
    | some p => g p
  have hvo (i) : IsOpen (V i) := by cases i <;> simp only [V]; exact hU; exact isOpen_ball
  have hga' (i) : AnalyticOnNhd ℂ (G i) (V i) := by
    cases i with
    | none => exact hf
    | some p => exact (hga p).mono (ball_subset_ball (by have := hr p; linarith))
  have hcompat (i j) : EqOn (G i) (G j) (V i ∩ V j) := by
    cases i with
    | none =>
      cases j with
      | none => exact fun _ _ => rfl
      | some q =>
        intro z hz
        exact (hge q ⟨ball_subset_ball (by have := hr q; linarith) hz.2,hz.1⟩).symm
    | some p =>
      cases j with
      | none =>
        intro z hz
        exact hge p ⟨ball_subset_ball (by have := hr p; linarith) hz.1,hz.2⟩
      | some q =>
        intro z hz
        have he := analytic_boundary_lens_agreement hU p.property q.property
          (hr p) (hr q) (hga p) (hga q) (hge p) (hge q) ⟨z,hz⟩
        exact he ⟨ball_subset_ball (by have := hr p; linarith) hz.1,
          ball_subset_ball (by have := hr q; linarith) hz.2⟩
  obtain ⟨F,hFa,hFe⟩ := analytic_family_gluing V hvo G hga' hcompat
  refine ⟨⋃ i, V i,isOpen_iUnion hvo,?_,F,hFa,hFe none,?_⟩
  · intro z hz
    by_cases hzu : z ∈ U
    · exact mem_iUnion.mpr ⟨none,hzu⟩
    · have hzf : z ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hz,hzu⟩
      exact mem_iUnion.mpr ⟨some ⟨z,hzf⟩,mem_ball_self (div_pos (hr ⟨z,hzf⟩) (by norm_num))⟩
  · intro z hz
    by_cases hzu : z ∈ U
    · have he : F =ᶠ[𝓝 z] f := Filter.Eventually.mono (hU.mem_nhds hzu) (hFe none)
      rw [he.deriv_eq]
      exact hd z hzu
    · have hzf : z ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hz,hzu⟩
      let p : frontier U := ⟨z,hzf⟩
      have hp : z ∈ V (some p) := mem_ball_self (div_pos (hr p) (by norm_num))
      have he : F =ᶠ[𝓝 z] g p := Filter.Eventually.mono ((hvo (some p)).mem_nhds hp) (hFe (some p))
      rw [he.deriv_eq]
      exact hgd p

end

open Set Metric Filter Topology

lemma bounded_holomorphic_local_deriv {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hb : ∀ z ∈ U, ‖f z‖ ≤ 1)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : closedBall x (2*r) ⊆ U)
    {y : ℂ} (hy : y ∈ ball x r) : ‖deriv f y‖ ≤ 1/r := by
  have hs : closedBall y r ⊆ U := by
    intro z hz
    apply hx
    rw [mem_closedBall] at hz ⊢
    have hh := dist_triangle z y x
    have hy' : dist y x < r := hy
    linarith
  rw [← Complex.cderiv_eq_deriv hU hf hr hs]
  exact Complex.norm_cderiv_le hr (fun z hz => hb z (hs (sphere_subset_closedBall hz)))

lemma bounded_holomorphic_local_lipschitz {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hb : ∀ z ∈ U, ‖f z‖ ≤ 1)
    {x : ℂ} {r : ℝ} (hr : 0 < r) (hx : closedBall x (2*r) ⊆ U)
    {y z : ℂ} (hy : y ∈ ball x r) (hz : z ∈ ball x r) :
    ‖f z-f y‖ ≤ (1/r)*‖z-y‖ := by
  apply (convex_ball x r).norm_image_sub_le_of_norm_deriv_le ?_ ?_ hy hz
  · intro w hw
    apply hf.differentiableAt (hU.mem_nhds (hx ?_))
    exact mem_closedBall.mpr (le_trans (mem_ball.mp hw).le (by linarith))
  · intro w hw
    exact bounded_holomorphic_local_deriv hU hf hb hr hx hw

theorem bounded_holomorphic_equicontinuous {ι : Type u_2} {U : Set ℂ} (hU : IsOpen U)
    (F : ι → ℂ → ℂ) (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hb : ∀ i z, z ∈ U → ‖F i z‖ ≤ 1) : EquicontinuousOn F U := by
  intro x hx
  apply EquicontinuousAt.equicontinuousWithinAt
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrU : closedBall x (2*r) ⊆ U := by
    have he : 2*r = R := by dsimp [r]; ring
    rwa [he]
  refine ⟨min r (ε*r),lt_min hr (mul_pos hε hr),?_⟩
  intro y hy i
  have hyr : y ∈ ball x r := lt_of_lt_of_le hy (min_le_left _ _)
  have hl := bounded_holomorphic_local_lipschitz hU (hF i) (hb i) hr hrU
    (mem_ball_self hr) hyr
  rw [dist_eq_norm] at hy ⊢
  have hye : ‖y-x‖ < ε*r := lt_of_lt_of_le hy (min_le_right _ _)
  rw [norm_sub_rev]
  calc
    ‖F i y-F i x‖ ≤ (1/r)*‖y-x‖ := hl
    _ < (1/r)*(ε*r) := mul_lt_mul_of_pos_left hye (one_div_pos.mpr hr)
    _ = ε := by field_simp

theorem bounded_holomorphic_subsequence {U : Set ℂ} (hU : IsOpen U)
    (F : ℕ → ℂ → ℂ) (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hb : ∀ i z, z ∈ U → ‖F i z‖ ≤ 1) :
    ∃ (f : ℂ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (F ∘ φ) f atTop U ∧
      DifferentiableOn ℂ f U ∧ (∀ z ∈ U, ‖f z‖ ≤ 1) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let C : ℕ → C(U,ℂ) := fun n => ⟨U.domRestrict (F n), (hF n).continuousOn.domRestrict⟩
  have hE : Equicontinuous (fun n (x : U) => C n x) :=
    (equicontinuous_restrict_iff F).mpr (bounded_holomorphic_equicontinuous hU F hF hb)
  have hEc : Equicontinuous (fun g : range C => ((g : C(U,ℂ)) : U → ℂ)) := by
    have hh := hE.comp (fun g : range C => g.property.choose)
    convert hh using 1
    funext g x
    exact congrArg (fun q : C(U,ℂ) => q x) g.property.choose_spec.symm
  have hc : IsCompact (closure (range C)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(U,ℂ) => (g : U → ℂ))
      (𝔖 := {K | IsCompact K}) (fun _ h => h)
      (show IsClosedEmbedding ContinuousMap.toUniformOnFunIsCompact from
        ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, by
          rw [ContinuousMap.range_toUniformOnFunIsCompact]
          exact UniformOnFun.isClosed_setOfPred_continuous
            CompactlyCoherentSpace.isCoherentWith⟩)
    · intro K _
      exact hEc.equicontinuousOn K
    · intro K _ x _
      refine ⟨closedBall (0 : ℂ) 1,isCompact_closedBall _ _,?_⟩
      rintro _ ⟨n,rfl⟩
      simpa [C, mem_closedBall, dist_zero_right] using hb n x x.property
  obtain ⟨a,_,φ,hφ,ha⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let f : ℂ → ℂ := fun z => if hz : z ∈ U then a ⟨z,hz⟩ else 0
  have hl : TendstoLocallyUniformlyOn (F ∘ φ) f atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have hh := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ha
    have he : f ∘ (Subtype.val : U → ℂ) = (a : U → ℂ) := by
      funext x
      exact dite_eq_left x.property
    rw [he]
    exact hh
  refine ⟨f,φ,hφ,hl,hl.differentiableOn (Eventually.of_forall (fun n => hF (φ n))) hU,?_⟩
  intro z hz
  exact le_of_tendsto (hl.tendsto_at hz).norm (Eventually.of_forall (fun n => hb (φ n) z hz))

theorem zero_free_locally_uniform_limit {U : Set ℂ} (hU : IsOpen U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hn : ∀ n z, z ∈ U → F n z ≠ 0)
    (hl : TendstoLocallyUniformlyOn F f atTop U)
    {x : ℂ} (hx : x ∈ U) (hfx : f x = 0) : f =ᶠ[𝓝 x] 0 := by
  have hf := hl.differentiableOn (Eventually.of_forall hF) hU
  rcases (hf.analyticOnNhd hU x hx).eventually_eq_zero_or_eventually_ne_zero with he | he
  · exact he
  obtain ⟨R,hR,hRe⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  obtain ⟨S,hS,hSU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let r := min (R/2) S
  have hr : 0 < r := lt_min (half_pos hR) hS
  have hrR : r < R := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hR)
  have hrU : closedBall x r ⊆ U :=
    (closedBall_subset_closedBall (min_le_right _ _)).trans hSU
  have hne : ∀ z ∈ sphere x r, f z ≠ 0 := by
    intro z hz
    apply hRe
    refine ⟨?_,?_⟩
    · exact lt_of_eq_of_lt (mem_sphere.mp hz) hrR
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro hzx
      exact hr.ne' (by simpa [hzx] using (mem_sphere.mp hz).symm)
  obtain ⟨w,hw,hmin⟩ := (isCompact_sphere x r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (hf.continuousOn.norm.mono (sphere_subset_closedBall.trans hrU))
  let δ := ‖f w‖/2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr (hne w hw))
  have hlu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hl
    (sphere x r) (sphere_subset_closedBall.trans hrU) (isCompact_sphere x r)
  have hevent : ∀ᶠ n in atTop, δ ≤ ‖F n x‖ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlu δ hδ] with n hn'
    have hb : ∀ z ∈ sphere x r, δ ≤ ‖F n z‖ := by
      intro z hz
      have h1 := norm_sub_norm_le (f z) (F n z)
      have h2 := hn' z hz
      rw [dist_eq_norm] at h2
      have h3 : ‖f w‖ ≤ ‖f z‖ := hmin hz
      dsimp [δ] at *
      linarith
    have hd : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball x r) := by
      apply ((hF n).mono ?_).diffContOnCl.inv
      · intro z hz
        exact hn n z (hrU (by simpa [closure_ball x hr.ne'] using hz))
      · simpa [closure_ball x hr.ne'] using hrU
    have hi := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := x) (r := r))
      hd (C := δ⁻¹) (fun z hz => ?_) (subset_closure (mem_ball_self hr))
    · rw [norm_inv] at hi
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hn n x hx)) hδ).mp hi
    · rw [frontier_ball x hr.ne'] at hz
      rw [norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hn n z (hrU (sphere_subset_closedBall hz)))) hδ).mpr (hb z hz)
  have hc := ge_of_tendsto (hl.tendsto_at hx).norm hevent
  rw [hfx, norm_zero] at hc
  exact (not_le_of_gt hδ hc).elim

theorem injOn_locally_uniform_limit {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hi : ∀ n, InjOn (F n) U)
    (hl : TendstoLocallyUniformlyOn F f atTop U)
    {a : ℂ} (ha : a ∈ U) (hda : deriv f a ≠ 0) : InjOn f U := by
  have hf := hl.differentiableOn (Eventually.of_forall hF) hU
  intro x hx y hy hxy
  by_contra hne
  let V := U \ {x}
  have hV : IsOpen V := hU.inter isClosed_singleton.isOpen_compl
  have hyV : y ∈ V := ⟨hy,by simpa using Ne.symm hne⟩
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => F n x)
      (fun _ : ℂ => f x) atTop U :=
    (hl.tendsto_at hx).tendstoUniformly_const.tendstoLocallyUniformly.tendstoLocallyUniformlyOn
  have hl' : TendstoLocallyUniformlyOn (fun n z => F n z-F n x)
      (fun z => f z-f x) atTop V := (hl.sub hconst).mono sdiff_subset
  have he := zero_free_locally_uniform_limit hV
    (fun n => ((hF n).sub_const (F n x)).mono sdiff_subset)
    (fun n z hz he => hz.2 (by simpa using hi n hz.1 hx (sub_eq_zero.mp he)))
    hl' hyV (sub_eq_zero.mpr hxy.symm)
  have heU := ((hf.sub_const (f x)).analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hy he
  have hea : f =ᶠ[𝓝 a] (fun _ => f x) := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact sub_eq_zero.mp (heU hz)
  apply hda
  rw [hea.deriv_eq]
  exact deriv_const a (f x)

def NormalizedUnivalent (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ InjOn f U ∧ MapsTo f U (ball 0 1) ∧ f a = 0

lemma exists_normalized_univalent {U : Set ℂ} (hUb : Bornology.IsBounded U) (a : ℂ) :
    ∃ f, NormalizedUnivalent U a f ∧ deriv f a ≠ 0 := by
  obtain ⟨R,hR,hUR⟩ := hUb.subset_ball_lt 0 a
  let f : ℂ → ℂ := fun z => (z-a)/(R:ℂ)
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hd : ∀ z, HasDerivAt f (1/(R:ℂ)) z := fun z =>
    ((hasDerivAt_id z).sub_const a).div_const (R:ℂ)
  refine ⟨f,⟨(fun z _ => (hd z).differentiableAt.differentiableWithinAt),?_,?_,?_⟩,?_⟩
  · intro z _ w _ he
    have h : z-a = w-a := (div_left_inj' hRc).mp he
    linear_combination h
  · intro z hz
    rw [mem_ball_zero_iff]
    change ‖(z-a)/(R:ℂ)‖ < 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR]
    simpa [mem_ball,dist_eq_norm] using hUR hz
  · simp [f]
  · rw [(hd a).deriv]
    exact one_div_ne_zero hRc

theorem exists_extremal_univalent {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedUnivalent U a f ∧ deriv f a ≠ 0 ∧
      ∀ g, NormalizedUnivalent U a g → ‖deriv g a‖ ≤ ‖deriv f a‖ := by
  classical
  obtain ⟨f₀,hf₀,hd₀⟩ := exists_normalized_univalent hUb a
  let S : Set ℝ := {r | ∃ f, NormalizedUnivalent U a f ∧ ‖deriv f a‖ = r}
  have hS : S.Nonempty := ⟨_,f₀,hf₀,rfl⟩
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  let r := R/2
  have hr : 0 < r := half_pos hR
  have hrU : closedBall a (2*r) ⊆ U := by
    convert hRU using 1
    dsimp [r]
    congr 1
    ring
  have hSb : BddAbove S := by
    refine ⟨1/r,?_⟩
    rintro t ⟨g,hg,rfl⟩
    exact bounded_holomorphic_local_deriv hU hg.1
      (fun z hz => (mem_ball_zero_iff.mp (hg.2.2.1 hz)).le) hr hrU (mem_ball_self hr)
  have hpos : 0 < sSup S := lt_of_lt_of_le (norm_pos_iff.mpr hd₀)
    (le_csSup hSb ⟨f₀,hf₀,rfl⟩)
  obtain ⟨u,_,hu,hum⟩ := exists_seq_tendsto_sSup hS hSb
  choose F hFn hFd using hum
  obtain ⟨f,φ,hφ,hl,hf,hb⟩ := bounded_holomorphic_subsequence hU F
    (fun n => (hFn n).1) (fun n z hz => (mem_ball_zero_iff.mp ((hFn n).2.2.1 hz)).le)
  have hder := (hl.deriv (Eventually.of_forall (fun n => (hFn (φ n)).1)) hU).tendsto_at ha
  have hu' : Tendsto (fun n => ‖deriv (F (φ n)) a‖) atTop (𝓝 (sSup S)) := by
    simpa only [Function.comp_def, hFd] using hu.comp hφ.tendsto_atTop
  have he : ‖deriv f a‖ = sSup S := tendsto_nhds_unique hder.norm hu'
  have hda : deriv f a ≠ 0 := norm_pos_iff.mp (he ▸ hpos)
  have hfa : f a = 0 := by
    have h0 : Tendsto (fun n => F (φ n) a) atTop (𝓝 (0 : ℂ)) := by
      simp only [(hFn _).2.2.2]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hl.tendsto_at ha) h0
  have hmaps : MapsTo f U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_ne (hb z hz) ?_
    intro heq
    have hmax : IsMaxOn (norm ∘ f) U z := fun w hw => (hb w hw).trans_eq heq.symm
    have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hU hf hz hmax ha
    change f a = f z at hc
    have : f z = 0 := hc.symm.trans hfa
    simp [this] at heq
  refine ⟨f,⟨hf,injOn_locally_uniform_limit hU hUc
      (fun n => (hFn (φ n)).1) (fun n => (hFn (φ n)).2.1) hl ha hda,hmaps,hfa⟩,hda,?_⟩
  intro g hg
  rw [he]
  exact le_csSup hSb ⟨g,hg,rfl⟩


end CompleteCrouzeix

end

end OAI
