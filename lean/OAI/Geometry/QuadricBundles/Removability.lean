import OAI.Geometry.QuadricBundles.Curvature

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

lemma usc_ge_of_ae_ge {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → ℝ}
    (hu : UpperSemicontinuousOn u Ω) {c : ℝ}
    (hae : ∀ᵐ x ∂volume.restrict Ω, c ≤ u x) : ∀ x ∈ Ω, c ≤ u x := by
  have hopen : IsOpen {x | x ∈ Ω ∧ u x < c} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hh := hu x hx.1 c hx.2
    rw [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hx.1)] at hh
    exact inter_mem (hΩ.mem_nhds hx.1) hh
  have hz : volume {x | x ∈ Ω ∧ u x < c} = 0 := by
    have hh := (ae_restrict_iff' hΩ.measurableSet).mp hae
    simpa only [ae_iff, not_forall, not_le, Classical.not_imp, exists_prop] using hh
  have he := hopen.eq_empty_of_measure_zero hz
  intro x hx
  by_contra h
  have : x ∈ {x | x ∈ Ω ∧ u x < c} := ⟨hx, lt_of_not_ge h⟩
  rw [he] at this
  exact this

lemma DiskSubharmonicOn.eq_on_ball_of_max {Ω : Set ℂ} {u : ℂ → ℝ}
    (hu : DiskSubharmonicOn Ω u) {x : ℂ} (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hball : closedBall x r ⊆ Ω) (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∀ y ∈ ball x r, u y = u x := by
  have hb : ball x r ⊆ Ω := ball_subset_closedBall.trans hball
  have hi := (hu.2 x hx r hr hball).1
  have hle : u ≤ᵐ[volume.restrict (ball x r)] fun _ ↦ u x :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦ hmax y (hb hy)
  have hc : IntegrableOn (fun _ : ℂ ↦ u x) (ball x r) :=
    integrableOn_const (measure_ne_top_of_subset ball_subset_closedBall
      (isCompact_closedBall x r).measure_ne_top)
  have he : (∫ y in ball x r, u y) = ∫ _ in ball x r, u x := by
    apply le_antisymm (integral_mono_ae hi hc hle)
    simpa only [setIntegral_const, measureReal_def, smul_eq_mul]
      using (hu.2 x hx r hr hball).2
  have hae := (integral_eq_iff_of_ae_le hi hc hle).mp he
  have hge := usc_ge_of_ae_ge isOpen_ball (hu.1.mono hb)
    (hae.mono fun _ h ↦ h.ge)
  intro y hy
  exact le_antisymm (hmax y (hb hy)) (hge y hy)

theorem DiskSubharmonicOn.eq_const_of_max {Ω : Set ℂ} {u : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hu : DiskSubharmonicOn Ω u)
    {x : ℂ} (hx : x ∈ Ω) (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∀ y ∈ Ω, u y = u x := by
  let : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set Ω := {y | u x ≤ u y}
  have hc : IsClosed C :=
    (upperSemicontinuousOn_iff_restrict.mpr hu.1).isClosed_preimage (u x)
  have ho : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds y.property)
    have hey : u y = u x := le_antisymm (hmax y y.property) hy
    have he := hu.eq_on_ball_of_max y.property hr hball
      (fun z hz ↦ (hmax z hz).trans hey.ge)
    have hn : {z : Ω | (z : ℂ) ∈ ball (y : ℂ) r} ∈ 𝓝 y :=
      continuous_subtype_val.continuousAt (ball_mem_nhds (y : ℂ) hr)
    apply mem_of_superset hn
    intro z hz
    change u x ≤ u z
    rw [he z hz, hey]
  have hne : C.Nonempty := ⟨⟨x,hx⟩, by change u x ≤ u x; exact le_rfl⟩
  have heq : C = univ := (show IsClopen C from ⟨hc, ho⟩).eq_univ hne
  intro y hy
  have hh : (⟨y,hy⟩ : Ω) ∈ C := heq.symm ▸ mem_univ _
  exact le_antisymm (hmax y hy) hh

def LocalDiskSubmeanOn (Ω : Set ℂ) (u : ℂ → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ Ω ∧
    IntegrableOn u (ball x r) ∧
      (volume (ball x r)).toReal * u x ≤ ∫ y in ball x r, u y

theorem LocalDiskSubmeanOn.eq_on_ball_of_max {Ω : Set ℂ} {u : ℂ → ℝ}
    (hu : LocalDiskSubmeanOn Ω u) {x : ℂ} (hx : x ∈ Ω)
    (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ω ∧ ∀ y ∈ ball x r, u y = u x := by
  obtain ⟨r,hr,hball,hi,hmean⟩ := hu.2 x hx
  have hb : ball x r ⊆ Ω := ball_subset_closedBall.trans hball
  have hle : u ≤ᵐ[volume.restrict (ball x r)] fun _ ↦ u x :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦ hmax y (hb hy)
  have hc : IntegrableOn (fun _ : ℂ ↦ u x) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have he : (∫ y in ball x r, u y) = ∫ _ in ball x r, u x := by
    apply le_antisymm (integral_mono_ae hi hc hle)
    simpa only [setIntegral_const, measureReal_def, smul_eq_mul] using hmean
  have hae := (integral_eq_iff_of_ae_le hi hc hle).mp he
  have hge := usc_ge_of_ae_ge isOpen_ball (hu.1.mono hb) (hae.mono fun _ h ↦ h.ge)
  exact ⟨r,hr,hb,fun y hy ↦ le_antisymm (hmax y (hb hy)) (hge y hy)⟩

theorem LocalDiskSubmeanOn.eq_const_of_max {Ω : Set ℂ} {u : ℂ → ℝ}
    (hconn : IsPreconnected Ω) (hu : LocalDiskSubmeanOn Ω u)
    {x : ℂ} (hx : x ∈ Ω) (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∀ y ∈ Ω, u y = u x := by
  let : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set Ω := {y | u x ≤ u y}
  have hc : IsClosed C :=
    (upperSemicontinuousOn_iff_restrict.mpr hu.1).isClosed_preimage (u x)
  have ho : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hey : u y = u x := le_antisymm (hmax y y.property) hy
    obtain ⟨r,hr,_,he⟩ := hu.eq_on_ball_of_max y.property
      (fun z hz ↦ (hmax z hz).trans hey.ge)
    have hn : {z : Ω | (z : ℂ) ∈ ball (y : ℂ) r} ∈ 𝓝 y :=
      continuous_subtype_val.continuousAt (ball_mem_nhds (y : ℂ) hr)
    apply mem_of_superset hn
    intro z hz
    change u x ≤ u z
    rw [he z hz,hey]
  have hne : C.Nonempty := ⟨⟨x,hx⟩,by change u x ≤ u x; exact le_rfl⟩
  have heq : C = univ := (show IsClopen C from ⟨hc,ho⟩).eq_univ hne
  intro y hy
  have hh : (⟨y,hy⟩ : Ω) ∈ C := heq.symm ▸ mem_univ _
  exact le_antisymm (hmax y hy) hh

theorem LocalDiskSubmeanOn.le_boundary {u : ℂ → ℝ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hc : ContinuousOn u (closedBall c R))
    (hu : LocalDiskSubmeanOn (ball c R) u)
    (hb : ∀ z ∈ sphere c R, u z ≤ M) : ∀ z ∈ closedBall c R, u z ≤ M := by
  obtain ⟨x,hx,hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
    ⟨c,mem_closedBall_self hR.le⟩ hc
  suffices hh : u x ≤ M from fun z hz ↦ (hmax hz).trans hh
  by_cases hxb : x ∈ sphere c R
  · exact hb x hxb
  · have hxi : x ∈ ball c R := by
      rw [mem_ball,mem_closedBall] at *
      exact lt_of_le_of_ne hx (by simpa only [mem_sphere] using hxb)
    have he := hu.eq_const_of_max (convex_ball c R).isPreconnected hxi
      (fun z hz ↦ hmax (ball_subset_closedBall hz))
    have hec : ∀ z ∈ closedBall c R, u z = u x := by
      exact Set.EqOn.of_subset_closure he hc continuousOn_const
        ball_subset_closedBall (by rw [closure_ball c hR.ne'])
    have hz : c + (R : ℂ) ∈ sphere c R := by simp [hR.le]
    rw [← hec _ (sphere_subset_closedBall hz)]
    exact hb _ hz

theorem compact_family_local_submean
    {α : Type u1} {E : Type u2} [TopologicalSpace α] [CompactSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {D : Set ℂ} (hD : IsOpen D) {Φ : α → ℂ → E}
    (hc : ContinuousOn (Function.uncurry Φ) (univ ×ˢ D))
    (hd : ∀ a, DifferentiableOn ℂ (Φ a) D)
    {U : Set E} {q : E → ℝ} (hm : ∀ a, MapsTo (Φ a) D U)
    (hl : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ DiskPshOn V q)
    {z : ℂ} (hz : z ∈ D) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ D ∧ ∀ a,
      IntegrableOn (q ∘ Φ a) (ball z r) ∧
      (volume (ball z r)).toReal * q (Φ a z) ≤ ∫ y in ball z r, q (Φ a y) := by
  classical
  have hh (a : α) : ∃ (A : Set α) (W : Set ℂ) (V : Set E),
      A ∈ 𝓝 a ∧ W ∈ 𝓝 z ∧ IsOpen V ∧ DiskPshOn V q ∧
      ∀ b ∈ A, ∀ y ∈ W, Φ b y ∈ V := by
    obtain ⟨V,hVo,haV,hV⟩ := hl _ (hm a hz)
    have hcont : ContinuousAt (Function.uncurry Φ) (a,z) :=
      hc.continuousAt ((isOpen_univ.prod hD).mem_nhds ⟨mem_univ a,hz⟩)
    have hn : (Function.uncurry Φ) ⁻¹' V ∈ 𝓝 (a,z) := hcont (hVo.mem_nhds haV)
    rw [nhds_prod_eq,mem_prod_iff] at hn
    obtain ⟨A,hA,W,hW,hAW⟩ := hn
    exact ⟨A,W,V,hA,hW,hVo,hV,fun b hb y hy ↦ hAW (show (b,y) ∈ A ×ˢ W from ⟨hb,hy⟩)⟩
  choose A W V hA hW hVo hV hmap using hh
  obtain ⟨t,_,ht⟩ := isCompact_univ.elim_nhds_subcover A (fun a _ ↦ hA a)
  have hn : D ∩ ⋂ a ∈ t, W a ∈ 𝓝 z :=
    inter_mem (hD.mem_nhds hz) ((Filter.biInter_mem t.finite_toSet).mpr (fun a _ ↦ hW a))
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  refine ⟨r,hr,fun y hy ↦ (hball hy).1,?_⟩
  intro a
  obtain ⟨b,hbt,hab⟩ := mem_iUnion₂.mp (ht (mem_univ a))
  let O := D ∩ (Φ a) ⁻¹' V b
  have hO : IsOpen O := (hd a).continuousOn.isOpen_inter_preimage hD (hVo b)
  have hbO : closedBall z r ⊆ O := by
    intro y hy
    have hhy := hball hy
    exact ⟨hhy.1,hmap b a hab y (mem_iInter₂.mp hhy.2 b hbt)⟩
  have hp := (hV b).2 O hO (Φ a) ((hd a).mono inter_subset_left) (fun _ h ↦ h.2)
  exact hp.2 z (hbO (mem_closedBall_self hr.le)) r hr hbO

open scoped Pointwise
noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

theorem submean_of_locally_psh
    {E : Type u3} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {q : E → ℝ} (hq : ContinuousOn q U)
    (hl : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ DiskPshOn V q)
    {D : Set ℂ} (_hD : IsOpen D) {γ : ℂ → E}
    (hγ : DifferentiableOn ℂ γ D) (hm : MapsTo γ D U)
    {c : ℂ} (_hc : c ∈ D) {R : ℝ} (hR : 0 < R) (hb : closedBall c R ⊆ D) :
    (volume (ball c R)).toReal * q (γ c) ≤ ∫ y in ball c R, q (γ y) := by
  let A := closedBall (0 : ℂ) 1
  let : IsFiniteMeasure (volume : Measure A) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  let Φ : A → ℂ → E := fun a z ↦ γ (c+(a : ℂ)*z)
  let F : A → ℂ → ℝ := fun a z ↦ q (Φ a z)
  have hbΦ : ∀ a : A, MapsTo (fun z : ℂ ↦ c+(a : ℂ)*z) (closedBall 0 R)
      (closedBall c R) := by
    intro a z hz
    have ha : ‖(a : ℂ)‖ ≤ 1 := by
      have hh : (a : ℂ) ∈ closedBall 0 1 := a.property
      simpa only [mem_closedBall,dist_zero_right] using hh
    have hz' : ‖z‖ ≤ R := by simpa using hz
    simp only [mem_closedBall,dist_self_add_left,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg z) ha).trans hz'
  have hΦ : ContinuousOn (Function.uncurry Φ) (univ ×ˢ closedBall 0 R) := by
    apply hγ.continuousOn.comp (f := fun p : A × ℂ ↦ c+(p.1 : ℂ)*p.2) (by fun_prop)
    exact fun p hp ↦ hb (hbΦ p.1 hp.2)
  have hF : ContinuousOn (Function.uncurry F) (univ ×ˢ closedBall 0 R) :=
    hq.comp hΦ (fun p hp ↦ hm (hb (hbΦ p.1 hp.2)))
  have hcont := compact_integral_continuousOn (μ := (volume : Measure A)) hF
  have hdΦ : ∀ a, DifferentiableOn ℂ (Φ a) (ball 0 R) := by
    intro a
    apply hγ.comp (f := fun z : ℂ ↦ c+(a : ℂ)*z) (by fun_prop)
    exact fun z hz ↦ hb (hbΦ a (ball_subset_closedBall hz))
  have hΦmap : ∀ a, MapsTo (Φ a) (ball 0 R) U :=
    fun a z hz ↦ hm (hb (hbΦ a (ball_subset_closedBall hz)))
  have hlocal : LocalDiskSubmeanOn (ball 0 R) (fun z ↦ ∫ a : A, F a z) := by
    refine ⟨(hcont.mono ball_subset_closedBall).upperSemicontinuousOn,?_⟩
    intro z hz
    obtain ⟨r,hr,hbr,hs⟩ := compact_family_local_submean isOpen_ball
      (hΦ.mono (prod_mono (Subset.refl univ) ball_subset_closedBall)) hdΦ hΦmap hl hz
    have hprod : Integrable (fun p : A × ℂ ↦ F p.1 p.2)
        ((volume : Measure A).prod (volume.restrict (ball z r))) := by
      have hi := (hF.mono (prod_mono (Subset.refl univ)
        (hbr.trans ball_subset_closedBall))).integrableOn_compact
        (μ := (volume : Measure A).prod volume) (isCompact_univ.prod (isCompact_closedBall z r))
      have hj := hi.mono_set (prod_mono (Subset.refl univ) ball_subset_closedBall)
      unfold IntegrableOn at hj
      rw [← Measure.prod_restrict,Measure.restrict_univ] at hj
      exact hj
    have hp : Integrable (fun a : A ↦ F a z) := by
      have hh : Continuous (fun a : A ↦ F a z) :=
        hF.comp_continuous (f := fun a : A ↦ (a,z)) (by fun_prop)
          (fun _ ↦ ⟨mem_univ _,ball_subset_closedBall hz⟩)
      exact integrableOn_univ.mp (hh.continuousOn.integrableOn_compact isCompact_univ)
    refine ⟨r,hr,hbr,hprod.integral_prod_right,?_⟩
    calc
      (volume (ball z r)).toReal * (∫ a : A, F a z) =
          ∫ a : A, (volume (ball z r)).toReal * F a z := (integral_const_mul _ _).symm
      _ ≤ ∫ a : A, ∫ y in ball z r, F a y :=
        integral_mono_ae (hp.const_mul _) hprod.integral_prod_left
          (Eventually.of_forall fun a ↦ (hs a).2)
      _ = ∫ y in ball z r, ∫ a : A, F a y := integral_integral_swap hprod
  have he (z : ℂ) : (∫ a : A, F a z) = radialIntegral (q ∘ γ) c z := by
    exact integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
      (fun a : ℂ ↦ q (γ (c+a*z)))
  have hm0 := hlocal.le_boundary hR hcont (M := radialIntegral (q ∘ γ) c (R : ℂ)) (by
    intro z hz
    rw [he]
    apply le_of_eq
    apply radialIntegral_eq_of_norm_eq
    simpa only [mem_sphere,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] using hz)
    0 (mem_closedBall_self hR.le)
  rw [he,radialIntegral_zero,radialIntegral_pos_radius _ _ hR] at hm0
  have hv := radialIntegral_pos_radius (fun _ ↦ (1 : ℝ)) c hR
  simp only [radialIntegral,setIntegral_const,measureReal_def,smul_eq_mul,mul_one] at hv
  have heR := complex_closedBall_ae_ball c R
  rw [measure_congr heR] at hv
  rw [← setIntegral_congr_set heR]
  have hn : R^2 ≠ 0 := pow_ne_zero _ hR.ne'
  have hscale : R^2 * (R^2)⁻¹ = 1 := mul_inv_cancel₀ hn
  have hmul := mul_le_mul_of_nonneg_left hm0 (sq_nonneg R)
  calc
    (volume (ball c R)).toReal * q (γ c) =
        R^2 * ((volume (closedBall (0 : ℂ) 1)).toReal * q (γ c)) := by
      rw [hv]
      rw [← mul_assoc,← mul_assoc,hscale,one_mul]
    _ ≤ R^2 * ((R^2)⁻¹ * ∫ y in closedBall c R, q (γ y)) := hmul
    _ = ∫ y in closedBall c R, q (γ y) := by rw [← mul_assoc,hscale,one_mul]

theorem DiskPshOn.of_locally
    {E : Type u4} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {q : E → ℝ} (hq : ContinuousOn q U)
    (hl : ∀ x ∈ U, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ DiskPshOn V q) :
    DiskPshOn U q := by
  refine ⟨hq.upperSemicontinuousOn,?_⟩
  intro D hD γ hγ hm
  have hcont := hq.comp hγ.continuousOn hm
  refine ⟨hcont.upperSemicontinuousOn,?_⟩
  intro c hc R hR hb
  refine ⟨((hcont.mono hb).integrableOn_compact (isCompact_closedBall c R)).mono_set
    ball_subset_closedBall,?_⟩
  exact submean_of_locally_psh hq hl hD hγ hm hc hR hb

open Real

theorem radialIntegral_of_circle_means {u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hu : ContinuousOn u (closedBall c R))
    (hm : ∀ a ∈ closedBall (0 : ℂ) 1,
      circleAverage (fun z ↦ u (c+a*z)) 0 R = u c) :
    radialIntegral u c (R : ℂ) = (volume (closedBall (0 : ℂ) 1)).toReal * u c := by
  have hmap (a : ℂ) (ha : a ∈ closedBall (0 : ℂ) 1) (θ : ℝ) :
      c+a*circleMap 0 R θ ∈ closedBall c R := by
    have ha' : ‖a‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using ha
    simp only [mem_closedBall,dist_self_add_left,norm_mul,norm_circleMap_zero,abs_of_nonneg hR]
    exact mul_le_of_le_one_left hR ha'
  have hc : ContinuousOn (fun p : ℂ × ℝ ↦ u (c+p.1*circleMap 0 R p.2))
      (closedBall (0 : ℂ) 1 ×ˢ Icc 0 (2*Real.pi)) :=
    hu.comp (by fun_prop) (fun p hp ↦ hmap p.1 hp.1 p.2)
  have hi := hc.integrableOn_compact
    (μ := (volume : Measure ℂ).prod volume) ((isCompact_closedBall (0 : ℂ) 1).prod isCompact_Icc)
  have hij := hi.mono_set (prod_mono (Subset.refl (closedBall (0 : ℂ) 1)) Ioc_subset_Icc_self)
  unfold IntegrableOn at hij
  rw [← Measure.prod_restrict] at hij
  have hswap := integral_integral_swap (f := fun a : ℂ ↦ fun θ : ℝ ↦ u (c+a*circleMap 0 R θ)) hij
  have hr (θ : ℝ) : (∫ a in closedBall (0 : ℂ) 1, u (c+a*circleMap 0 R θ)) =
      radialIntegral u c (R : ℂ) := by
    apply radialIntegral_eq_of_norm_eq
    simp [norm_circleMap_zero]
  calc
    radialIntegral u c (R : ℂ) =
        (2*Real.pi)⁻¹ * ∫ θ in Ioc 0 (2*Real.pi), radialIntegral u c (R : ℂ) := by
      simp only [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc]
      rw [sub_zero, ENNReal.toReal_ofReal Real.two_pi_pos.le]
      field_simp [Real.pi_ne_zero]
    _ = (2*Real.pi)⁻¹ * ∫ θ in Ioc 0 (2*Real.pi),
        ∫ a in closedBall (0 : ℂ) 1, u (c+a*circleMap 0 R θ) := by simp only [hr]
    _ = (2*Real.pi)⁻¹ * ∫ a in closedBall (0 : ℂ) 1,
        ∫ θ in Ioc 0 (2*Real.pi), u (c+a*circleMap 0 R θ) := by rw [hswap]
    _ = ∫ a in closedBall (0 : ℂ) 1,
        circleAverage (fun z ↦ u (c+a*z)) 0 R := by
      simp only [circleAverage,intervalIntegral.integral_of_le Real.two_pi_pos.le,
        smul_eq_mul,integral_const_mul]
    _ = ∫ _a in closedBall (0 : ℂ) 1, u c := by
      apply setIntegral_congr_fun measurableSet_closedBall
      exact hm
    _ = (volume (closedBall (0 : ℂ) 1)).toReal * u c := by
      simp only [setIntegral_const,measureReal_def,smul_eq_mul]
lemma log_norm_subharmonic {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hn : ∀ z ∈ D, f z ≠ 0) :
    DiskSubharmonicOn D (fun z ↦ Real.log ‖f z‖) := by
  have hcont : ContinuousOn (fun z ↦ Real.log ‖f z‖) D :=
    hf.continuousOn.norm.log (fun z hz ↦ norm_ne_zero_iff.mpr (hn z hz))
  refine ⟨hcont.upperSemicontinuousOn,?_⟩
  intro c hc R hR hb
  refine ⟨((hcont.mono hb).integrableOn_compact (isCompact_closedBall c R)).mono_set
    ball_subset_closedBall,?_⟩
  have hm : ∀ a ∈ closedBall (0 : ℂ) 1,
      circleAverage (fun z ↦ Real.log ‖f (c+a*z)‖) 0 R = Real.log ‖f c‖ := by
    intro a ha
    have ha' : ‖a‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using ha
    have hg : ∀ z ∈ closedBall (0 : ℂ) |R|, c+a*z ∈ D := by
      intro z hz
      apply hb
      have hz' : ‖z‖ ≤ R := by simpa [abs_of_pos hR] using hz
      simp only [mem_closedBall,dist_self_add_left,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg z) ha').trans hz'
    have hh : InnerProductSpace.HarmonicOnNhd (fun z ↦ Real.log ‖f (c+a*z)‖)
        (closedBall (0 : ℂ) |R|) := by
      intro z hz
      apply AnalyticAt.harmonicAt_log_norm
      · exact (hf.analyticAt (hD.mem_nhds (hg z hz))).comp (f := fun w : ℂ ↦ c+a*w)
          (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ c+a*w) z)
      · exact hn _ (hg z hz)
    simpa only [mul_zero,add_zero] using hh.circleAverage_eq
  have he := radialIntegral_of_circle_means hR.le (hcont.mono hb) hm
  rw [radialIntegral_pos_radius _ _ hR] at he
  have hv := radialIntegral_pos_radius (fun _ ↦ (1 : ℝ)) c hR
  simp only [radialIntegral,setIntegral_const,measureReal_def,smul_eq_mul,mul_one] at hv
  have hball := complex_closedBall_ae_ball c R
  rw [measure_congr hball] at hv
  rw [← setIntegral_congr_set hball]
  apply le_of_eq
  rw [hv] at he
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 hR.ne'))
  simpa only [mul_assoc] using he.symm

theorem log_norm_psh {E : Type u5} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (_hU : IsOpen U) {f : E → ℂ} (hf : DifferentiableOn ℂ f U)
    (hn : ∀ x ∈ U, f x ≠ 0) : DiskPshOn U (fun x ↦ Real.log ‖f x‖) := by
  refine ⟨(hf.continuousOn.norm.log (fun x hx ↦ norm_ne_zero_iff.mpr (hn x hx))).upperSemicontinuousOn,?_⟩
  intro D hD γ hγ hm
  exact log_norm_subharmonic hD (hf.comp hγ hm) (fun z hz ↦ hn _ (hm hz))
lemma DiskPshOn.comp {E : Type u6} {F : Type u7} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {Ω : Set E} {U : Set F}
    {q : E → ℝ} (hq : DiskPshOn Ω q) {f : F → E}
    (hf : DifferentiableOn ℂ f U) (hmap : MapsTo f U Ω) :
    DiskPshOn U (q ∘ f) := by
  refine ⟨hq.1.comp hf.continuousOn hmap, ?_⟩
  intro D hD γ hγ hγmap
  exact hq.2 D hD (f ∘ γ) (hf.comp hγ hγmap) (hmap.comp hγmap)

lemma DiskSubharmonicOn.add {D : Set ℂ} {u v : ℂ → ℝ}
    (hu : DiskSubharmonicOn D u) (hv : DiskSubharmonicOn D v) :
    DiskSubharmonicOn D (fun z ↦ u z + v z) := by
  refine ⟨hu.1.add hv.1,?_⟩
  intro c hc R hR hb
  obtain ⟨hui,hus⟩ := hu.2 c hc R hR hb
  obtain ⟨hvi,hvs⟩ := hv.2 c hc R hR hb
  refine ⟨hui.add hvi,?_⟩
  rw [integral_add hui hvi,mul_add]
  exact add_le_add hus hvs

lemma DiskSubharmonicOn.max {D : Set ℂ} {u v : ℂ → ℝ}
    (hu : DiskSubharmonicOn D u) (hv : DiskSubharmonicOn D v) :
    DiskSubharmonicOn D (fun z ↦ max (u z) (v z)) := by
  refine ⟨hu.1.sup hv.1,?_⟩
  intro c hc R hR hb
  obtain ⟨hui,hus⟩ := hu.2 c hc R hR hb
  obtain ⟨hvi,hvs⟩ := hv.2 c hc R hR hb
  have hi := hui.sup hvi
  refine ⟨hi,?_⟩
  dsimp only
  rcases le_total (u c) (v c) with h|h
  · rw [max_eq_right h]
    exact hvs.trans (integral_mono hvi hi (fun z ↦ le_max_right _ _))
  · rw [max_eq_left h]
    exact hus.trans (integral_mono hui hi (fun z ↦ le_max_left _ _))

lemma DiskPshOn.add {E : Type u8} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {u v : E → ℝ} (hu : DiskPshOn U u) (hv : DiskPshOn U v) :
    DiskPshOn U (fun z ↦ u z + v z) := by
  refine ⟨hu.1.add hv.1,?_⟩
  intro D hD γ hγ hm
  exact (hu.2 D hD γ hγ hm).add (hv.2 D hD γ hγ hm)

lemma DiskPshOn.max {E : Type u9} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {u v : E → ℝ} (hu : DiskPshOn U u) (hv : DiskPshOn U v) :
    DiskPshOn U (fun z ↦ max (u z) (v z)) := by
  refine ⟨hu.1.sup hv.1,?_⟩
  intro D hD γ hγ hm
  exact (hu.2 D hD γ hγ hm).max (hv.2 D hD γ hγ hm)

lemma diskPshOn_const {E : Type u10} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (c : ℝ) : DiskPshOn U (fun _ ↦ c) := by
  refine ⟨continuousOn_const.upperSemicontinuousOn,?_⟩
  intro D hD γ hγ hm
  refine ⟨continuousOn_const.upperSemicontinuousOn,?_⟩
  intro z hz R hR hb
  refine ⟨integrableOn_const measure_ball_lt_top.ne,?_⟩
  simp only [Function.comp_apply,setIntegral_const,measureReal_def,smul_eq_mul,le_refl]

lemma DiskPshOn.const_mul_of_continuous {E : Type u11} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {u : E → ℝ} (hu : DiskPshOn U u) (hc : ContinuousOn u U)
    {δ : ℝ} (hδ : 0 ≤ δ) : DiskPshOn U (fun z ↦ δ*u z) := by
  refine ⟨(hc.const_mul δ).upperSemicontinuousOn,?_⟩
  intro D hD γ hγ hm
  refine ⟨((hc.comp hγ.continuousOn hm).const_mul δ).upperSemicontinuousOn,?_⟩
  intro z hz R hR hb
  obtain ⟨hi,hs⟩ := (hu.2 D hD γ hγ hm).2 z hz R hR hb
  refine ⟨hi.const_mul δ,?_⟩
  change (volume (ball z R)).toReal * (δ*u (γ z)) ≤ ∫ y in ball z R, δ*u (γ y)
  rw [integral_const_mul,mul_left_comm]
  exact mul_le_mul_of_nonneg_left hs hδ

lemma DiskPshOn.mono {E : Type u12} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U V : Set E} {u : E → ℝ} (hu : DiskPshOn U u) (hVU : V ⊆ U) : DiskPshOn V u :=
  ⟨hu.1.mono hVU,fun D hD γ hγ hm ↦ hu.2 D hD γ hγ (fun _ hz ↦ hVU (hm hz))⟩

lemma DiskPshOn.congr {E : Type u13} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} {u v : E → ℝ} (hu : DiskPshOn U u) (he : EqOn u v U) :
    DiskPshOn U v := by
  refine ⟨fun x hx ↦ UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hu.1 x hx) hx
    ((show ∀ᶠ y in 𝓝[U] x, y ∈ U from self_mem_nhdsWithin).mono (fun y hy ↦ he hy)),?_⟩
  intro D hD γ hγ hm
  have hd := hu.2 D hD γ hγ hm
  refine ⟨fun z hz ↦ UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hd.1 z hz) hz
    ((show ∀ᶠ y in 𝓝[D] z, y ∈ D from self_mem_nhdsWithin).mono (fun y hy ↦ he (hm hy))),?_⟩
  intro z hz R hR hb
  have he' : (fun y ↦ u (γ y)) =ᵐ[volume.restrict (ball z R)] (fun y ↦ v (γ y)) :=
    (ae_restrict_mem measurableSet_ball).mono (fun y hy ↦ he (hm (hb (ball_subset_closedBall hy))))
  obtain ⟨hi,hs⟩ := hd.2 z hz R hR hb
  refine ⟨hi.congr he',?_⟩
  change (volume (ball z R)).toReal * v (γ z) ≤ ∫ y in ball z R, v (γ y)
  change (volume (ball z R)).toReal * u (γ z) ≤ ∫ y in ball z R, u (γ y) at hs
  rwa [integral_congr_ae he',he (hm hz)] at hs
def logBarrier {E : Type u14} (q : E → ℝ) (f : E → ℂ) (δ : ℝ) (x : E) : ℝ :=
  if f x = 0 then 0 else max (q x + δ * Real.log ‖f x‖) 0

lemma logBarrier_eventually_zero {E : Type u15} [TopologicalSpace E]
    {q : E → ℝ} {f : E → ℂ} {x : E} (hq : ContinuousAt q x)
    (hf : ContinuousAt f x) (hx : f x = 0) {δ : ℝ} (hδ : 0 < δ) :
    logBarrier q f δ =ᶠ[𝓝 x] (fun _ ↦ 0) := by
  have hq' : ∀ᶠ y in 𝓝 x, q y < q x + 1 :=
    hq.eventually (gt_mem_nhds (lt_add_one (q x)))
  have hf' : ∀ᶠ y in 𝓝 x, ‖f y‖ < Real.exp (-(q x+1)/δ) :=
    hf.norm.eventually (gt_mem_nhds (by simpa [hx] using Real.exp_pos (-(q x+1)/δ)))
  filter_upwards [hq',hf'] with y hyq hyf
  unfold logBarrier
  split_ifs with hy
  · rfl
  · have hl := (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hy)).mpr hyf
    have hm := mul_lt_mul_of_pos_left hl hδ
    have he : δ * (-(q x+1)/δ) = -(q x+1) := by field_simp
    rw [he] at hm
    exact max_eq_right (by linarith)

lemma logBarrier_continuousOn {E : Type u16} [TopologicalSpace E]
    {U : Set E} (hU : IsOpen U) {q : E → ℝ} {f : E → ℂ}
    (hq : ContinuousOn q U) (hf : ContinuousOn f U) {δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (logBarrier q f δ) U := by
  intro x hx
  have hqa := hq.continuousAt (hU.mem_nhds hx)
  have hfa := hf.continuousAt (hU.mem_nhds hx)
  apply ContinuousAt.continuousWithinAt
  by_cases hz : f x = 0
  · exact continuousAt_const.congr_of_eventuallyEq
      (logBarrier_eventually_zero hqa hfa hz hδ)
  · have hn : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hfa.eventually_ne hz
    have hc : ContinuousAt (fun y ↦ max (q y + δ * Real.log ‖f y‖) 0) x :=
      (hqa.add ((hfa.norm.log (norm_ne_zero_iff.mpr hz)).const_mul δ)).max continuousAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [hn] with y hy
    simp only [logBarrier,hy,↓reduceIte]

lemma logBarrier_nonneg {E : Type u17} (q : E → ℝ) (f : E → ℂ) (δ : ℝ) (x : E) :
    0 ≤ logBarrier q f δ x := by
  unfold logBarrier
  split_ifs
  · exact le_refl _
  · exact le_max_right _ _

lemma logBarrier_le {E : Type u18} {q : E → ℝ} {f : E → ℂ} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {x : E} (hq : 0 ≤ q x) :
    logBarrier q f δ x ≤ q x + ‖f x‖ := by
  unfold logBarrier
  split_ifs with hf
  · positivity
  · apply max_le _ (by positivity)
    apply add_le_add_right
    by_cases hl : Real.log ‖f x‖ ≤ 0
    · exact (mul_nonpos_of_nonneg_of_nonpos hδ0 hl).trans (norm_nonneg _)
    · exact (mul_le_of_le_one_left (le_of_not_ge hl) hδ1).trans
        ((Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hf)).trans (by linarith))

lemma logBarrier_tendsto_of_ne_zero {E : Type u19} {q : E → ℝ} {f : E → ℂ}
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) {x : E}
    (hf : f x ≠ 0) (hq : 0 ≤ q x) :
    Tendsto (fun n ↦ logBarrier q f (δ n) x) atTop (𝓝 (q x)) := by
  simpa only [logBarrier,hf,↓reduceIte,zero_mul,add_zero,max_eq_left hq] using
    ((tendsto_const_nhds (x := q x)).add (hδ.mul_const (Real.log ‖f x‖))).max
      (tendsto_const_nhds (x := (0 : ℝ)))

theorem logBarrier_psh {E : Type u20} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) {q : E → ℝ} {f : E → ℂ}
    (hq : ContinuousOn q U) (hf : Differentiable ℂ f)
    (hp : DiskPshOn (U ∩ {x | f x ≠ 0}) q) {δ : ℝ} (hδ : 0 < δ) :
    DiskPshOn U (logBarrier q f δ) := by
  apply DiskPshOn.of_locally (logBarrier_continuousOn hU hq hf.continuous.continuousOn hδ)
  intro x hx
  by_cases hz : f x = 0
  · have he := logBarrier_eventually_zero (hq.continuousAt (hU.mem_nhds hx))
      hf.continuous.continuousAt hz hδ
    obtain ⟨V,hV,ho,hxV⟩ := _root_.mem_nhds_iff.mp he
    refine ⟨V,ho,hxV,(diskPshOn_const V 0).congr ?_⟩
    exact fun y hy ↦ (hV hy).symm
  · let V := U ∩ {y | f y ≠ 0}
    have hV : IsOpen V := hU.inter (isClosed_singleton.isOpen_compl.preimage hf.continuous)
    have hn : ∀ y ∈ V, f y ≠ 0 := fun y hy ↦ hy.2
    have hc : ContinuousOn (fun y ↦ Real.log ‖f y‖) V :=
      hf.continuous.continuousOn.norm.log (fun y hy ↦ norm_ne_zero_iff.mpr (hn y hy))
    have hl := (log_norm_psh hV hf.differentiableOn hn).const_mul_of_continuous hc hδ.le
    refine ⟨V,hV,⟨hx,hz⟩,((hp.add hl).max (diskPshOn_const V 0)).congr ?_⟩
    intro y hy
    simp only [logBarrier,hn y hy,↓reduceIte]

theorem DiskSubharmonicOn.pointwise_limit {Ω : Set ℂ} {u : ℕ → ℂ → ℝ}
    {q : ℂ → ℝ} (hu : ∀ n, DiskSubharmonicOn Ω (u n))
    (hq : UpperSemicontinuousOn q Ω)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n ↦ u n x) atTop (𝓝 (q x)))
    (hbound : ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → closedBall x r ⊆ Ω →
      ∃ C : ℝ, ∀ n, ∀ y ∈ ball x r, ‖u n y‖ ≤ C) : DiskSubharmonicOn Ω q := by
  refine ⟨hq, ?_⟩
  intro x hx r hr hb
  obtain ⟨C, hC⟩ := hbound x hx r hr hb
  have hi (n : ℕ) : IntegrableOn (u n) (ball x r) := (hu n).2 x hx r hr hb |>.1
  have hc : IntegrableOn (fun _ : ℂ ↦ C) (ball x r) :=
    integrableOn_const measure_ball_lt_top.ne
  have hCae (n : ℕ) : ∀ᵐ y ∂volume.restrict (ball x r), ‖u n y‖ ≤ C :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦ hC n y hy
  have hl : ∀ᵐ y ∂volume.restrict (ball x r),
      Tendsto (fun n ↦ u n y) atTop (𝓝 (q y)) :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦ hlim y (hb (ball_subset_closedBall hy))
  have hqi : IntegrableOn q (ball x r) := by
    apply hc.mono' (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hi n).aestronglyMeasurable) hl)
    filter_upwards [hl, ae_all_iff.mpr hCae] with y hy hCy
    exact le_of_tendsto hy.norm (Eventually.of_forall hCy)
  have hInt := tendsto_integral_of_dominated_convergence (fun _ : ℂ ↦ C)
    (fun n ↦ (hi n).aestronglyMeasurable) hc hCae hl
  refine ⟨hqi, ?_⟩
  exact le_of_tendsto_of_tendsto ((hlim x hx).const_mul _) hInt
    (Eventually.of_forall fun n ↦ (hu n).2 x hx r hr hb |>.2)

theorem DiskSubharmonicOn.integral {α : Type u21} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {Ω : Set ℂ} {F : α → ℂ → ℝ}
    (hF : ∀ᵐ a ∂μ, DiskSubharmonicOn Ω (F a))
    (hc : UpperSemicontinuousOn (fun z ↦ ∫ a, F a z ∂μ) Ω)
    (hpoint : ∀ z ∈ Ω, Integrable (fun a ↦ F a z) μ)
    (hprod : ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → closedBall z r ⊆ Ω →
      Integrable (fun p : α × ℂ ↦ F p.1 p.2) (μ.prod (volume.restrict (ball z r)))) :
    DiskSubharmonicOn Ω (fun z ↦ ∫ a, F a z ∂μ) := by
  refine ⟨hc, ?_⟩
  intro z hz r hr hb
  have hi := hprod z hz r hr hb
  refine ⟨hi.integral_prod_right, ?_⟩
  have hm : ∀ᵐ a ∂μ, (volume (ball z r)).toReal * F a z ≤ ∫ y in ball z r, F a y :=
    hF.mono fun a ha ↦ (ha.2 z hz r hr hb).2
  calc
    (volume (ball z r)).toReal * (∫ a, F a z ∂μ) =
        ∫ a, (volume (ball z r)).toReal * F a z ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ a, (∫ y in ball z r, F a y) ∂μ :=
      integral_mono_ae ((hpoint z hz).const_mul _) hi.integral_prod_left hm
    _ = ∫ y in ball z r, ∫ a, F a y ∂μ := integral_integral_swap hi

theorem DiskPshOn.pointwise_limit {E : Type u22} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Ω : Set E} {u : ℕ → E → ℝ} {q : E → ℝ}
    (hu : ∀ n, DiskPshOn Ω (u n)) (hq : UpperSemicontinuousOn q Ω)
    (hlim : ∀ x ∈ Ω, Tendsto (fun n ↦ u n x) atTop (𝓝 (q x)))
    (hbound : ∀ K : Set E, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n, ∀ x ∈ K, ‖u n x‖ ≤ C) : DiskPshOn Ω q := by
  refine ⟨hq, ?_⟩
  intro D hD γ hγ hmap
  refine DiskSubharmonicOn.pointwise_limit (fun n ↦ (hu n).2 D hD γ hγ hmap)
    (hq.comp hγ.continuousOn hmap) (fun x hx ↦ hlim (γ x) (hmap hx)) ?_
  intro x hx r hr hb
  have hc : IsCompact (γ '' closedBall x r) :=
    (isCompact_closedBall x r).image_of_continuousOn (hγ.continuousOn.mono hb)
  obtain ⟨C, hC⟩ := hbound _ hc (image_subset_iff.mpr (hmap.mono_left hb))
  exact ⟨C, fun n y hy ↦ hC n (γ y) ⟨y, ball_subset_closedBall hy, rfl⟩⟩

lemma continuousOn_integral_compact_parameter
    {E : Type u23} {α : Type u24} [NormedAddCommGroup E] [LocallyCompactSpace E]
    [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {Ω : Set E} (hΩ : IsOpen Ω)
    {F : α → E → ℝ} (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Ω)) :
    ContinuousOn (fun x ↦ ∫ a, F a x ∂μ) Ω := by
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have hc : Continuous (fun p : Ω × α ↦ F p.2 p.1) :=
    hF.comp_continuous (f := fun p : Ω × α ↦ (p.2, (p.1 : E)))
      (by fun_prop) (fun p ↦ ⟨mem_univ _, p.1.property⟩)
  have hi := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun x : Ω ↦ fun a : α ↦ F a x) hc isCompact_univ
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hi using 1
  ext x
  simp only [Set.domRestrict_apply, setIntegral_univ]

theorem DiskPshOn.integral_compact_parameter
    {E : Type u25} {α : Type u26} [NormedAddCommGroup E] [NormedSpace ℂ E] [LocallyCompactSpace E]
    [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {Ω : Set E} (hΩ : IsOpen Ω) {F : α → E → ℝ}
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ Ω))
    (hF : ∀ a, DiskPshOn Ω (F a)) : DiskPshOn Ω (fun x ↦ ∫ a, F a x ∂μ) := by
  have hcont := continuousOn_integral_compact_parameter (μ := μ) hΩ hc
  refine ⟨hcont.upperSemicontinuousOn, ?_⟩
  intro D hD γ hγ hmap
  apply DiskSubharmonicOn.integral
    (Eventually.of_forall fun a ↦ (hF a).2 D hD γ hγ hmap)
    (hcont.upperSemicontinuousOn.comp hγ.continuousOn hmap)
  · intro z hz
    have hh : Continuous (fun a ↦ F a (γ z)) :=
      hc.comp_continuous (f := fun a : α ↦ (a, γ z))
        (by fun_prop) (fun a ↦ ⟨mem_univ _, hmap hz⟩)
    exact integrableOn_univ.mp (hh.continuousOn.integrableOn_compact isCompact_univ)
  · intro z hz r hr hb
    have hcomp : ContinuousOn (fun p : α × ℂ ↦ F p.1 (γ p.2))
        (univ ×ˢ closedBall z r) := by
      apply hc.comp (continuous_fst.continuousOn.prodMk
        (hγ.continuousOn.comp continuous_snd.continuousOn (fun p hp ↦ hb hp.2)))
      exact fun p hp ↦ ⟨mem_univ _, hmap (hb hp.2)⟩
    have hi := hcomp.integrableOn_compact (μ := μ.prod volume) (isCompact_univ.prod (isCompact_closedBall z r))
    have hij := hi.mono_set (prod_mono (Subset.refl univ) ball_subset_closedBall)
    unfold IntegrableOn at hij
    rw [← Measure.prod_restrict univ (ball z r), Measure.restrict_univ] at hij
    exact hij

theorem averaged_hypersurface_removal
    {E : Type u27} {α : Type u28} [NormedAddCommGroup E] [NormedSpace ℂ E] [LocallyCompactSpace E]
    [TopologicalSpace α] [CompactSpace α] [T2Space α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) {q : E → ℝ} {f : E → ℂ}
    (hq : ContinuousOn q U) (hq0 : ∀ x ∈ U, 0 ≤ q x) (hf : Differentiable ℂ f)
    (hp : DiskPshOn (U ∩ {x | f x ≠ 0}) q) {H : α → E → E}
    (hHc : ContinuousOn (Function.uncurry H) (univ ×ˢ V))
    (hHd : ∀ a, DifferentiableOn ℂ (H a) V) (hHm : ∀ a, MapsTo (H a) V U)
    (hzero : ∀ x ∈ V, ∀ᵐ a ∂μ, f (H a x) ≠ 0) :
    DiskPshOn V (fun x ↦ ∫ a, q (H a x) ∂μ) := by
  let δ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ)+1)
  have hδp (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδ1 (n : ℕ) : δ n ≤ 1 := by
    dsimp [δ]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → α → E → ℝ := fun n a x ↦ logBarrier q f (δ n) (H a x)
  have hFc (n : ℕ) : ContinuousOn (Function.uncurry (F n)) (univ ×ˢ V) :=
    (logBarrier_continuousOn hU hq hf.continuous.continuousOn (hδp n)).comp hHc
      (fun p hp ↦ hHm p.1 hp.2)
  have hFpsh (n : ℕ) (a : α) : DiskPshOn V (F n a) :=
    (logBarrier_psh hU hq hf hp (hδp n)).comp (hHd a) (hHm a)
  have hqc : ContinuousOn (fun p : α × E ↦ q (H p.1 p.2)) (univ ×ˢ V) :=
    hq.comp hHc (fun p hp ↦ hHm p.1 hp.2)
  have hbc : ContinuousOn (fun p : α × E ↦ q (H p.1 p.2) + ‖f (H p.1 p.2)‖)
      (univ ×ˢ V) := hqc.add (hf.continuous.continuousOn.comp hHc (fun _ _ ↦ mem_univ _)).norm
  have hbound : ∀ K : Set E, IsCompact K → K ⊆ V →
      ∃ C : ℝ, ∀ n, ∀ a, ∀ x ∈ K, ‖F n a x‖ ≤ C := by
    intro K hK hKV
    obtain ⟨C,hC⟩ := (isCompact_univ.prod hK).exists_bound_of_continuousOn
      (hbc.mono (prod_mono (Subset.refl univ) hKV))
    refine ⟨C,fun n a x hx ↦ ?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (logBarrier_nonneg q f (δ n) (H a x))]
    exact (logBarrier_le (hδp n).le (hδ1 n) (hq0 _ (hHm a (hKV hx)))).trans
      ((le_abs_self _).trans (hC (a,x) ⟨mem_univ _,hx⟩))
  apply DiskPshOn.pointwise_limit
    (u := fun n x ↦ ∫ a, F n a x ∂μ)
    (fun n ↦ DiskPshOn.integral_compact_parameter hV (hFc n) (hFpsh n))
    (continuousOn_integral_compact_parameter (μ := μ) (F := fun a x ↦ q (H a x)) hV hqc).upperSemicontinuousOn
  · intro x hx
    obtain ⟨C,hC⟩ := hbound {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    have hi (n : ℕ) : Integrable (fun a ↦ F n a x) μ := by
      have hc : Continuous (fun a ↦ F n a x) :=
        (hFc n).comp_continuous (f := fun a : α ↦ (a,x)) (by fun_prop)
          (fun _ ↦ ⟨mem_univ _,hx⟩)
      exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
    apply tendsto_integral_of_dominated_convergence (fun _ : α ↦ C)
      (fun n ↦ (hi n).aestronglyMeasurable) (integrable_const C)
      (fun n ↦ Eventually.of_forall (fun a ↦ hC n a x (mem_singleton x)))
    exact (hzero x hx).mono (fun a ha ↦
      logBarrier_tendsto_of_ne_zero hδlim ha (hq0 _ (hHm a hx)))
  · intro K hK hKV
    obtain ⟨C,hC⟩ := hbound K hK hKV
    refine ⟨C * μ.real univ,fun n x hx ↦ ?_⟩
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall (fun a ↦ hC n a x hx))

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped unitInterval
noncomputable section

lemma interval_translation_ne_zero_ae (z : ℂ) {δ : ℝ} (hδ : δ ≠ 0) :
    ∀ᵐ a : unitInterval, z + (δ : ℂ) * (a : ℝ) ≠ 0 := by
  have hinj : Function.Injective (fun a : unitInterval ↦ z + (δ : ℂ) * (a : ℝ)) := by
    intro a b hab
    apply Subtype.ext
    apply Complex.ofReal_injective
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hδ) (add_left_cancel hab)
  have hs : Set.Subsingleton {a : unitInterval | z + (δ : ℂ) * (a : ℝ) = 0} := by
    intro a ha b hb
    exact hinj (ha.trans hb.symm)
  simpa only [ae_iff, not_not] using hs.countable.measure_zero (μ := volume)

variable {V : Type u29} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [LocallyCompactSpace V]

omit [NormedSpace ℂ V] [LocallyCompactSpace V] in
lemma first_translation_continuous (δ : ℝ) :
    Continuous (fun p : unitInterval × (ℂ × V) ↦
      (p.2.1 + (δ : ℂ) * (p.1 : ℝ), p.2.2)) := by
  fun_prop

omit [NormedSpace ℂ V] [LocallyCompactSpace V] in
lemma first_translation_dist (δ : ℝ) (hδ : 0 ≤ δ) (a : unitInterval) (x : ℂ × V) :
    dist (x.1 + (δ : ℂ) * (a : ℝ), x.2) x ≤ δ := by
  change max (dist (x.1 + (δ : ℂ) * (a : ℝ)) x.1) (dist x.2 x.2) ≤ δ
  simp only [dist_self, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ, abs_of_nonneg a.property.1]
  exact max_le (mul_le_of_le_one_right hδ a.property.2) hδ

omit [NormedSpace ℂ V] [LocallyCompactSpace V] in

lemma translation_average_tendsto {q : ℂ × V → ℝ} {c : ℂ × V} {r : ℝ}
    (hr : 0 < r) (hq : ContinuousOn q (ball c r)) {x : ℂ × V}
    (hx : x ∈ ball c (r / 2)) :
    Tendsto (fun n : ℕ ↦ ∫ a : unitInterval,
      q (x.1 + ((r / (4 * ((n : ℝ) + 1)) : ℝ) : ℂ) * (a : ℝ), x.2))
      atTop (𝓝 (q x)) := by
  let δ : ℕ → ℝ := fun n ↦ r / (4 * ((n : ℝ) + 1))
  have hδp (n : ℕ) : 0 ≤ δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ r / 4 := by
    dsimp [δ]
    exact div_le_div_of_nonneg_left hr.le (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have hh := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / 4)
    convert hh using 1 <;> simp [δ, div_eq_mul_inv, mul_comm, mul_left_comm]
  have hxq : x ∈ ball c r := by exact ball_subset_ball (by linarith) hx
  have hxcont : ContinuousAt q x := (hq x hxq).continuousAt (isOpen_ball.mem_nhds hxq)
  have hmap (n : ℕ) (a : unitInterval) :
      (x.1 + (δ n : ℂ) * (a : ℝ), x.2) ∈ ball c r := by
    apply lt_of_le_of_lt (dist_triangle _ x c)
    have hd := first_translation_dist (V := V) (δ n) (hδp n) a x
    have hx' : dist x c < r / 2 := hx
    linarith [hδle n]
  obtain ⟨s, hs, hsball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hxcont (ball_mem_nhds (q x) (show 0 < (1 : ℝ) by norm_num)))
  have he : ∀ᶠ n : ℕ in atTop, δ n ≤ s :=
    (tendsto_order.1 hδlim).2 s hs
      |>.mono (fun _ h ↦ h.le)
  suffices Tendsto (fun n : ℕ ↦ ∫ a : unitInterval,
      q (x.1 + (δ n : ℂ) * (a : ℝ), x.2)) atTop
      (𝓝 (∫ _a : unitInterval, q x)) by simpa [δ] using this
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ : unitInterval ↦ ‖q x‖ + 1)
  · filter_upwards [] with n
    apply Continuous.aestronglyMeasurable
    exact (hq.comp_continuous
      (by fun_prop : Continuous (fun a : unitInterval ↦ (x.1 + (δ n : ℂ)*(a : ℝ),x.2)))
      (hmap n))
  · filter_upwards [he] with n hn
    exact Eventually.of_forall fun a ↦ by
      have hqa := hsball ((first_translation_dist (V := V) (δ n) (hδp n) a x).trans hn)
      have hdist : dist (q (x.1 + (δ n : ℂ)*(a : ℝ),x.2)) (q x) < 1 := hqa
      calc
        ‖q (x.1 + (δ n : ℂ)*(a : ℝ),x.2)‖ ≤
            dist (q (x.1 + (δ n : ℂ)*(a : ℝ),x.2)) (q x) + ‖q x‖ := by
              simpa only [dist_zero_right] using
                (dist_triangle (q (x.1 + (δ n : ℂ)*(a : ℝ),x.2)) (q x) 0)
        _ ≤ ‖q x‖ + 1 := by linarith
  · exact integrable_const _
  · exact Eventually.of_forall fun a ↦ hxcont.tendsto.comp (by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [(tendsto_order.1 hδlim).2 ε hε] with n hn
      exact (first_translation_dist (V := V) (δ n) (hδp n) a x).trans_lt hn)

theorem first_hyperplane_removable_ball {c : ℂ × V} {r : ℝ} (hr : 0 < r)
    {q : ℂ × V → ℝ} (hq : ContinuousOn q (ball c r))
    (hq0 : ∀ x ∈ ball c r, 0 ≤ q x)
    (hp : DiskPshOn (ball c r ∩ {x | x.1 ≠ 0}) q) :
    DiskPshOn (ball c (r / 2)) q := by
  let : ProperSpace (ℂ × V) := ProperSpace.of_locallyCompactSpace ℂ
  let δ : ℕ → ℝ := fun n ↦ r / (4 * ((n : ℝ) + 1))
  let H : ℕ → unitInterval → (ℂ × V) → (ℂ × V) :=
    fun n a x ↦ (x.1 + (δ n : ℂ) * (a : ℝ), x.2)
  have hδp (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ r / 4 := by
    dsimp [δ]
    exact div_le_div_of_nonneg_left hr.le (by positivity)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hmapSmall (n : ℕ) (a : unitInterval) (x : ℂ × V)
      (hx : x ∈ ball c (r / 2)) : H n a x ∈ closedBall c (3*r/4) := by
    have hd := first_translation_dist (V := V) (δ n) (hδp n).le a x
    change dist (H n a x) c ≤ 3*r/4
    have ht := dist_triangle (H n a x) x c
    have hx' : dist x c < r/2 := hx
    change dist (H n a x) x ≤ δ n at hd
    linarith [hδle n]
  have hb : closedBall c (3*r/4) ⊆ ball c r :=
    closedBall_subset_ball (by linarith)
  have hmap (n : ℕ) (a : unitInterval) : MapsTo (H n a) (ball c (r/2)) (ball c r) :=
    fun x hx ↦ hb (hmapSmall n a x hx)
  have hu (n : ℕ) : DiskPshOn (ball c (r / 2))
      (fun x ↦ ∫ a : unitInterval, q (H n a x)) := by
    apply averaged_hypersurface_removal isOpen_ball isOpen_ball hq hq0
      (f := fun x : ℂ × V ↦ x.1) differentiable_fst hp
      (first_translation_continuous (V := V) (δ n)).continuousOn
      (fun a ↦ (by fun_prop : Differentiable ℂ (H n a)).differentiableOn) (hmap n)
    intro x _
    exact interval_translation_ne_zero_ae x.1 (hδp n).ne'
  apply DiskPshOn.pointwise_limit hu
    (hq.mono (ball_subset_ball (by linarith))).upperSemicontinuousOn
  · intro x hx
    exact translation_average_tendsto hr hq hx
  · intro K _hK hKV
    obtain ⟨C,hC⟩ := (isCompact_closedBall c (3*r/4)).exists_bound_of_continuousOn (hq.mono hb)
    refine ⟨C,fun n x hx ↦ ?_⟩
    have hh := norm_integral_le_of_norm_le_const (μ := (volume : Measure unitInterval))
      (C := C) (Eventually.of_forall (fun a ↦ hC _ (hmapSmall n a x (hKV hx))))
    simpa using hh

theorem first_hyperplane_removable {U : Set (ℂ × V)} (hU : IsOpen U)
    {q : ℂ × V → ℝ} (hq : ContinuousOn q U) (hq0 : ∀ x ∈ U, 0 ≤ q x)
    (hp : DiskPshOn (U ∩ {x | x.1 ≠ 0}) q) : DiskPshOn U q := by
  apply DiskPshOn.of_locally hq
  intro x hx
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_ball.mem_iff.mp (hU.mem_nhds hx)
  refine ⟨ball x (r/2), isOpen_ball, mem_ball_self (by linarith), ?_⟩
  exact first_hyperplane_removable_ball hr (hq.mono hb) (fun y hy ↦ hq0 y (hb hy))
    (hp.mono (inter_subset_inter_left _ hb))

end
end QuadricCounterexample

end OAI
