import OAI.Geometry.Perimeter.Regularity.GraphPhase

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

def graphCylinder (v : Euc n) : Set (Euc n) :=
  {x | ‖normalProjection v x‖<1/4 ∧ |inner ℝ v x|<1/2}

def graphDefining (v : Euc n) (f : normalPlane v → ℝ) (x : Euc n) : ℝ :=
  inner ℝ v x-f (normalProjection v x)

theorem graphCylinder_open (v : Euc n) : IsOpen (graphCylinder v) :=
  (isOpen_lt (normalProjection v).continuous.norm continuous_const).inter
    (isOpen_lt (show Continuous (fun x : Euc n ↦ |inner ℝ v x|) from
      ((innerSL ℝ v).continuous).abs) continuous_const)

@[simp] theorem graphDefining_fiber {v : Euc n} (hv : ‖v‖=1)
    (f : normalPlane v → ℝ) (y : normalPlane v) (t : ℝ) :
    graphDefining v f ((y:Euc n)+t•v)=t-f y := by
  simp only [graphDefining,normalProjection_fiber,normal_fiber_inner hv]

@[simp] theorem graphCylinder_fiber {v : Euc n} (hv : ‖v‖=1)
    (y : normalPlane v) (t : ℝ) :
    (y:Euc n)+t•v∈graphCylinder v ↔ ‖y‖<1/4 ∧ |t|<1/2 := by
  simp only [graphCylinder,mem_ofPred_eq,normalProjection_fiber,normal_fiber_inner hv]

theorem graphCylinder_norm_lt_one {v : Euc n} (hv : ‖v‖=1)
    {x : Euc n} (hx : x∈graphCylinder v) : ‖x‖<1 := by
  obtain ⟨⟨y,t⟩,rfl⟩ := (normalCoordinates v hv).surjective x
  simp only [normalCoordinates_apply,graphCylinder_fiber hv] at hx ⊢
  have hh := norm_add_le (y:Euc n) (t•v)
  rw [norm_smul,Real.norm_eq_abs,hv,mul_one] at hh
  rw [Submodule.norm_coe] at hh
  linarith [hx.1,hx.2]

theorem graphDefining_contDiffOn {v : Euc n} {f : normalPlane v → ℝ} {k : ℕ∞ω}
    (hf : ContDiffOn ℝ k f (Metric.ball 0 (1/4))) :
    ContDiffOn ℝ k (graphDefining v f) (graphCylinder v) := by
  apply (contDiff_const.inner ℝ contDiff_id).contDiffOn.sub
  exact hf.comp (normalProjection v).contDiff.contDiffOn (fun x hx ↦ by
    simpa only [Metric.mem_ball,dist_zero_right] using hx.1)

theorem graphDefining_hasFDerivAt {v : Euc n} {f : normalPlane v → ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4))) {x : Euc n}
    (hx : x∈graphCylinder v) :
    HasFDerivAt (graphDefining v f)
      ((innerSL ℝ v)-(fderiv ℝ f (normalProjection v x)).comp (normalProjection v)) x := by
  have hy : normalProjection v x∈Metric.ball 0 (1/4) := by
    simpa only [Metric.mem_ball,dist_zero_right] using hx.1
  have hfd : DifferentiableAt ℝ f (normalProjection v x) :=
    (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hy)).differentiableAt (by norm_num)
  exact (innerSL ℝ v).hasFDerivAt.sub (hfd.hasFDerivAt.comp x (normalProjection v).hasFDerivAt)

theorem graphDefining_fderiv_normal {v : Euc n} (hv : ‖v‖=1)
    {f : normalPlane v → ℝ} (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)))
    {x : Euc n} (hx : x∈graphCylinder v) : fderiv ℝ (graphDefining v f) x v=1 := by
  rw [(graphDefining_hasFDerivAt hf hx).fderiv]
  have hvp : normalProjection v v=0 := by
    simpa only [Submodule.coe_zero,zero_add,one_smul] using normalProjection_fiber v 0 1
  simp only [sub_apply,ContinuousLinearMap.comp_apply,hvp,map_zero,sub_zero]
  change inner ℝ v v=1
  rw [real_inner_self_eq_norm_sq,hv,one_pow]

theorem graphDefining_fderiv_ne_zero {v : Euc n} (hv : ‖v‖=1)
    {f : normalPlane v → ℝ} (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)))
    {x : Euc n} (hx : x∈graphCylinder v) : fderiv ℝ (graphDefining v f) x≠0 := by
  intro h
  have hh := graphDefining_fderiv_normal hv hf hx
  rw [h,zero_apply] at hh
  norm_num at hh

theorem graphDefining_support_iff {v : Euc n} (hv : ‖v‖=1) {E : Set (Euc n)}
    {f : normalPlane v → ℝ}
    (hiff : ∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
      ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y))
    {x : Euc n} (hx : x∈graphCylinder v) : x∈perimeterSupport E ↔ graphDefining v f x=0 := by
  obtain ⟨⟨y,t⟩,rfl⟩ := (normalCoordinates v hv).surjective x
  simp only [normalCoordinates_apply] at hx ⊢
  have hh := (graphCylinder_fiber hv y t).mp hx
  rw [graphDefining_fiber hv,sub_eq_zero]
  exact hiff y t hh.1 (graphCylinder_norm_lt_one hv hx)

theorem graphDefining_phaseSupport_iff (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0≤a) (ha4 : a<1/4)
    (hs : FullSlab E v 8 a) {f : normalPlane v → ℝ}
    (hiff : ∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
      ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y))
    {x : Euc n} (hx : x∈graphCylinder v) :
    x∈(volume.restrict E).support ↔ graphDefining v f x≤0 := by
  obtain ⟨⟨y,t⟩,rfl⟩ := (normalCoordinates v hv).surjective x
  simp only [normalCoordinates_apply] at hx ⊢
  have hh := (graphCylinder_fiber hv y t).mp hx
  rw [graphDefining_fiber hv,sub_nonpos]
  exact full_graph_phaseSupport_iff hn hmin hv ha ha4 hs hiff y hh.1 t hh.2

theorem graphDefining_approximateNormal (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0≤a) (ha4 : a<1/4)
    (hs : FullSlab E v 8 a) {f : normalPlane v → ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)))
    (hiff : ∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
      ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y))
    {x : Euc n} (hx : x∈graphCylinder v) (hxS : x∈perimeterSupport E) :
    approximateNormal E x=‖gradient (graphDefining v f) x‖⁻¹ • gradient (graphDefining v f) x := by
  let K := (volume.restrict E).support
  have hlocal : ∀ᶠ z in 𝓝 x, (graphDefining v f z<0 → z∈K) ∧
      (z∈K → graphDefining v f z≤0) := by
    filter_upwards [(graphCylinder_open v).mem_nhds hx] with z hz
    have hh := graphDefining_phaseSupport_iff hn hmin hv ha ha4 hs hiff hz
    exact ⟨fun h ↦ hh.mpr h.le,hh.mp⟩
  have hbl := hasHalfspaceBlowup_gradient_filled Measure.isClosed_support.measurableSet
    (graphDefining_hasFDerivAt hf hx).differentiableAt
    ((graphDefining_support_iff hv hiff hx).mp hxS) (graphDefining_fderiv_ne_zero hv hf hx) hlocal
  have hae := minimizing_ae_eq_phaseSupport
    (Real.HolderConjugate.conjExponent (by exact_mod_cast hn : 1<(n:ℝ))) hmin
  exact approximateNormal_eq_of_blowup hmin.1 ((hasHalfspaceBlowup_iff_of_ae hae x _).mpr hbl)

end RPISingularHarnack

end

end OAI
