import OAI.Analysis.HotSpots.Multiplicity

namespace OAI

section ActualBoundaryCauchySupport

section ActualZeroExtensionLayer
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace Laplacian
namespace StrictHotSpots



lemma zeroExtension_hasFDerivAt {Ω B : Set Plane} {u : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (hΩ : IsOpen Ω) (hB : IsOpen B)
    (hD : ∀ x ∈ B ∩ closure Ω, HasFDerivWithinAt u (D x) (closure Ω) x)
    (hz : ∀ x ∈ B ∩ frontier Ω, u x = 0 ∧ D x = 0)
    {x : Plane} (hx : x ∈ B) :
    HasFDerivAt (Ω.indicator u) (Ω.indicator D x) x := by
  classical
  by_cases hxi : x ∈ Ω
  · rw [indicator_of_mem hxi]
    apply ((hD x ⟨hx,subset_closure hxi⟩).hasFDerivAt
      (mem_of_superset (hΩ.mem_nhds hxi) subset_closure)).congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds hxi] with y hy
    exact indicator_of_mem hy _
  · rw [indicator_of_notMem hxi]
    by_cases hxc : x ∈ closure Ω
    · have hxf : x ∈ frontier Ω := ⟨hxc,by simpa only [hΩ.interior_eq] using hxi⟩
      have hzx := hz x ⟨hx,hxf⟩
      have heq : EqOn (Ω.indicator u) u (closure Ω ∩ B) := by
        intro y hy
        by_cases hyΩ : y ∈ Ω
        · exact indicator_of_mem hyΩ _
        · rw [indicator_of_notMem hyΩ]
          exact (hz y ⟨hy.2,hy.1,by simpa only [hΩ.interior_eq] using hyΩ⟩).1.symm
      have hh : HasFDerivWithinAt (Ω.indicator u) (0 : Plane →L[ℝ] ℝ) (closure Ω ∩ B) x := by
        rw [← hzx.2]
        exact ((hD x ⟨hx,hxc⟩).mono inter_subset_left).congr heq
          (by rw [indicator_of_notMem hxi,hzx.1])
      have hc : HasFDerivWithinAt (Ω.indicator u) (0 : Plane →L[ℝ] ℝ) (Ωᶜ ∩ B) x := by
        exact (hasFDerivWithinAt_const (𝕜 := ℝ) (s := Ωᶜ ∩ B) (0 : ℝ) x).congr
          (fun y hy => indicator_of_notMem hy.1 _) (indicator_of_notMem hxi _)
      apply (hh.union hc).hasFDerivAt
      apply mem_of_superset (hB.mem_nhds hx)
      intro y hy
      by_cases hyΩ : y ∈ Ω
      · exact Or.inl ⟨subset_closure hyΩ,hy⟩
      · exact Or.inr ⟨hyΩ,hy⟩
    · apply (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      exact indicator_of_notMem (fun hyΩ => hy (subset_closure hyΩ)) _

lemma zeroExtension_continuousOn {E : Type*} [NormedAddCommGroup E]
    {Ω B : Set Plane} {f : Plane → E}
    (hf : ContinuousOn f (B ∩ closure Ω))
    (hz : ∀ x ∈ B ∩ frontier Ω, f x = 0) : ContinuousOn (Ω.indicator f) B := by
  classical
  exact ContinuousOn.piecewise hz hf continuousOn_const

lemma weakGradient_of_continuous_derivative {B : Set Plane} {v : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (hB : IsOpen B)
    (hv : ∀ x ∈ B, HasFDerivAt v (D x) x) (hD : ContinuousOn D B)
    (hmv : MemLp v 2 (volume.restrict B))
    (hmg : MemLp (fun x => (InnerProductSpace.toDual ℝ Plane).symm (D x)) 2 (volume.restrict B)) :
    HasH1Gradient B v (fun x => (InnerProductSpace.toDual ℝ Plane).symm (D x)) := by
  refine ⟨hmv,hmg,?_⟩
  have hvc : ContinuousOn v B := fun x hx => (hv x hx).continuousAt.continuousWithinAt
  intro φ hφ hc hs e
  have he (x) : inner ℝ ((InnerProductSpace.toDual ℝ Plane).symm (D x)) e = D x e :=
    InnerProductSpace.toDual_symm_apply
  simp_rw [he]
  have hdφ : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : tsupport (fun x => fderiv ℝ φ x e) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ e).trans hs
  rw [setIntegral_mul_test hds,setIntegral_mul_test hs]
  have hd : Integrable (fun x => fderiv ℝ v x e * φ x) volume := by
    apply (integrable_mul_test hB (hD.clm_apply (continuousOn_const (c := e))) hφ.continuous hc hs).congr
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ B
      · rw [(hv x hx).fderiv]
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]; simp
  have hEq := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hd
    (integrable_mul_test hB hvc hdφ (hc.fderiv_apply ℝ e) hds)
    (integrable_mul_test hB hvc hφ.continuous hc hs)
    (fun x hx => (hv x (hs hx)).differentiableAt)
    (fun x _ => hφ.differentiable (by simp) x)
  rw [hEq]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : x ∈ B
    · rw [(hv x hx).fderiv]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]; simp

end StrictHotSpots

namespace StrictHotSpots

lemma zeroExtension_H1 {Ω B : Set Plane} {u : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (hΩ : IsOpen Ω) (hB : IsOpen B)
    (hD : ∀ x ∈ B ∩ closure Ω, HasFDerivWithinAt u (D x) (closure Ω) x)
    (hDc : ContinuousOn D (B ∩ closure Ω))
    (hz : ∀ x ∈ B ∩ frontier Ω, u x = 0 ∧ D x = 0)
    (hu : HasH1Gradient Ω u (gradient u)) :
    HasH1Gradient B (Ω.indicator u) (Ω.indicator (gradient u)) := by
  classical
  let d (x : Plane) := (InnerProductSpace.toDual ℝ Plane).symm (Ω.indicator D x)
  have hd : d =ᵐ[volume.restrict B] Ω.indicator (gradient u) := by
    filter_upwards [ae_restrict_mem hB.measurableSet] with x hx
    by_cases hxΩ : x ∈ Ω
    · have hdu := (hD x ⟨hx,subset_closure hxΩ⟩).hasFDerivAt
        (mem_of_superset (hΩ.mem_nhds hxΩ) subset_closure)
      simp only [d,indicator_of_mem hxΩ,gradient,hdu.fderiv]
    · simp only [d,indicator_of_notMem hxΩ,map_zero]
  have hmv : MemLp (Ω.indicator u) 2 (volume.restrict B) :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hu.1).mono_measure Measure.restrict_le_self
  have hmg : MemLp (Ω.indicator (gradient u)) 2 (volume.restrict B) :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hu.2.1).mono_measure Measure.restrict_le_self
  have hh := weakGradient_of_continuous_derivative hB
    (fun x hx => zeroExtension_hasFDerivAt hΩ hB hD hz hx)
    (zeroExtension_continuousOn hDc (fun x hx => (hz x hx).2)) hmv ((memLp_congr_ae hd).mpr hmg)
  refine ⟨hmv,hmg,?_⟩
  intro φ hφ hc hs e
  rw [hh.2.2 _ hφ hc hs e]
  congr 1
  apply integral_congr_ae
  filter_upwards [hd] with x hx
  rw [show (InnerProductSpace.toDual ℝ Plane).symm (Ω.indicator D x) =
    Ω.indicator (gradient u) x from hx]

lemma integral_indicator_local {Ω B : Set Plane} (hΩ : MeasurableSet Ω)
    {f : Plane → ℝ} (hf : ∀ x ∉ B, f x = 0) :
    (∫ x in B, Ω.indicator f x) = ∫ x in Ω, f x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,integral_indicator hΩ]
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · rw [indicator_of_mem hxΩ,hf x hx]
  · rw [indicator_of_notMem hxΩ]

lemma zeroExtension_weakEquation {Ω B : Set Plane} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : InInteriorNeumannEigenspace Ω u)
    (hh : HasH1Gradient B (Ω.indicator u) (Ω.indicator (gradient u))) :
    PlaneWeakEquation B (firstPositiveNeumannValue Ω) (Ω.indicator u) := by
  classical
  intro φ hφ hc hs
  rw [weak_laplacian_test hh hφ hc hs]
  have hgφ (x : Plane) (hx : x ∉ B) : gradient φ x = 0 := by
    unfold gradient
    rw [image_eq_zero_of_notMem_tsupport (f := fderiv ℝ φ)
      (fun h => hx (hs (tsupport_fderiv_subset ℝ h))),map_zero]
  have h1 : (fun x => inner ℝ (Ω.indicator (gradient u) x) (gradient φ x)) =
      Ω.indicator (fun x => inner ℝ (gradient u x) (gradient φ x)) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,inner_zero_left]
  have h2 : (fun x => Ω.indicator u x * φ x) = Ω.indicator (fun x => u x * φ x) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,zero_mul]
  rw [h1,h2,integral_indicator_local hΩ.measurableSet
    (fun x hx => by rw [hgφ x hx,inner_zero_right]),
    integral_indicator_local hΩ.measurableSet
    (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),mul_zero]),
    hu.2.2.2 φ (gradient φ) (HasH1Gradient.test hΩ hφ hc),neg_mul]




theorem interior_eigenfunction_zero_of_boundary_jet {Ω B : Set Plane} {u : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (hΩ : IsOpen Ω) (hcΩ : IsPreconnected Ω)
    (hbΩ : Bornology.IsBounded Ω) (hB : IsOpen B) (hcB : IsPreconnected B)
    (hbB : Bornology.IsBounded B) (hu : InInteriorNeumannEigenspace Ω u)
    (hD : ∀ x ∈ B ∩ closure Ω, HasFDerivWithinAt u (D x) (closure Ω) x)
    (hDc : ContinuousOn D (B ∩ closure Ω))
    (hz : ∀ x ∈ B ∩ frontier Ω, u x = 0 ∧ D x = 0)
    (hin : (B ∩ Ω).Nonempty)
    (hout : ∃ a ∈ B, ∃ ε > 0, ball a ε ⊆ Ωᶜ) :
    EqOn u 0 Ω := by
  classical
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hbB.measure_lt_top.ne
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hbΩ.measure_lt_top.ne
  have hh := zeroExtension_H1 hΩ hB hD hDc hz hu.2.1
  have hW := zeroExtension_weakEquation hΩ hu hh
  have hext : ∀ᵐ x ∂volume, x ∈ B → Ω.indicator u x = 0 := by
    apply planeWeak_uniqueContinuation hB hcB (hh.1.integrable (by norm_num)) hW
    obtain ⟨a,ha,ε,hε,hs⟩ := hout
    refine ⟨a,ha,ε,hε,Eventually.of_forall fun x hx => ?_⟩
    exact indicator_of_notMem (hs hx) _
  have hu0 : ∀ᵐ x ∂volume, x ∈ Ω → u x = 0 := by
    apply planeWeak_uniqueContinuation hΩ hcΩ (hu.2.1.1.integrable (by norm_num))
      (planeWeakEquation_of_euler hΩ hu.2.1 hu.2.2.2)
    obtain ⟨a,ha⟩ := hin
    obtain ⟨ε,hε,hs⟩ := Metric.isOpen_iff.mp (hB.inter hΩ) a ha
    refine ⟨a,ha.2,ε,hε,?_⟩
    filter_upwards [hext] with x hx hxball
    have hm := hs hxball
    simpa only [indicator_of_mem hm.2] using hx hm.1
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hΩ.measurableSet).mpr hu0) hΩ
    hu.1.continuousOn continuousOn_const

end StrictHotSpots

end
end ActualZeroExtensionLayer
section ActualBoundaryLocalConstLayer
noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff
namespace StrictHotSpots

lemma nonzero_real_functional_surjective (D : Plane →L[ℝ] ℝ) (hD : D ≠ 0) :
    D.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  have hn : ∃ v, D v ≠ 0 := by
    by_contra hh
    apply hD
    ext v
    simpa using not_exists.mp hh v
  obtain ⟨v,hv⟩ := hn
  intro t
  refine ⟨(t / D v) • v,?_⟩
  simp [map_smul,div_mul_cancel₀ _ hv]

lemma frontier_level_zero {Ω U : Set Plane} {ρ : Plane → ℝ} {p : Plane}
    (ho : IsOpen Ω) (hU : IsOpen U) (hpU : p ∈ U) (hp : p ∈ frontier Ω)
    (hc : ContinuousAt ρ p)
    (he : Ω ∩ U = {x | ρ x < 0} ∩ U) : ρ p = 0 := by
  apply le_antisymm
  · by_contra hh
    have ht : ∀ᶠ x in 𝓝 p, x ∈ U ∧ 0 < ρ x :=
      (show ∀ᶠ x in 𝓝 p, x ∈ U from hU.mem_nhds hpU).and
        (hc (lt_mem_nhds (lt_of_not_ge hh)))
    obtain ⟨x,hx,hxU,hpx⟩ := (mem_closure_iff_frequently.mp hp.1).and_eventually ht |>.exists
    have hz : ρ x < 0 := (he ▸ (show x ∈ Ω ∩ U from ⟨hx,hxU⟩)).1
    exact (not_lt_of_ge hpx.le) hz
  · by_contra hh
    have hm : p ∈ Ω := ((he.symm ▸ (show p ∈ {x | ρ x < 0} ∩ U from
      ⟨lt_of_not_ge hh,hpU⟩)) : p ∈ Ω ∩ U).1
    exact hp.2 (ho.interior_eq.symm ▸ hm)

lemma regular_level_mem_frontier {Ω U : Set Plane} {ρ : Plane → ℝ} {p : Plane}
    (ho : IsOpen Ω) (hU : IsOpen U) (hpU : p ∈ U)
    (hc : DifferentiableAt ℝ ρ p) (hD : fderiv ℝ ρ p ≠ 0) (hpρ : ρ p = 0)
    (he : Ω ∩ U = {x | ρ x < 0} ∩ U) : p ∈ frontier Ω := by
  obtain ⟨v,hv⟩ : ∃ v, fderiv ℝ ρ p v = -1 :=
    LinearMap.range_eq_top.mp (nonzero_real_functional_surjective _ hD) (-1)
  have ht : Tendsto (fun t : ℝ => p+t•v) (𝓝[>] 0) (𝓝 p) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_id'.mpr (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const v)
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ), p+t•v ∈ Ω := by
    filter_upwards [HasFDerivAt.eventually_lt_along_ray hc.hasFDerivAt
      (show fderiv ℝ ρ p v < 0 by rw [hv]; norm_num),ht (hU.mem_nhds hpU)] with t hneg htU
    exact ((he.symm ▸ (show p+t•v ∈ {x | ρ x < 0} ∩ U from
      ⟨by change ρ (p+t•v) < 0; simpa only [hpρ] using hneg,htU⟩)) : p+t•v ∈ Ω ∩ U).1
  refine ⟨mem_closure_of_tendsto ht hm,?_⟩
  rw [ho.interior_eq]
  intro hh
  have hz : ρ p < 0 := (he ▸ (show p ∈ Ω ∩ U from ⟨hh,hpU⟩)).1
  simp only [hpρ,lt_self_iff_false] at hz





theorem SmoothBoundary.locally_const_of_boundary_zero_jet
    {Ω O : Set Plane} {u : Plane → ℝ} (hs : SmoothBoundary Ω) (ho : IsOpen Ω)
    {p : Plane} (hp : p ∈ frontier Ω)
    (hO : IsOpen O) (hpO : p ∈ O)
    (hz : ∀ x ∈ O ∩ frontier Ω, HasFDerivWithinAt u (0 : Plane →L[ℝ] ℝ) (closure Ω) x) :
    ∃ V : Set Plane, IsOpen V ∧ p ∈ V ∧ ∀ x ∈ V ∩ frontier Ω, u x = u p := by
  obtain ⟨U,ρ,hU,hpU,hρ,hD,hpρ,he⟩ := hs p hp
  have hρat : ContDiffAt ℝ ∞ ρ p := (hρ p hpU).contDiffAt (hU.mem_nhds hpU)
  let D := fderiv ℝ ρ p
  let hker := D.ker_closedComplemented_of_finiteDimensional_range
  let φ := HasStrictFDerivAt.implicitFunctionDataOfComplemented ρ D
    (hρat.hasStrictFDerivAt (by simp)) (nonzero_real_functional_surjective D hD) hker
  have hφp : φ.prodFun p = (0,0) := by
    simp [φ,ImplicitFunctionData.prodFun,hpρ]
  have hr : ContDiff ℝ ∞ φ.rightFun := by
    change ContDiff ℝ ∞ (fun x => Classical.choose hker (x-p))
    fun_prop
  have hcunc : ContDiffAt ℝ 1 φ.implicitFunction.uncurry (0,0) := by
    rw [← hφp]
    exact φ.contDiffAt_implicitFunction (hρat.of_le (by simp))
      (hr.contDiffAt.of_le (by simp)) (by simp)
  let c : D.ker → Plane := φ.implicitFunction 0
  have hc : ContDiffAt ℝ 1 c 0 := by
    exact hcunc.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hcp : c 0 = p := by
    have hh := φ.toOpenPartialHomeomorph.left_inv φ.pt_mem_toOpenPartialHomeomorph_source
    change φ.implicitFunction (φ.prodFun p).1 (φ.prodFun p).2 = p at hh
    simpa only [hφp] using hh
  have ht : Tendsto (fun y : D.ker => (0,y)) (𝓝 0) (𝓝 (φ.prodFun p)) := by
    rw [hφp]
    exact tendsto_const_nhds.prodMk_nhds tendsto_id
  have hcρ : ∀ᶠ y in 𝓝 (0 : D.ker), ρ (c y) = 0 := ht φ.leftFun_implicitFunction
  have hct : Tendsto c (𝓝 (0 : D.ker)) (𝓝 p) := hcp ▸ hc.continuousAt.tendsto
  have hdn := hct ((hρat.continuousAt_fderiv (by simp)).eventually_ne hD)
  have hgood : ∀ᶠ y in 𝓝 (0 : D.ker), DifferentiableAt ℝ c y ∧ c y ∈ O ∩ frontier Ω := by
    filter_upwards [hc.eventually (by simp),hcρ,hdn,hct (hU.mem_nhds hpU),
      hct (hO.mem_nhds hpO)] with y hcy hρy hdy hyU hyO
    refine ⟨hcy.differentiableAt (by simp),hyO,?_⟩
    exact regular_level_mem_frontier ho hU hyU
      (((hρ (c y) hyU).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp))
      hdy hρy he
  obtain ⟨ε,hε,hεgood⟩ := Metric.eventually_nhds_iff.mp hgood
  have hfzero (y : D.ker) (hy : y ∈ ball 0 ε) : HasFDerivAt (u ∘ c) (0 : D.ker →L[ℝ] ℝ) y := by
    have hygood := hεgood hy
    have hdu := hz (c y) hygood.2
    have hmaps : ∀ᶠ z in 𝓝 y, c z ∈ closure Ω := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      exact (hεgood hz).2.2.1
    simpa only [ContinuousLinearMap.zero_comp] using
      hdu.comp_hasFDerivAt y hygood.1.hasFDerivAt hmaps
  have hconst (y : D.ker) (hy : y ∈ ball 0 ε) : u (c y) = u p := by
    have hh := (convex_ball (0 : D.ker) ε).is_const_of_fderivWithin_eq_zero
      (fun z hz => (hfzero z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hfzero z hz).hasFDerivWithinAt.fderivWithin
        (isOpen_ball.uniqueDiffOn z hz)) hy (mem_ball_self hε)
    exact hh.trans (congrArg u hcp)
  have hright0 : φ.rightFun p = 0 := congrArg Prod.snd hφp
  have hry : ∀ᶠ x in 𝓝 p, φ.rightFun x ∈ ball 0 ε := by
    exact hr.continuous.continuousAt.tendsto
      (hright0.symm ▸ (isOpen_ball.mem_nhds (mem_ball_self hε)))
  have hloc : ∀ᶠ x in 𝓝 p, x ∈ frontier Ω → u x = u p := by
    filter_upwards [hU.mem_nhds hpU,hry,φ.implicitFunction_apply_image] with x hxU hxy hix
    intro hxf
    have hzρ := frontier_level_zero ho hU hxU hxf
      ((hρ x hxU).continuousWithinAt.continuousAt (hU.mem_nhds hxU)) he
    have hic : c (φ.rightFun x) = x := by
      change φ.implicitFunction 0 (φ.rightFun x) = x
      change φ.implicitFunction (ρ x) (φ.rightFun x) = x at hix
      simpa only [hzρ] using hix
    exact hic ▸ hconst _ hxy
  obtain ⟨V,hV,hVo,hpV⟩ := _root_.mem_nhds_iff.mp hloc
  exact ⟨V,hVo,hpV,fun x hx => hV hx.1 hx.2⟩

end StrictHotSpots

end
end ActualBoundaryLocalConstLayer
end ActualBoundaryCauchySupport

section ClosedEigenLocalRank

noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots
namespace Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
include c



theorem eq_zero_of_boundary_closedGradient (hΩ : AdmissibleDomain Ω)
    {v : Plane → ℝ} (hv : InInteriorNeumannEigenspace Ω v)
    (hvc : ContinuousOn v (closure Ω)) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    {p : Plane} (hp : p ∈ frontier Ω) {U : Set Plane} (hU : IsOpen U) (hpU : p ∈ U)
    (hz : ∀ x ∈ U ∩ frontier Ω, v x = 0 ∧ Y x = 0) : EqOn v 0 Ω := by
  obtain ⟨ε,hε,hεU⟩ := Metric.isOpen_iff.mp hU p hpU
  let D : Plane → Plane →L[ℝ] ℝ := fun x => InnerProductSpace.toDual ℝ Plane (Y x)
  apply interior_eigenfunction_zero_of_boundary_jet hΩ.2.1
    hΩ.2.2.2.1.isPathConnected.isConnected.isPreconnected hΩ.2.2.1
    isOpen_ball (convex_ball p ε).isPreconnected isBounded_ball hv (D := D)
  · intro x hx
    by_cases hxi : x ∈ Ω
    · have hd := (hv.differentiableAt hΩ.2.1 hxi).hasFDerivAt.hasFDerivWithinAt (s := closure Ω)
      have hh : fderiv ℝ v x = D x := by
        change fderiv ℝ v x = InnerProductSpace.toDual ℝ Plane (Y x)
        rw [← he hxi]
        exact (InnerProductSpace.toDual ℝ Plane).apply_symm_apply _ |>.symm
      rwa [hh] at hd
    · have hxf : x ∈ frontier Ω := ⟨hx.2,by simpa only [hΩ.2.1.interior_eq] using hxi⟩
      have hh := (hz x ⟨hεU hx.1,hxf⟩).2
      have hd := c.hasFDerivWithinAt_zero_of_closedGradient_zero hv.1 hvc hY he hx.2 hh
      simpa only [D,hh,map_zero] using hd
  · exact ((InnerProductSpace.toDual ℝ Plane).continuous.comp_continuousOn hY).mono inter_subset_right
  · intro x hx
    have hh := hz x ⟨hεU hx.1,hx.2⟩
    exact ⟨hh.1,by simp only [D,hh.2,map_zero]⟩
  · obtain ⟨x,hx,hxp⟩ := Metric.mem_closure_iff.mp hp.1 ε hε
    exact ⟨x,by simpa only [mem_ball,dist_comm] using hxp,hx⟩
  · exact hΩ.2.2.2.2.exterior_ball_in_neighborhood hp isOpen_ball (mem_ball_self hε)
end Conformal.ClosedDiskChart


def closedPatchEigenSpace (Ω O : Set Plane) (hΩ : AdmissibleDomain Ω) :
    Submodule ℝ (ClosedEigenJet Ω) where
  carrier := {J | J ∈ closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 ∧
    ∀ x : closure Ω, (x : Plane) ∈ O ∩ frontier Ω → J.2 x = 0}
  zero_mem' := ⟨(closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1).zero_mem,by simp⟩
  add_mem' := by
    intro J K hJ hK
    refine ⟨(closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1).add_mem hJ.1 hK.1,?_⟩
    intro x hx
    change J.2 x + K.2 x = 0
    rw [hJ.2 x hx,hK.2 x hx,add_zero]
  smul_mem' := by
    intro a J hJ
    refine ⟨(closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1).smul_mem a hJ.1,?_⟩
    intro x hx
    change a • J.2 x = 0
    rw [hJ.2 x hx,smul_zero]

def closedPatchEval {Ω O : Set Plane} (hΩ : AdmissibleDomain Ω) {p : Plane}
    (hp : p ∈ frontier Ω) : closedPatchEigenSpace Ω O hΩ →ₗ[ℝ] ℝ where
  toFun J := J.val.1 ⟨p,hp.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma closedPatchEval_injective {Ω O : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) {p : Plane} (hp : p ∈ frontier Ω) (hO : IsOpen O) (hpO : p ∈ O) :
    Injective (closedPatchEval (O := O) hΩ hp) := by
  have hzero (J : closedPatchEigenSpace Ω O hΩ) (hJ : closedPatchEval hΩ hp J = 0) : J = 0 := by
    obtain ⟨v,Y,hv,hvc,hY,he,hjet⟩ := J.property.1
    have hz (x : Plane) (hx : x ∈ O ∩ frontier Ω) : Y x = 0 := by
      have h := J.property.2 ⟨x,hx.2.1⟩ hx
      rw [← hjet] at h
      exact h
    have hd (x : Plane) (hx : x ∈ O ∩ frontier Ω) :
        HasFDerivWithinAt v (0 : Plane →L[ℝ] ℝ) (closure Ω) x :=
      c.hasFDerivWithinAt_zero_of_closedGradient_zero hv.1 hvc hY he hx.2.1 (hz x hx)
    obtain ⟨V,hV,hpV,hconst⟩ := hΩ.2.2.2.2.locally_const_of_boundary_zero_jet hΩ.2.1 hp hO hpO hd
    have hvp : v p = 0 := by
      change J.val.1 ⟨p,hp.1⟩ = 0 at hJ
      rw [← hjet] at hJ
      exact hJ
    have hv0 : EqOn v 0 Ω := c.eq_zero_of_boundary_closedGradient hΩ hv hvc hY he hp
      (hV.inter hO) ⟨hpV,hpO⟩
      (fun x hx => ⟨(hconst x ⟨hx.1.1,hx.2⟩).trans hvp,hz x ⟨hx.1.2,hx.2⟩⟩)
    apply Subtype.ext
    exact hjet.symm.trans (closedEigenJet_eq_zero_of_eqOn hΩ.2.1 hvc hY he hv0)
  intro J K hJK
  apply sub_eq_zero.mp
  apply hzero (J-K)
  change J.val.1 ⟨p,hp.1⟩ - K.val.1 ⟨p,hp.1⟩ = 0
  exact sub_eq_zero.mpr hJK


theorem closedPatchEigenSpace_finrank_le_one {Ω O : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) {p : Plane} (hp : p ∈ frontier Ω) (hO : IsOpen O) (hpO : p ∈ O) :
    Module.Finite ℝ (closedPatchEigenSpace Ω O hΩ) ∧
      Module.finrank ℝ (closedPatchEigenSpace Ω O hΩ) ≤ 1 := by
  have hi := closedPatchEval_injective c hΩ hp hO hpO
  have hf := Module.Finite.of_injective (closedPatchEval (O := O) hΩ hp) hi
  let : Module.Finite ℝ (closedPatchEigenSpace Ω O hΩ) := hf
  exact ⟨hf,by simpa using LinearMap.finrank_le_finrank_of_injective hi⟩
end StrictHotSpots
end
end ClosedEigenLocalRank



end OAI
