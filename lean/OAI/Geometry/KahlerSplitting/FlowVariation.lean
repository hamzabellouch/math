import OAI.Geometry.KahlerSplitting.Picard

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology
open scoped ContDiff
open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem picard_initial_variation (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p v : E} {z : ℂ} {ψ : ℂ → FlowPath E} {Z : FlowPath E}
    (hψ : HasDerivAt ψ Z 0) (hr : range (ψ 0) ⊆ U)
    (heq : ∀ᶠ w in 𝓝 (0 : ℂ),
      ψ w = ContinuousMap.const FlowTime (p+w•v) + z • picardIntegral V (ψ w)) :
    Z = ContinuousMap.const FlowTime v +
      z • pathPrimitiveL (pathLinearApply (D.comp (ψ 0)) Z) := by
  have hi := (hasFDerivAt_picardIntegral V D hU hder hr).comp_hasDerivAt 0 hψ
  have hp := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add p
  have hc := (ContinuousLinearMap.const ℂ FlowTime : E →L[ℂ] FlowPath E).hasFDerivAt.comp_hasDerivAt 0 hp
  have hh := hc.add (hi.const_smul z)
  have he : HasDerivAt ψ (ContinuousMap.const FlowTime v +
      z • pathPrimitiveL (pathLinearApply (D.comp (ψ 0)) Z)) 0 := by
    convert! hh.congr_of_eventuallyEq heq using 1
    simp
    rfl
  exact hψ.unique he

theorem commuting_field_picard_equation (V W : C(E,E)) (D : C(E,E →L[ℂ] E))
    (DW : E → E →L[ℂ] E) {U : Set E}
    (hW : ∀ x ∈ U, HasFDerivAt W (DW x) x)
    (hcomm : ∀ x ∈ U, DW x (V x) = D x (W x))
    {p : E} {z : ℂ} {γ : FlowPath E} (hr : range γ ⊆ U)
    (heq : γ = ContinuousMap.const FlowTime p + z • picardIntegral V γ) :
    W.comp γ = ContinuousMap.const FlowTime (W p) +
      z • pathPrimitiveL (pathLinearApply (D.comp γ) (W.comp γ)) := by
  let η := picardRealExtension V p z γ
  let B := pathLinearApply (D.comp γ) (W.comp γ)
  have hη (u : FlowTime) : η u = γ u := picardRealExtension_eq V heq u
  have hd (u : FlowTime) : HasDerivAt (fun v : ℝ ↦ W (η v))
      (z • pathExtend B u) u := by
    have ht := picardRealExtension_hasDerivAt V p z γ u.val
    have hv := ((hW (γ u) (hr (mem_range_self u))).restrictScalars ℝ)
    rw [← hη u] at hv
    have hc := hv.comp_hasDerivAt u.val ht
    convert! hc using 1
    rw [pathExtend_apply,hη u,pathExtend_apply]
    change z • D (γ u) (W (γ u)) = DW (γ u) (z • V (γ u))
    rw [map_smul,hcomm _ (hr (mem_range_self u))]
  ext t
  have hderiv (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) t.val) :
      HasDerivAt (fun v : ℝ ↦ W (η v)) (z • pathExtend B u) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hu
      exact ⟨hu.1,hu.2.trans t.property.2⟩
    exact hd ⟨u,hu'⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (((pathExtend B).continuous.const_smul z).intervalIntegrable 0 t.val)
  rw [intervalIntegral.integral_smul,hη t] at hi
  have hη0 : η 0 = p := by simp [η,picardRealExtension]
  rw [hη0] at hi
  change W (γ t) = W p + z • ∫ u in (0 : ℝ)..t.val, pathExtend B u
  exact (sub_eq_iff_eq_add.mp hi.symm).trans (add_comm _ _)

theorem picard_endpoint_preserves_commuting_field (V W : C(E,E))
    (D : C(E,E →L[ℂ] E)) (DW : E → E →L[ℂ] E)
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    (hW : ∀ x ∈ U, HasFDerivAt W (DW x) x)
    (hcomm : ∀ x ∈ U, DW x (V x) = D x (W x))
    {p : E} {z : ℂ} {ψ : ℂ → FlowPath E} {Z : FlowPath E}
    (hψ : HasDerivAt ψ Z 0) (hr : range (ψ 0) ⊆ U)
    (heq : ∀ᶠ w in 𝓝 (0 : ℂ), ψ w =
      ContinuousMap.const FlowTime (p+w•W p) + z • picardIntegral V (ψ w))
    (hz : ‖z‖ * ‖D.comp (ψ 0)‖ < 1) :
    HasDerivAt (fun w ↦ ψ w ⟨1,zero_le_one,le_rfl⟩)
      (W (ψ 0 ⟨1,zero_le_one,le_rfl⟩)) 0 := by
  have hZ := picard_initial_variation V D hU hV hψ hr heq
  have heq0 : ψ 0 = ContinuousMap.const FlowTime p + z • picardIntegral V (ψ 0) := by
    simpa using heq.self_of_nhds
  have hY := commuting_field_picard_equation V W D DW hW hcomm hr heq0
  have hZY := picard_linear_unique (D.comp (ψ 0)) hz hZ hY
  have hEval := (ContinuousMap.evalCLM (R := ℂ) (M := E)
    (⟨1,zero_le_one,le_rfl⟩ : FlowTime)).hasFDerivAt.comp_hasDerivAt 0 hψ
  convert! hEval using 1
  rw [hZY]; rfl

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem exists_small_holomorphic_picard_family (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ W : Set (FlowParameter E), IsOpen W ∧ (p,0) ∈ W ∧
      ∃ φ : FlowParameter E → FlowPath E,
        ContDiffOn ℂ 1 φ W ∧ φ (p,0) = ContinuousMap.const FlowTime p ∧
        ∀ q ∈ W, range (φ q) ⊆ U ∧
          φ q = ContinuousMap.const FlowTime q.1 + q.2 • picardIntegral V (φ q) ∧
          ‖q.2‖ * ‖D.comp (φ q)‖ < 1 := by
  obtain ⟨O,hOo,hOp,φ,hφ,hφbase,heq⟩ := exists_holomorphic_picard_family V D hU hder hp
  have hcφ : ContinuousAt φ (p,0) := hφ.continuousOn.continuousAt (hOo.mem_nhds hOp)
  have hcD : ContinuousAt (fun q : E × ℂ ↦ D.comp (φ q)) (p,0) := by
    convert! D.continuous_postcomp.continuousAt.comp hcφ
  have hn : Continuous (fun A : C(FlowTime,E →L[ℂ] E) ↦ ‖A‖) := by
    convert! @continuous_norm C(FlowTime,E →L[ℂ] E) inferInstance
  have hcNorm : ContinuousAt (fun q : E × ℂ ↦ ‖q.2‖ * ‖D.comp (φ q)‖) (p,0) :=
    continuous_snd.continuousAt.norm.mul (hn.continuousAt.comp hcD)
  have hsmall : ∀ᶠ q : E × ℂ in 𝓝 (p,0), ‖q.2‖ * ‖D.comp (φ q)‖ < 1 := by
    apply hcNorm.eventually_lt continuousAt_const
    simp
  have hboth : O ∩ {q | ‖q.2‖ * ‖D.comp (φ q)‖ < 1} ∈ 𝓝 (p,0) :=
    inter_mem (hOo.mem_nhds hOp) hsmall
  obtain ⟨W,hWO,hWo,hWp⟩ := _root_.mem_nhds_iff.mp hboth
  refine ⟨W,hWo,hWp,φ,hφ.mono (fun q hq ↦ (hWO hq).1),hφbase,?_⟩
  intro q hq
  exact ⟨(heq q (hWO hq).1).1,(heq q (hWO hq).1).2,(hWO hq).2⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem picard_endpoint_hasDerivAt (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} {z : ℂ} {ψ : ℂ → FlowPath E} {Z : FlowPath E}
    (hψ : HasDerivAt ψ Z z) (hr : range (ψ z) ⊆ U)
    (heq : ∀ᶠ w in 𝓝 z, ψ w = ContinuousMap.const FlowTime p + w • picardIntegral V (ψ w))
    (hz : ‖z‖ * ‖D.comp (ψ z)‖ < 1) :
    HasDerivAt (fun w ↦ ψ w ⟨1,zero_le_one,le_rfl⟩)
      (V (ψ z ⟨1,zero_le_one,le_rfl⟩)) z := by
  have hZ := picard_variation_equation V D hU hder hψ hr heq
  have hY := picardTimeVariation_equation V D hder hr heq.self_of_nhds
  have hZY := picard_linear_unique (D.comp (ψ z)) hz hZ hY
  have he := (ContinuousMap.evalCLM (R := ℂ) (M := E)
    (⟨1,zero_le_one,le_rfl⟩ : FlowTime)).hasFDerivAt.comp_hasDerivAt z hψ
  convert! he using 1
  rw [hZY]
  simp [picardTimeVariation]

theorem exists_holomorphic_flow_representatives (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ W : Set (E × ℂ), IsOpen W ∧ (p,0) ∈ W ∧
      ∃ F : E × ℂ → E,
        ContDiffOn ℂ 1 F W ∧ MapsTo F W U ∧
        (∀ x, (x,0) ∈ W → F (x,0) = x) ∧
        (∀ q ∈ W, HasDerivAt (fun z ↦ F (q.1,z)) (V (F q)) q.2) := by
  obtain ⟨W,hWo,hWp,φ,hφ,hφbase,heq⟩ :=
    exists_small_holomorphic_picard_family V D hU hder hp
  let e₁ : FlowTime := ⟨1,zero_le_one,le_rfl⟩
  let F : E × ℂ → E := fun q ↦ φ q e₁
  refine ⟨W,hWo,hWp,F,?_,?_,?_,?_⟩
  · exact (ContinuousMap.evalCLM (R := ℂ) (M := E) e₁).contDiff.comp_contDiffOn
      hφ
  · intro q hq
    exact (heq q hq).1 (mem_range_self e₁)
  · intro x hx
    have h := congrArg (fun γ : FlowPath E ↦ γ e₁) (heq (x,0) hx).2.1
    simpa [F] using h
  · intro q hq
    have hφq : DifferentiableAt ℂ φ q :=
      (hφ.contDiffAt (hWo.mem_nhds hq)).differentiableAt (by norm_num)
    have hem : DifferentiableAt ℂ (fun z : ℂ ↦ (q.1,z)) q.2 :=
      (differentiableAt_const q.1).prodMk differentiableAt_id
    have hψ := (hφq.comp q.2 hem).hasDerivAt
    have heq' : ∀ᶠ z in 𝓝 q.2,
        φ (q.1,z) = ContinuousMap.const FlowTime q.1 + z • picardIntegral V (φ (q.1,z)) := by
      have hn := hem.continuousAt.tendsto.eventually (hWo.mem_nhds hq)
      filter_upwards [hn] with z hz
      exact (heq _ hz).2.1
    exact picard_endpoint_hasDerivAt V D hU hder hψ (heq q hq).1 heq' (heq q hq).2.2

end UniversalCoverSplitting
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem picard_family_fderiv_preserves (V W : C(E,E))
    (D : C(E,E →L[ℂ] E)) (DW : E → E →L[ℂ] E)
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    (hW : ∀ x ∈ U, HasFDerivAt W (DW x) x)
    (hcomm : ∀ x ∈ U, DW x (V x) = D x (W x))
    {O : Set (E × ℂ)} (hO : IsOpen O) {φ : E × ℂ → FlowPath E}
    (hφ : ContDiffOn ℂ 1 φ O)
    (heq : ∀ q ∈ O, range (φ q) ⊆ U ∧
      φ q = ContinuousMap.const FlowTime q.1 + q.2 • picardIntegral V (φ q) ∧
      ‖q.2‖ * ‖D.comp (φ q)‖ < 1)
    {q : E × ℂ} (hq : q ∈ O) :
    fderiv ℂ (fun r ↦ φ r ⟨1,zero_le_one,le_rfl⟩) q (W q.1,0) =
      W (φ q ⟨1,zero_le_one,le_rfl⟩) := by
  let c : ℂ → E × ℂ := fun w ↦ (q.1 + w • W q.1,q.2)
  have hc : HasDerivAt c (W q.1,0) 0 := by
    convert! (((hasDerivAt_id (0 : ℂ)).smul_const (W q.1)).const_add q.1).prodMk
      (hasDerivAt_const (0 : ℂ) q.2) using 1; simp
  have hc0 : c 0 = q := by simp [c]
  have hφq := (hφ.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hφc : DifferentiableAt ℂ φ (c 0) := by simpa only [hc0] using hφq
  have hψ := hφc.hasFDerivAt.comp_hasDerivAt 0 hc
  have hr : range (φ (c 0)) ⊆ U := by simpa [hc0] using (heq q hq).1
  have hi : ∀ᶠ w in 𝓝 (0 : ℂ), φ (c w) =
      ContinuousMap.const FlowTime (q.1+w•W q.1) + q.2 • picardIntegral V (φ (c w)) := by
    have hnc : O ∈ 𝓝 (c 0) := by simpa only [hc0] using hO.mem_nhds hq
    have hn := hc.continuousAt.tendsto.eventually hnc
    filter_upwards [hn] with w hw
    exact (heq _ hw).2.1
  have hz : ‖q.2‖ * ‖D.comp (φ (c 0))‖ < 1 := by
    simpa [hc0] using (heq q hq).2.2
  have hP := picard_endpoint_preserves_commuting_field V W D DW hU hV hW hcomm hψ hr hi hz
  let F : E × ℂ → E := fun r ↦ φ r ⟨1,zero_le_one,le_rfl⟩
  have hF : DifferentiableAt ℂ F q :=
    (ContinuousMap.evalCLM (R := ℂ) (M := E) (⟨1,zero_le_one,le_rfl⟩ : FlowTime)).differentiableAt.comp q hφq
  have hFc : DifferentiableAt ℂ F (c 0) := by simpa only [hc0] using hF
  have hF' := hFc.hasFDerivAt.comp_hasDerivAt 0 hc
  simpa [hc0,F] using hF'.unique hP

theorem exists_holomorphic_flow_preserving_representatives (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ W : Set (E × ℂ), IsOpen W ∧ (p,0) ∈ W ∧
      ∃ F : E × ℂ → E,
        ContDiffOn ℂ 1 F W ∧ MapsTo F W U ∧
        (∀ x, (x,0) ∈ W → F (x,0) = x) ∧
        (∀ q ∈ W, HasDerivAt (fun z ↦ F (q.1,z)) (V (F q)) q.2) ∧
        (∀ (A : C(E,E)) (DA : E → E →L[ℂ] E),
          (∀ x ∈ U, HasFDerivAt A (DA x) x) →
          (∀ x ∈ U, DA x (V x) = D x (A x)) →
          ∀ q ∈ W, fderiv ℂ F q (A q.1,0) = A (F q)) := by
  obtain ⟨W,hWo,hWp,φ,hφ,hφbase,heq⟩ :=
    exists_small_holomorphic_picard_family V D hU hder hp
  let e₁ : FlowTime := ⟨1,zero_le_one,le_rfl⟩
  let F : E × ℂ → E := fun q ↦ φ q e₁
  refine ⟨W,hWo,hWp,F,?_,?_,?_,?_,?_⟩
  · exact (ContinuousMap.evalCLM (R := ℂ) (M := E) e₁).contDiff.comp_contDiffOn
      hφ
  · intro q hq
    exact (heq q hq).1 (mem_range_self e₁)
  · intro x hx
    have h := congrArg (fun γ : FlowPath E ↦ γ e₁) (heq (x,0) hx).2.1
    simpa [F] using h
  · intro q hq
    have hφq : DifferentiableAt ℂ φ q :=
      (hφ.contDiffAt (hWo.mem_nhds hq)).differentiableAt (by norm_num)
    have hem : DifferentiableAt ℂ (fun z : ℂ ↦ (q.1,z)) q.2 :=
      (differentiableAt_const q.1).prodMk differentiableAt_id
    have hψ := (hφq.comp q.2 hem).hasDerivAt
    have heq' : ∀ᶠ z in 𝓝 q.2,
        φ (q.1,z) = ContinuousMap.const FlowTime q.1 + z • picardIntegral V (φ (q.1,z)) := by
      have hn := hem.continuousAt.tendsto.eventually (hWo.mem_nhds hq)
      filter_upwards [hn] with z hz
      exact (heq _ hz).2.1
    exact picard_endpoint_hasDerivAt V D hU hder hψ (heq q hq).1 heq' (heq q hq).2.2

  · intro A DA hA hcomm q hq
    exact picard_family_fderiv_preserves V A D DA hU hder hA hcomm hWo hφ heq hq

end UniversalCoverSplitting
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

structure HolomorphicFlowData (V : C(E,E)) (D : C(E,E →L[ℂ] E)) (U : Set E) (p : E) where
  domain : Set (E × ℂ)
  isOpen_domain : IsOpen domain
  base_mem : (p,0) ∈ domain
  map : E × ℂ → E
  contDiff : ContDiffOn ℂ 1 map domain
  mapsTo : MapsTo map domain U
  zero : ∀ x, (x,0) ∈ domain → map (x,0) = x
  time : ∀ q ∈ domain, fderiv ℂ map q (0,1) = V (map q)
  preserves : ∀ (A : C(E,E)) (DA : E → E →L[ℂ] E),
    (∀ x ∈ U, HasFDerivAt A (DA x) x) →
    (∀ x ∈ U, DA x (V x) = D x (A x)) →
    ∀ q ∈ domain, fderiv ℂ map q (A q.1,0) = A (map q)

theorem exists_holomorphicFlowData (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) : Nonempty (HolomorphicFlowData V D U p) := by
  obtain ⟨O,hO,hpO,F,hF,hFU,hF0,hFt,hFA⟩ :=
    exists_holomorphic_flow_preserving_representatives V D hU hV hp
  refine ⟨⟨O,hO,hpO,F,hF,hFU,hF0,?_,hFA⟩⟩
  intro q hq
  have hFq := (hF.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)
  have hc : HasDerivAt (fun z : ℂ ↦ (q.1,z)) (0,1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  exact (hFq.hasFDerivAt.comp_hasDerivAt q.2 hc).unique (hFt q hq)

end UniversalCoverSplitting

end

end OAI
