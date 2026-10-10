import OAI.Geometry.KahlerSplitting.PathDerivatives

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
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set Metric Filter Topology
open Set MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
abbrev FlowTime := Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathExtend (γ : C(FlowTime,E)) : C(ℝ,E) :=
  γ.comp ⟨projIcc 0 1 zero_le_one, continuous_projIcc⟩

omit [NormedSpace ℝ E] in
@[simp] theorem pathExtend_apply (γ : C(FlowTime,E)) (t : FlowTime) :
    pathExtend γ t = γ t := by simp [pathExtend,projIcc_of_mem _ t.property]

def pathPrimitive (γ : C(FlowTime,E)) : C(FlowTime,E) :=
  ⟨fun t ↦ ∫ u in (0 : ℝ)..t.val, pathExtend γ u,
    (intervalIntegral.continuous_primitive
      (fun a b ↦ (pathExtend γ).continuous.intervalIntegrable a b) 0).comp continuous_subtype_val⟩

@[simp] theorem pathPrimitive_apply (γ : C(FlowTime,E)) (t : FlowTime) :
    pathPrimitive γ t = ∫ u in (0 : ℝ)..t.val, pathExtend γ u := rfl

 theorem pathPrimitive_norm_le (γ : C(FlowTime,E)) : ‖pathPrimitive γ‖ ≤ ‖γ‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg γ)).mpr
  intro t
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t.val) (C := ‖γ‖) (f := pathExtend γ)
    (fun u _ ↦ γ.norm_coe_le_norm (projIcc 0 1 zero_le_one u))
  calc
    ‖pathPrimitive γ t‖ ≤ ‖γ‖ * |t.val - 0| := hb
    _ ≤ ‖γ‖ := by rw [sub_zero,abs_of_nonneg t.property.1]; nlinarith [t.property.2,norm_nonneg γ]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def pathPrimitiveL : C(FlowTime,E) →L[ℂ] C(FlowTime,E) :=
  LinearMap.mkContinuous
    { toFun := fun γ : C(FlowTime,E) ↦ pathPrimitive γ
      map_add' := by
        intro γ η; ext t
        exact intervalIntegral.integral_add
          ((pathExtend γ).continuous.intervalIntegrable _ _)
          ((pathExtend η).continuous.intervalIntegrable _ _)
      map_smul' := by
        intro z γ; ext t
        exact intervalIntegral.integral_smul z (pathExtend γ) }
    1 (fun γ ↦ by simpa using pathPrimitive_norm_le γ)

@[simp] theorem pathPrimitiveL_apply (γ : C(FlowTime,E)) :
    pathPrimitiveL γ = pathPrimitive γ := rfl

 theorem pathPrimitiveL_norm_le : ‖(pathPrimitiveL : C(FlowTime,E) →L[ℂ] C(FlowTime,E))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro γ
  simpa using pathPrimitive_norm_le γ

end UniversalCoverSplitting
open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

abbrev FlowPath (E : Type*) [TopologicalSpace E] := C(FlowTime,E)
abbrev FlowParameter (E : Type*) := E × ℂ

def picardIntegral (V : C(E,E)) (γ : FlowPath E) : FlowPath E :=
  pathPrimitiveL (V.comp γ)

def picardEquation (V : C(E,E)) (q : FlowParameter E × FlowPath E) :
    FlowParameter E × FlowPath E :=
  (q.1,q.2 - (ContinuousMap.const FlowTime q.1.1) - q.1.2 • picardIntegral V q.2)

def picardBase (p : E) : FlowParameter E × FlowPath E :=
  ((p,0),ContinuousMap.const FlowTime p)

@[simp] theorem picardEquation_base (V : C(E,E)) (p : E) :
    picardEquation V (picardBase p) = ((p,0),0) := by simp [picardEquation,picardBase]

def pathShear (L : FlowParameter E →L[ℂ] FlowPath E) :
    (FlowParameter E × FlowPath E) ≃L[ℂ] (FlowParameter E × FlowPath E) where
  toFun q := (q.1,q.2-L q.1)
  invFun q := (q.1,q.2+L q.1)
  left_inv := by intro q; ext <;> simp
  right_inv := by intro q; ext <;> simp
  map_add' := by intro q r; ext <;> simp; abel
  map_smul' := by intro z q; ext <;> simp [smul_sub]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def picardLinearTerm (V : C(E,E)) (p : E) : FlowParameter E →L[ℂ] FlowPath E :=
  (ContinuousLinearMap.const ℂ FlowTime).comp (ContinuousLinearMap.fst ℂ E ℂ) +
    (ContinuousLinearMap.snd ℂ E ℂ).smulRight
      (picardIntegral V (ContinuousMap.const FlowTime p))

 theorem contDiffAt_picardEquation_one (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ContDiffAt ℂ 1 (picardEquation V) (picardBase p) := by
  have hpath : range (ContinuousMap.const FlowTime p) ⊆ U := by
    rintro _ ⟨t,rfl⟩; exact hp
  have hs := contDiffAt_pathCompose_one V D hU hder (ContinuousMap.const FlowTime p) hpath
  have hi : ContDiffAt ℂ 1 (picardIntegral V) (ContinuousMap.const FlowTime p) :=
    (pathPrimitiveL : FlowPath E →L[ℂ] FlowPath E).contDiff.contDiffAt.comp _ hs
  have hiq : ContDiffAt ℂ 1 (fun q : FlowParameter E × FlowPath E ↦ picardIntegral V q.2)
      (picardBase p) := hi.comp (f := fun q : FlowParameter E × FlowPath E ↦ q.2) (picardBase p) contDiffAt_id.snd
  have hc : ContDiffAt ℂ 1 (fun q : FlowParameter E × FlowPath E ↦
      ContinuousMap.const FlowTime q.1.1) (picardBase p) :=
    (ContinuousLinearMap.const ℂ FlowTime : E →L[ℂ] FlowPath E).contDiff.contDiffAt.comp _
      contDiffAt_id.fst.fst
  exact contDiffAt_id.fst.prodMk
    ((contDiffAt_id.snd.sub hc).sub (contDiffAt_id.fst.snd.smul hiq))

 theorem hasFDerivAt_picardEquation_base (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    HasFDerivAt (picardEquation V) (pathShear (picardLinearTerm V p)).toContinuousLinearMap
      (picardBase p) := by
  have hpath : range (ContinuousMap.const FlowTime p) ⊆ U := by
    rintro _ ⟨t,rfl⟩; exact hp
  have hs := contDiffAt_pathCompose_one V D hU hder (ContinuousMap.const FlowTime p) hpath
  have hi : DifferentiableAt ℂ (picardIntegral V) (ContinuousMap.const FlowTime p) :=
    (pathPrimitiveL : FlowPath E →L[ℂ] FlowPath E).differentiableAt.comp _
      (hs.differentiableAt (by norm_num))
  let q₀ := picardBase p
  have hid : HasFDerivAt (fun q : FlowParameter E × FlowPath E ↦ q)
      (ContinuousLinearMap.id ℂ _) q₀ := hasFDerivAt_id q₀
  have hiq := hi.hasFDerivAt.comp q₀ hid.snd
  have hc := (ContinuousLinearMap.const ℂ FlowTime : E →L[ℂ] FlowPath E).hasFDerivAt.comp q₀
    hid.fst.fst
  have he := hid.fst.prodMk ((hid.snd.sub hc).sub (hid.fst.snd.smul hiq))
  convert! he using 1
  ext q t <;> simp [pathShear,picardLinearTerm,picardBase,q₀]

end UniversalCoverSplitting
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem exists_holomorphic_picard_family (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ W : Set (FlowParameter E), IsOpen W ∧ (p,0) ∈ W ∧
      ∃ φ : FlowParameter E → FlowPath E,
        ContDiffOn ℂ 1 φ W ∧ φ (p,0) = ContinuousMap.const FlowTime p ∧
        ∀ q ∈ W, range (φ q) ⊆ U ∧
          φ q = ContinuousMap.const FlowTime q.1 + q.2 • picardIntegral V (φ q) := by
  let q₀ := picardBase p
  have hc := contDiffAt_picardEquation_one V D hU hder hp
  have hd := hasFDerivAt_picardEquation_base V D hU hder hp
  have hn : (1 : ℕ∞ω) ≠ 0 := by norm_num
  let H := hc.localInverse hd hn
  have hHbase : H ((p,0),0) = q₀ := by
    simpa only [picardEquation_base] using hc.localInverse_apply_image hd hn
  have hH : ContDiffAt ℂ 1 H ((p,0),0) := by
    simpa only [picardEquation_base] using hc.to_localInverse hd hn
  let φ : FlowParameter E → FlowPath E := fun q ↦ (H (q,0)).2
  have hφbase : φ (p,0) = ContinuousMap.const FlowTime p := by
    change (H ((p,0),0)).2 = _
    rw [hHbase]; rfl
  have hφ : ContDiffAt ℂ 1 φ (p,0) :=
    hH.snd.comp (f := fun q : FlowParameter E ↦ (q,(0 : FlowPath E))) (p,0)
      (contDiffAt_id.prodMk contDiffAt_const)
  have hemb : ContinuousAt (fun q : FlowParameter E ↦ (q,(0 : FlowPath E))) (p,0) := by
    fun_prop
  have hi : ∀ᶠ q : FlowParameter E × FlowPath E in 𝓝 ((p,0),0),
      picardEquation V (H q) = q := by
    convert! (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse using 1
    simp only [picardEquation_base]
  have hir := hemb.tendsto.eventually hi
  have hprange : range (ContinuousMap.const FlowTime p) ⊆ U := by
    rintro _ ⟨t,rfl⟩; exact hp
  have hr : ∀ᶠ q in 𝓝 (p,0), range (φ q) ⊆ U := by
    have hh : ∀ᶠ γ : FlowPath E in 𝓝 (φ (p,0)), range γ ⊆ U := by
      rw [hφbase]
      convert! ContinuousMap.eventually_range_subset hU hprange
    exact hφ.continuousAt.tendsto.eventually hh
  obtain ⟨S,hS,hCS⟩ := hφ.contDiffOn le_rfl (by norm_num)
  have hall : {q | q ∈ S ∧ picardEquation V (H (q,0)) = (q,0) ∧ range (φ q) ⊆ U}
      ∈ 𝓝 (p,0) := by
    filter_upwards [hS,hir,hr] with q hq hiq hrq
    exact ⟨hq,hiq,hrq⟩
  obtain ⟨W,hW,hWo,hWp⟩ := _root_.mem_nhds_iff.mp hall
  refine ⟨W,hWo,hWp,φ,hCS.mono (fun q hq ↦ (hW hq).1),hφbase,?_⟩
  intro q hq
  obtain ⟨_,heq,hrange⟩ := hW hq
  refine ⟨hrange,?_⟩
  have hparam := congrArg Prod.fst heq
  have hres := congrArg Prod.snd heq
  change (H (q,0)).1 = q at hparam
  change (H (q,0)).2 - ContinuousMap.const FlowTime (H (q,0)).1.1 -
    (H (q,0)).1.2 • picardIntegral V (H (q,0)).2 = 0 at hres
  rw [hparam] at hres
  apply sub_eq_zero.mp
  simpa only [sub_add_eq_sub_sub,φ] using hres

end UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem hasFDerivAt_picardIntegral (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {γ : FlowPath E} (hγ : range γ ⊆ U) :
    HasFDerivAt (picardIntegral V)
      (pathPrimitiveL.comp (pathLinearApply (D.comp γ))) γ := by
  have hs (t : FlowTime) : HasStrictFDerivAt V (D (γ t)) (γ t) := by
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · filter_upwards [hU.mem_nhds (hγ (mem_range_self t))] with x hx
      exact hder x hx
    · exact D.continuous.continuousAt
  have hD (t : FlowTime) : ContinuousAt D (γ t) := D.continuous.continuousAt
  have hsc : HasFDerivAt (fun η : FlowPath E ↦ V.comp η)
      (pathLinearApply (D.comp γ)) γ := by
    convert! (hasStrictFDerivAt_pathCompose V D γ hs hD).hasFDerivAt using 1
  exact pathPrimitiveL.hasFDerivAt.comp γ hsc

omit [CompleteSpace E] in

theorem picard_variation_equation (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} {z : ℂ} {ψ : ℂ → FlowPath E} {Z : FlowPath E}
    (hψ : HasDerivAt ψ Z z) (hr : range (ψ z) ⊆ U)
    (heq : ∀ᶠ w in 𝓝 z, ψ w = ContinuousMap.const FlowTime p + w • picardIntegral V (ψ w)) :
    Z = picardIntegral V (ψ z) + z • pathPrimitiveL (pathLinearApply (D.comp (ψ z)) Z) := by
  have hi := (hasFDerivAt_picardIntegral V D hU hder hr).comp_hasDerivAt z hψ
  have hh := ((hasDerivAt_id z).smul hi).const_add (ContinuousMap.const FlowTime p)
  have he : HasDerivAt ψ
      (picardIntegral V (ψ z) + z • pathPrimitiveL (pathLinearApply (D.comp (ψ z)) Z)) z := by
    convert! hh.congr_of_eventuallyEq heq using 1
    simp [add_comm]
  exact hψ.unique he

omit [CompleteSpace E] in

theorem picard_linear_unique (A : C(FlowTime,E →L[ℂ] E)) {z : ℂ}
    (hz : ‖z‖ * ‖A‖ < 1) {B Z Y : FlowPath E}
    (hZ : Z = B + z • pathPrimitiveL (pathLinearApply A Z))
    (hY : Y = B + z • pathPrimitiveL (pathLinearApply A Y)) : Z = Y := by
  have he : Z-Y = z • pathPrimitiveL (pathLinearApply A (Z-Y)) := by
    calc
      Z-Y = (B + z • pathPrimitiveL (pathLinearApply A Z)) -
          (B + z • pathPrimitiveL (pathLinearApply A Y)) := congrArg₂ (· - ·) hZ hY
      _ = z • pathPrimitiveL (pathLinearApply A (Z-Y)) := by
        rw [map_sub,map_sub,smul_sub]; abel
  have hn : ‖Z-Y‖ ≤ (‖z‖ * ‖A‖) * ‖Z-Y‖ := by
    calc
      ‖Z-Y‖ = ‖z‖ * ‖pathPrimitiveL (pathLinearApply A (Z-Y))‖ := (congrArg norm he).trans (norm_smul _ _)
      _ ≤ ‖z‖ * ‖pathLinearApply A (Z-Y)‖ :=
        mul_le_mul_of_nonneg_left (pathPrimitive_norm_le _) (norm_nonneg z)
      _ ≤ ‖z‖ * (‖A‖ * ‖Z-Y‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
        exact ((pathLinearApply A).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (pathLinearApply_norm_le A) (norm_nonneg _))
      _ = (‖z‖ * ‖A‖) * ‖Z-Y‖ := by ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (Z-Y)]))

def picardRealExtension (V : C(E,E)) (p : E) (z : ℂ) (γ : FlowPath E) : ℝ → E :=
  fun t ↦ p + z • ∫ u in (0 : ℝ)..t, V (pathExtend γ u)

theorem picardRealExtension_hasDerivAt (V : C(E,E)) (p : E) (z : ℂ)
    (γ : FlowPath E) (t : ℝ) :
    HasDerivAt (picardRealExtension V p z γ) (z • V (pathExtend γ t)) t := by
  have hc : Continuous (fun u ↦ V (pathExtend γ u)) := V.continuous.comp (pathExtend γ).continuous
  exact ((intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt).const_smul z).const_add p

omit [CompleteSpace E] in
theorem picardRealExtension_eq (V : C(E,E)) {p : E} {z : ℂ} {γ : FlowPath E}
    (heq : γ = ContinuousMap.const FlowTime p + z • picardIntegral V γ)
    (t : FlowTime) : picardRealExtension V p z γ t = γ t := by
  exact (congrArg (fun η : FlowPath E ↦ η t) heq).symm

def picardTimeVariation (V : C(E,E)) (γ : FlowPath E) : FlowPath E :=
  ⟨fun t ↦ t.val • V (γ t), by fun_prop⟩

end UniversalCoverSplitting
open Set Metric Filter Topology MeasureTheory
open scoped Interval

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem picardTimeVariation_equation (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hder : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} {z : ℂ} {γ : FlowPath E} (hr : range γ ⊆ U)
    (heq : γ = ContinuousMap.const FlowTime p + z • picardIntegral V γ) :
    picardTimeVariation V γ = picardIntegral V γ +
      z • pathPrimitiveL (pathLinearApply (D.comp γ) (picardTimeVariation V γ)) := by
  let η := picardRealExtension V p z γ
  let β := V.comp γ
  let A := D.comp γ
  let Y := picardTimeVariation V γ
  let g : ℝ → E := fun u ↦ pathExtend β u + z • pathExtend (pathLinearApply A Y) u
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hη (u : FlowTime) : η u = γ u := picardRealExtension_eq V heq u
  have hd (u : FlowTime) : HasDerivAt (fun v : ℝ ↦ v • V (η v)) (g u) u := by
    have ht := picardRealExtension_hasDerivAt V p z γ u.val
    have hv := ((hder (γ u) (hr (mem_range_self u))).restrictScalars ℝ)
    rw [← hη u] at hv
    have hc := hv.comp_hasDerivAt u.val ht
    have hh := (hasDerivAt_id u.val).smul hc
    convert! hh using 1
    dsimp [g,β,A,Y,picardTimeVariation]
    rw [pathExtend_apply,pathExtend_apply,pathLinearApply_apply,hη u,pathExtend_apply]
    simp only [one_smul,ContinuousMap.comp_apply]
    change V (γ u) + z • (D (γ u)) (u.val • V (γ u)) =
      u.val • (D (γ u)) (z • V (γ u)) + V (γ u)
    simp only [ContinuousLinearMap.map_smul_of_tower]
    rw [smul_comm,add_comm]
  ext t
  have hderiv (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) t.val) :
      HasDerivAt (fun v : ℝ ↦ v • V (η v)) (g u) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hu
      exact ⟨hu.1,hu.2.trans t.property.2⟩
    exact hd ⟨u,hu'⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hg.intervalIntegrable 0 t.val)
  have heval : (∫ u in (0 : ℝ)..t.val, g u) =
      picardIntegral V γ t + z • pathPrimitiveL (pathLinearApply A Y) t := by
    dsimp [g,picardIntegral]
    rw [intervalIntegral.integral_add,intervalIntegral.integral_smul]
    · exact (pathExtend β).continuous.intervalIntegrable _ _
    · exact ((pathExtend (pathLinearApply A Y)).continuous.const_smul z).intervalIntegrable _ _
  rw [heval] at hi
  simp only [zero_smul,sub_zero] at hi
  change t.val • V (γ t) = _
  rw [← hη t]
  exact hi.symm

end UniversalCoverSplitting

end

end OAI
