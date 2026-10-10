import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.LabelWeight

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.initial_label_lintegral {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase)
    {g : Phase→ENNReal} (hg : Measurable g) :
    (∫⁻ z in initialConeLabels T (F.flow zX T).1, g z) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ n : Sphere,∫⁻ v : Vec,
        ENNReal.ofReal (t^2*(1-dot n.1 (velocity (F.flow zX t).2))) *
          g ((F.flow zX t).1-t • n.1,v) ∂volume ∂sphereMeasure := by
  classical
  let A := initialConeLabels T (F.flow zX T).1
  have hA : MeasurableSet A :=
    (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).measurableSet
  have hX : Continuous (prefixFlow F.flow T zX) := by
    exact (F.continuousOn_time zX).comp_continuous
      (continuous_const.max (continuous_const.min continuous_id)) (prefixClamp_mem hT)
  let k : Sphere→ℝ→ENNReal := fun n t=>
    ENNReal.ofReal (t^2*(1-dot n.1 (velocity (prefixFlow F.flow T zX t).2))) *
      ∫⁻ v : Vec,g ((prefixFlow F.flow T zX t).1-t • n.1,v)
  have hk : Measurable (Function.uncurry k) := by
    have hn : Measurable (fun p : Sphere×ℝ => (p.1:Vec)) :=
      measurable_subtype_coe.comp measurable_fst
    have hx := hX.measurable.comp (measurable_snd : Measurable (Prod.snd : Sphere×ℝ→ℝ))
    have hv := (contDiff_velocity (k:=1)).continuous.measurable.comp hx.snd
    have hr : Measurable (fun p : Sphere×ℝ =>
        p.2^2*(1-dot (p.1:Vec) (velocity (prefixFlow F.flow T zX p.2).2))) := by
      simp only [dot_eq_inner]
      exact (measurable_snd.pow_const 2).mul
        ((measurable_const (a:=(1:ℝ))).sub (hn.inner hv))
    have hg' : Measurable (fun p : (Sphere×ℝ)×Vec =>
        g ((prefixFlow F.flow T zX p.1.2).1-p.1.2 • (p.1.1:Vec),p.2)) := by
      exact hg.comp (((hx.fst.sub (measurable_snd.smul hn)).comp measurable_fst).prodMk measurable_snd)
    exact hr.ennreal_ofReal.mul hg'.lintegral_prod_right'
  calc
    _ = ∫⁻ y : Vec, ∫⁻ v : Vec, A.indicator g (y,v) := by
      rw [← lintegral_indicator hA]
      exact lintegral_prod _ (hg.indicator hA).aemeasurable
    _ = ∫⁻ y in ball (F.flow zX T).1 T, ∫⁻ v : Vec,g (y,v) := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y∈ball (F.flow zX T).1 T
      · rw [indicator_of_mem hy]
        apply lintegral_congr
        intro v
        apply indicator_of_mem
        simpa only [A,initialConeLabels,mem_ofPred_eq,mem_ball,dist_eq_norm,norm_sub_rev] using hy
      · rw [indicator_of_notMem hy]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro v
        apply indicator_of_notMem
        intro hz
        apply hy
        simpa only [A,initialConeLabels,mem_ofPred_eq,mem_ball,dist_eq_norm,norm_sub_rev] using hz
    _ = ∫⁻ n : Sphere,∫⁻ t in Ioo (0:ℝ) T,k n t ∂volume ∂sphereMeasure := by
      have hh := F.receiver_polar_lintegral (s:=0) ⟨le_rfl,hT⟩ zX (hg.lintegral_prod_right' (ν:=volume))
      simp only [sub_zero,zero_add] at hh
      rw [hh]
      apply lintegral_congr
      intro n
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp only [k,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht)]
    _ = ∫⁻ t in Ioo (0:ℝ) T,∫⁻ n : Sphere,k n t ∂sphereMeasure :=
      lintegral_lintegral_swap hk.aemeasurable
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply lintegral_congr
      intro n
      simp only [k,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht)]
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

def initialPuncturedCone (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : Set Phase :=
  initialConeLabels T (α zX T).1 ∩ {z : Phase | z.1≠zX.1}

lemma isOpen_initialPuncturedCone (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) :
    IsOpen (initialPuncturedCone α zX T) :=
  (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).inter
    (isClosed_eq continuous_fst continuous_const).isOpen_compl

lemma initialPuncturedCone_sub (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) :
    initialPuncturedCone α zX T ⊆ initialClosedCone α zX T ∩ {z : Phase | z.1≠zX.1} :=
  by
    intro z hz
    refine ⟨?_,hz.2⟩
    change ‖(α zX T).1-z.1‖≤T
    exact le_of_lt hz.1

lemma PhaseFlowOn.initial_spherical_label_mem {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (ht : t∈Ioo 0 T) (n : Sphere) (v : Vec) :
    ((F.flow zX t).1-t • n.1,v)∈initialPuncturedCone F.flow zX T := by
  have hT : 0≤T := ht.1.le.trans ht.2.le
  have hn : ‖t • n.1‖=t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1,sphere_norm n,mul_one]
  have hm : t • n.1 ∈ receiverRadialDomain 0 T := by
    change 0<‖t • n.1‖ ∧ 0+‖t • n.1‖<T
    simpa only [hn,zero_add,mem_Ioo] using ht
  have hi := mem_image_of_mem (receiverRadial F.flow zX 0) hm
  rw [F.receiver_image ⟨le_rfl,hT⟩ zX] at hi
  simp only [receiverRadial,hn,zero_add,sub_zero,F.initial,Set.mem_sdiff,mem_singleton_iff] at hi
  refine ⟨?_,hi.2⟩
  simpa only [initialConeLabels,mem_ofPred_eq,mem_ball,dist_eq_norm,norm_sub_rev] using hi.1

def initialConeState (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (z : Phase) : CutoffState :=
  let t := branchTime α zX z T 0
  (t,branchDirection α zX z T 0,z.2,(α zX t).2)

lemma PhaseFlowOn.initial_state_regular {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    ContinuousOn (initialConeState F.flow zX T) (initialPuncturedCone F.flow zX T) ∧
    ∀ z∈initialPuncturedCone F.flow zX T,
      0<(initialConeState F.flow zX T z).1 ∧
      (initialConeState F.flow zX T z).1≤T ∧
      ‖(initialConeState F.flow zX T z).2.1‖=1 := by
  let A := initialPuncturedCone F.flow zX T
  let τ := fun z=>branchTime F.flow zX z T 0
  have hm : ∀ z∈A,0∈closedBranchDomain F.flow zX z T := fun z hz=>
    F.initial_closed_branch_mem hT zX z ((initialPuncturedCone_sub F.flow zX T hz).1)
  have htm : MapsTo τ A (Icc 0 T) := fun z hz=>(F.branch_spec_closed zX z (hm z hz)).1
  have hne : ∀ z∈A,(F.flow zX 0).1≠(F.flow z 0).1 := by
    intro z hz
    simpa only [F.initial] using Ne.symm hz.2
  have hpos : ∀ z∈A,0<τ z := by
    intro z hz
    simpa only [sub_zero] using F.branch_radius_pos_closed zX z (hm z hz) (hne z hz)
  have ht : ContinuousOn τ A := by
    obtain ⟨C,hC⟩ := F.initial_branch_lipschitz hT zX
    exact hC.continuousOn.mono (fun z hz=>(initialPuncturedCone_sub F.flow zX T hz).1)
  have hX := (F.continuousOn_time zX).comp ht htm
  have hn : ContinuousOn (fun z=>branchDirection F.flow zX z T 0) A := by
    convert (ht.inv₀ (fun z hz=>(hpos z hz).ne')).smul
      (hX.fst.sub continuous_fst.continuousOn) using 1
    funext z
    simp only [branchDirection,sub_zero,F.initial,τ,Function.comp_apply]
    rfl
  refine ⟨ht.prodMk (hn.prodMk (continuous_snd.continuousOn.prodMk hX.snd)),?_⟩
  intro z hz
  exact ⟨hpos z hz,(htm hz).2,F.branchDirection_norm_closed zX z (hm z hz) (hne z hz)⟩

lemma PhaseFlowOn.initial_selected_cutoff {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    ContinuousOn (fun z=>stateCutoff T Q (initialConeState F.flow zX T z))
      (initialPuncturedCone F.flow zX T) ∧
    ∀ z∈initialPuncturedCone F.flow zX T,
      stateCutoff T Q (initialConeState F.flow zX T z)∈Icc (0:ℝ) 1 := by
  obtain ⟨hc,hb⟩ := F.initial_state_regular hT zX
  constructor
  · intro z hz
    exact ((contDiffAt_stateCutoff T Q (hb z hz).1 (hb z hz).2.2).continuousAt).comp_continuousWithinAt (hc z hz)
  · intro z hz
    apply selectedDyadicCutoff_mem_unit
    · exact physicalCutoffCoordinates_pos (hb z hz).2.2 (hb z hz).1
    · exact physicalCutoffCoordinates_le_one (hb z hz).2.2 ((hb z hz).2.1.trans (le_max_right _ _))

def selectedInitialKernel (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (f : Phase→ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W : ℝ→Vec→L[ℝ]Vec) : Phase→Vec :=
  (initialPuncturedCone α zX T).indicator (fun z=>
    let t := branchTime α zX z T 0
    (f z*ψ t*stateCutoff T Q (initialConeState α zX T z)) •
      W t (retardedPrimitive t (velocity (α zX t).2) (velocity z.2)
        (branchDirection α zX z T 0)))

lemma PhaseFlowOn.selected_initial_kernel_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) {f : Phase→ℝ}
    (hf : Continuous f) (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ}
    (hψ : ContinuousOn ψ (Icc 0 T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : ContinuousOn W (Icc 0 T)) :
    Measurable (selectedInitialKernel F.flow zX T f Q ψ W) := by
  classical
  let A := initialPuncturedCone F.flow zX T
  let τ := fun z=>branchTime F.flow zX z T 0
  have htm : MapsTo τ A (Icc 0 T) := fun z hz=>
    (F.branch_spec_closed zX z (F.initial_closed_branch_mem hT zX z
      ((initialPuncturedCone_sub F.flow zX T hz).1))).1
  have ht : ContinuousOn τ A := (F.initial_state_regular hT zX).1.fst
  have hχ := (F.initial_selected_cutoff hT zX Q).1
  have hp := (F.initial_primitive_continuousOn hT zX).mono (initialPuncturedCone_sub F.flow zX T)
  have hc := ((hf.continuousOn.mul (hψ.comp ht htm)).mul hχ).smul
    ((hW.comp ht htm).clm_apply hp)
  have h := hc.measurable_piecewise (continuousOn_const (c:=(0:Vec)))
    (isOpen_initialPuncturedCone F.flow zX T).measurableSet
  convert h using 1
  funext z
  rfl

lemma PhaseFlowOn.selected_initial_kernel_pullback {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (ht : t∈Ioo 0 T)
    (f : Phase→ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W : ℝ→Vec→L[ℝ]Vec)
    (n : Sphere) (v : Vec) :
    (t^2*(1-dot n.1 (velocity (F.flow zX t).2))) •
      selectedInitialKernel F.flow zX T f Q ψ W ((F.flow zX t).1-t • n.1,v) =
    initialSignedBoundaryDensity f (F.flow zX t).1 (F.flow zX t).2 t (ψ t)
      (stateCutoff T Q (t,n.1,v,(F.flow zX t).2)) (W t) n.1 v := by
  rw [selectedInitialKernel,indicator_of_mem (F.initial_spherical_label_mem zX ht n v)]
  obtain ⟨hτ,hn⟩ := F.initial_branch_pullback zX ht n v
  simp only [initialConeState,hτ,hn]
  simp only [initialSignedBoundaryDensity,smul_smul]
  congr 1
  ring

lemma selectedInitialKernel_integrable_bound {f : Phase→ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (E B : Field) (T : ℝ) (F : PhaseFlowOn E B T)
      (zX : Phase) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
      (W : ℝ→Vec→L[ℝ]Vec) (M : ℝ),
      0≤T → 0≤M → ContinuousOn ψ (Icc 0 T) → ContinuousOn W (Icc 0 T) →
      (∀ t∈Icc 0 T,‖W t‖≤M) →
      Integrable (selectedInitialKernel F.flow zX T f Q ψ W) ∧
      ‖∫ z : Phase,selectedInitialKernel F.flow zX T f Q ψ W z‖ ≤
        C*T*M*(∫ t in Ioo (0:ℝ) T,|ψ t|) := by
  obtain ⟨C,hC,hb⟩ := initialSignedBoundary_lintegral_bound hf hc hpos
  refine ⟨C,hC,?_⟩
  intro E B T F zX Q ψ W M hT hM hψ hW hWM
  let G := selectedInitialKernel F.flow zX T f Q ψ W
  have hG : Measurable G := F.selected_initial_kernel_measurable hT zX hf Q hψ hW
  have hψi : IntegrableOn ψ (Ioo 0 T) :=
    (hψ.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  let χ := fun t (n : Sphere) v=>stateCutoff T Q (t,n.1,v,(F.flow zX t).2)
  have hχ : ∀ t∈Ioo (0:ℝ) T,∀ n v,χ t n v∈Icc (0:ℝ) 1 := by
    intro t ht n v
    apply selectedDyadicCutoff_mem_unit
    · exact physicalCutoffCoordinates_pos (sphere_norm n) ht.1
    · exact physicalCutoffCoordinates_le_one (sphere_norm n) (ht.2.le.trans (le_max_right _ _))
  have heq : (∫⁻ z : Phase,ENNReal.ofReal ‖G z‖) =
      ∫⁻ t in Ioo (0:ℝ) T,∫⁻ n : Sphere,∫⁻ v : Vec,
        ENNReal.ofReal ‖initialSignedBoundaryDensity f (F.flow zX t).1 (F.flow zX t).2 t
          (ψ t) (χ t n v) (W t) n.1 v‖ ∂volume ∂sphereMeasure := by
    calc
      _ = ∫⁻ z in initialConeLabels T (F.flow zX T).1,ENNReal.ofReal ‖G z‖ := by
        have hA : MeasurableSet (initialConeLabels T (F.flow zX T).1) :=
          (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).measurableSet
        rw [← lintegral_indicator hA]
        apply lintegral_congr
        intro z
        by_cases hz : z∈initialConeLabels T (F.flow zX T).1
        · rw [indicator_of_mem hz]
        · rw [indicator_of_notMem hz]
          have hz' : z∉initialPuncturedCone F.flow zX T := fun hh=>hz hh.1
          simp only [G,selectedInitialKernel,indicator_of_notMem hz',norm_zero,ENNReal.ofReal_zero]
      _ = _ := by
        rw [F.initial_label_lintegral hT zX hG.norm.ennreal_ofReal]
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        apply lintegral_congr
        intro n
        apply lintegral_congr
        intro v
        have hr : 0≤t^2*(1-dot n.1 (velocity (F.flow zX t).2)) :=
          mul_nonneg (sq_nonneg _) (cone_denom_pos _ _ (sphere_norm n)).le
        have hp := congrArg (fun x : Vec=>ENNReal.ofReal ‖x‖)
          (F.selected_initial_kernel_pullback zX ht f Q ψ W n v)
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,ENNReal.ofReal_mul hr] using hp
  have hbound : (∫⁻ z : Phase,ENNReal.ofReal ‖G z‖) ≤
      ENNReal.ofReal (C*T*M*(∫ t in Ioo (0:ℝ) T,|ψ t|)) := by
    rw [heq]
    exact hb T M (Ioo 0 T) (fun t=>(F.flow zX t).1) (fun t=>(F.flow zX t).2)
      ψ χ W hT hM measurableSet_Ioo Ioo_subset_Icc_self hψi hχ
      (fun t ht=>hWM t (Ioo_subset_Icc_self ht))
  have hfinite : (∫⁻ z : Phase,ENNReal.ofReal ‖G z‖)<⊤ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨hG.aestronglyMeasurable,(hasFiniteIntegral_iff_norm G).mpr hfinite⟩,?_⟩
  apply (norm_integral_le_lintegral_norm G).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans
    (le_of_eq (ENNReal.toReal_ofReal (by positivity)))

lemma PhaseFlowOn.selected_label_branch_formula {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX z : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow z b).1‖=T)
    (hne : ∀σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow z σ).1)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal}
    (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0) :
    (∫σ : ℝ,selectedLabelSignedForce s F.flow zX T Q ψ (σ,z)) =
      (s.f (0,z)*ψ (branchTime F.flow zX z T 0)*
        selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX z 0)) •
      retardedPrimitive (branchTime F.flow zX z T 0) (velocity (F.flow zX (branchTime F.flow zX z T 0)).2)
        (velocity z.2) (branchDirection F.flow zX z T 0)+
        ∫σ : ℝ,selectedLabelCosts s F.flow zX T Q ψ (σ,z) := by
  classical
  have hT : 0≤T := hb.1.trans hb.2
  let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX z σ)
  let τ := branchTime F.flow zX z T
  let P := fun σ=>retardedPrimitive (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
  let K := fun σ=>signedForceKernel (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
    (phaseAcceleration s.E s.B F.flow z σ)
  let R := fun σ=>signedRemainder (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
    (phaseAcceleration s.E s.B F.flow zX (τ σ))
  let G := fun σ=>(ψ (τ σ)*χ σ) • K σ
  let H := fun σ=>(deriv ψ (τ σ)*branchRate F.flow zX z T σ*χ σ+
      ψ (τ σ)*branchSelectedRate s.E s.B F.flow T zX z Q σ) • P σ +
      (ψ (τ σ)*χ σ) • R σ
  have hd : ∀σ,(σ,z)∈labelBranchDomain F.flow zX T ↔ σ∈Ioo 0 b := by
    intro σ
    change (σ∈branchDomain F.flow zX z T ∧ _) ↔ _
    rw [F.branchDomain_eq hT zX z hb he]
    constructor
    · exact And.left
    · intro hσ
      exact ⟨hσ,hne σ ⟨hσ.1.le,hσ.2.le.trans hb.2⟩⟩
  have hK : (fun σ=>selectedLabelSignedForce s F.flow zX T Q ψ (σ,z))=
      (Ioo (0:ℝ) b).indicator (fun σ=>s.f (0,z) • G σ) := by
    funext σ
    by_cases hσ : σ∈Ioo (0:ℝ) b
    · have hp := (hd σ).mpr hσ
      have hp' : (σ,z)∈jointBranchDomain F.flow zX T := hp
      simp only [selectedLabelSignedForce,labelWeight,labelReceiverTime,labelSelectedCutoff,
        actualLabelSignedForce,indicator_of_mem hp,indicator_of_mem hp',indicator_of_mem hσ,
        G,K,τ,χ,sourceAcceleration,phaseAcceleration,smul_smul]
      congr 1
      ring
    · have hp := mt (hd σ).mp hσ
      simp only [selectedLabelSignedForce,actualLabelSignedForce,indicator_of_notMem hp,
        indicator_of_notMem hσ,smul_zero]
  have hH : (fun σ=>selectedLabelCosts s F.flow zX T Q ψ (σ,z))=
      (Ioo (0:ℝ) b).indicator (fun σ=>s.f (0,z) • H σ) := by
    funext σ
    by_cases hσ : σ∈Ioo (0:ℝ) b
    · have hp := (hd σ).mpr hσ
      have hp' : (σ,z)∈jointBranchDomain F.flow zX T := hp
      simp only [selectedLabelCosts,labelWeight,labelReceiverTime,labelSelectedCutoff,
        actualLabelRatePrimitive,actualLabelCutoffCost,actualLabelPrimitive,actualLabelRemainder,
        indicator_of_mem hp,indicator_of_mem hp',indicator_of_mem hσ,H,P,R,τ,χ,
        smul_smul,smul_add,add_smul]
      module
    · have hp := mt (hd σ).mp hσ
      simp only [selectedLabelCosts,actualLabelRatePrimitive,actualLabelCutoffCost,
        actualLabelPrimitive,actualLabelRemainder,indicator_of_notMem hp,
        indicator_of_notMem hσ,smul_zero,add_zero]
  have hI : (∫σ in 0..b,G σ)=(ψ (τ 0)*χ 0) • P 0+∫σ in 0..b,H σ := by
    simpa only [G,H,K,P,R,τ,χ,ContinuousLinearMap.id_apply,zero_apply,zero_add]
      using F.actual_selected_temporal_signed_formula hs zX z hb he hne Q hψ hψT
        (W:=fun _=>ContinuousLinearMap.id ℝ Vec) (W':=fun _=>0) continuousOn_const continuousOn_const
        (fun σ _=>hasDerivAt_const σ (ContinuousLinearMap.id ℝ Vec))
  rw [hK,hH,integral_indicator measurableSet_Ioo,integral_indicator measurableSet_Ioo,
    integral_smul,integral_smul,restrict_Ioo_eq_restrict_Ioc,
    ←intervalIntegral.integral_of_le hb.1,←intervalIntegral.integral_of_le hb.1,hI,smul_add]
  congr 1
  simp only [P,τ,χ,sub_zero,F.initial,smul_smul]
  congr 1
  ring

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.branchDomain_empty_of_not_initial {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX z : Phase)
    (hz : z∉initialConeLabels T (F.flow zX T).1) :
    branchDomain F.flow zX z T=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro σ hσ
  have ht : T≤‖(F.flow zX T).1-z.1‖ := le_of_not_gt hz
  have hh := F.emission_strictMono hT z (F.flow zX T).1 ⟨le_rfl,hT⟩
    (Ioo_subset_Icc_self hσ.1) hσ.1.1
  simp only [F.initial,zero_add] at hh
  linarith [hσ.2]

lemma PhaseFlowOn.ae_selected_label_formula {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal}
    (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0) :
    ∀ᵐ z : Phase,(∫σ : ℝ,selectedLabelSignedForce s F.flow zX T Q ψ (σ,z)) =
      selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ (fun _=>ContinuousLinearMap.id ℝ Vec) z+
        ∫σ : ℝ,selectedLabelCosts s F.flow zX T Q ψ (σ,z) := by
  classical
  have hn : ∀ᵐ z ∂(volume : Measure Phase),
      z∉{y : Phase | ∃t∈Icc 0 T,(F.flow y t).1=(F.flow zX t).1} :=
    ae_iff.mpr (by simpa only [mem_ofPred_eq,not_not] using F.closed_collision_null hT zX)
  filter_upwards [hn] with z hz
  have hne : ∀t∈Icc 0 T,(F.flow zX t).1≠(F.flow z t).1 := fun t ht he=>hz ⟨t,ht,he.symm⟩
  by_cases hy : z∈initialConeLabels T (F.flow zX T).1
  · obtain ⟨b,⟨hb,he⟩,_⟩ := F.exists_emission ⟨hT,le_rfl⟩ (F.flow zX T).1 hy
    have hp : z∈initialPuncturedCone F.flow zX T := ⟨hy,by
      have hn0 := hne 0 ⟨le_rfl,hT⟩
      change (F.flow zX 0).1 ≠ (F.flow z 0).1 at hn0
      simpa only [F.initial,mem_ofPred_eq,ne_eq,eq_comm] using hn0⟩
    rw [F.selected_label_branch_formula hs zX z hb he hne Q hψ hψT]
    congr 1
    simp only [selectedInitialKernel,indicator_of_mem hp,ContinuousLinearMap.id_apply,
      actualCutoffCoordinates,sub_zero,F.initial,stateCutoff,initialConeState]
  · have hd := F.branchDomain_empty_of_not_initial hT zX z hy
    have hp : z∉initialPuncturedCone F.flow zX T := fun hz=>hy hz.1
    have he : ∀σ,(σ,z)∉labelBranchDomain F.flow zX T := fun σ hh=>by
      have hh' := hh.1
      rw [hd] at hh'
      exact hh'
    have hK : (fun σ=>selectedLabelSignedForce s F.flow zX T Q ψ (σ,z))=0 := by
      funext σ
      simp only [selectedLabelSignedForce,actualLabelSignedForce,indicator_of_notMem (he σ),
        smul_zero,Pi.zero_apply]
    have hC : (fun σ=>selectedLabelCosts s F.flow zX T Q ψ (σ,z))=0 := by
      funext σ
      simp only [selectedLabelCosts,actualLabelCutoffCost,actualLabelRatePrimitive,
        actualLabelPrimitive,actualLabelRemainder,indicator_of_notMem (he σ),
        smul_zero,add_zero,Pi.zero_apply]
    simp only [hK,hC,selectedInitialKernel,indicator_of_notMem hp]
    simp

lemma PhaseFlowOn.selected_signed_fubini {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0) :
    (∫σ : ℝ,∫z : Phase,selectedLabelSignedForce s F.flow zX T Q ψ (σ,z)) =
      (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ
        (fun _=>ContinuousLinearMap.id ℝ Vec) z)+
      ∫σ : ℝ,∫z : Phase,selectedLabelCosts s F.flow zX T Q ψ (σ,z) := by
  have hiK := F.selectedLabelSignedForce_integrable hs hT zX Q hψ.continuous.measurable hψb
  have hiC := F.selectedLabelCosts_integrable hs hT zX Q hψ hψb
  have hfc : Continuous (fun z=>s.f (0,z)) := hs.f_smooth.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _=>⟨⟨le_rfl,hT⟩,mem_univ _⟩)
  obtain ⟨K,hK,hcompact⟩ := hs.compact
  have hfs : HasCompactSupport (fun z=>s.f (0,z)) := hK.of_isClosed_subset (isClosed_tsupport _)
    (hcompact 0 ⟨le_rfl,hT⟩)
  obtain ⟨C,_,hb⟩ := selectedInitialKernel_integrable_bound hfc hfs (hs.nonnegative 0 ⟨le_rfl,hT⟩)
  have hiB := (hb s.E s.B T F zX Q ψ (fun _=>ContinuousLinearMap.id ℝ Vec) 1 hT zero_le_one
    hψ.continuous.continuousOn continuousOn_const (fun _ _=>by simp)).1
  have hKi : Integrable (Function.uncurry (fun σ z=>selectedLabelSignedForce s F.flow zX T Q ψ (σ,z)))
      (volume.prod volume) := hiK
  have hCi : Integrable (Function.uncurry (fun σ z=>selectedLabelCosts s F.flow zX T Q ψ (σ,z)))
      (volume.prod volume) := hiC
  rw [integral_integral_swap hKi]
  rw [integral_congr_ae (F.ae_selected_label_formula hs hT zX Q hψ.lipschitzOnWith hψT),
    integral_add hiB hiC.integral_prod_right,←integral_integral_swap hCi]

lemma integrable_bounded_clm_apply {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : α→Vec→L[ℝ]Vec} {f : α→Vec} {C : ℝ}
    (hf : Integrable f μ) (hG : AEStronglyMeasurable G μ)
    (hb : ∀ᵐ x∂μ,‖G x‖≤C) : Integrable (fun x=>G x (f x)) μ := by
  apply (hf.norm.const_mul C).mono'
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hG.prodMk hf.aestronglyMeasurable))
  filter_upwards [hb] with x hx
  exact (G x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

lemma PhaseFlowOn.integrable_receiver_multiplier {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase)
    {G : ℝ→Vec→L[ℝ]Vec} (hG : Continuous G) {f : ℝ×Phase→Vec} (hf : Integrable f) :
    Integrable (fun p=>G (labelReceiverTime F.flow zX T p) (f p)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  exact integrable_bounded_clm_apply hf
    (hG.measurable.comp (F.labelReceiverTime_measurable zX)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p=>hC _ (F.labelReceiverTime_mem hT zX p)))

def selectedMultiplierForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (G : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : Vec :=
  G (labelReceiverTime α zX T p) (selectedLabelSignedForce s α zX T Q ψ p)

def selectedMultiplierCosts (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (G G' : ℝ→Vec→L[ℝ]Vec) (p : ℝ×Phase) : Vec :=
  G (labelReceiverTime α zX T p) (selectedLabelCosts s α zX T Q ψ p)+
    G' (labelReceiverTime α zX T p)
      (labelWeight α zX T Q ψ p • actualLabelRatePrimitive s α zX T p)

lemma PhaseFlowOn.selectedMultiplier_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) {G G' : ℝ→Vec→L[ℝ]Vec}
    (hG : Continuous G) (hG' : Continuous G') :
    Integrable (selectedMultiplierForce s F.flow zX T Q ψ G) ∧
      Integrable (selectedMultiplierCosts s F.flow zX T Q ψ G G') := by
  have hf := F.selectedLabelSignedForce_integrable hs hT zX Q hψ.continuous.measurable hψb
  have hc := F.selectedLabelCosts_integrable hs hT zX Q hψ hψb
  have hp := (F.actualLabelRatePrimitive_integrable hs zX).bdd_smul 1
    (F.labelWeight_measurable zX Q hψ.continuous.measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p=>by
      simpa only [Real.norm_eq_abs] using F.labelWeight_bound hT zX Q hψb p))
  exact ⟨F.integrable_receiver_multiplier hT zX hG hf,
    (F.integrable_receiver_multiplier hT zX hG hc).add
      (F.integrable_receiver_multiplier hT zX hG' hp)⟩

lemma PhaseFlowOn.receiver_multiplier_closed_regularity {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX z : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow z b).1‖=T)
    (hne : ∀σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow z σ).1)
    {G G' : ℝ→Vec→L[ℝ]Vec} (hG : ContinuousOn G (Icc 0 T))
    (hG' : ContinuousOn G' (Icc 0 T)) (hGd : ∀t∈Ioo 0 T,HasDerivAt G (G' t) t) :
    let τ := branchTime F.flow zX z T
    ContinuousOn (fun σ=>G (τ σ)) (Icc 0 b) ∧
    ContinuousOn (fun σ=>branchRate F.flow zX z T σ • G' (τ σ)) (Icc 0 b) ∧
    ∀σ∈Ioo 0 b,HasDerivAt (fun σ=>G (τ σ))
      (branchRate F.flow zX z T σ • G' (τ σ)) σ := by
  dsimp only
  have hT : 0≤T := hb.1.trans hb.2
  have hclosed := F.closedBranchDomain_eq hT zX z hb he
  have hmem : ∀σ∈Icc 0 b,σ∈closedBranchDomain F.flow zX z T := fun σ hσ=>by
    rwa [hclosed]
  have ht : ∀σ∈Icc 0 b,branchTime F.flow zX z T σ∈Icc 0 T := fun σ hσ=>
    ⟨hσ.1.trans (F.branch_spec_closed zX z (hmem σ hσ)).1.1,
      (F.branch_spec_closed zX z (hmem σ hσ)).1.2⟩
  obtain ⟨C,hC⟩ := F.branch_lipschitzOn_closed hT zX z
  have hτ : ContinuousOn (branchTime F.flow zX z T) (Icc 0 b) := by
    simpa only [hclosed] using hC.continuousOn
  have hr := (F.branchCutoffState_closed_regularity hs zX z hb he hne).2.1.fst.add (continuousOn_const (c:=(1:ℝ)))
  have hrate : ContinuousOn (branchRate F.flow zX z T) (Icc 0 b) := by
    convert hr using 1
    ext σ
    simp only [Pi.add_apply,branchCutoffStateRate,sub_add_cancel]
  refine ⟨hG.comp hτ ht,hrate.smul (hG'.comp hτ ht),?_⟩
  intro σ hσ
  have hdom : σ∈branchDomain F.flow zX z T := by rwa [F.branchDomain_eq hT zX z hb he]
  have hsT : σ∈Icc 0 T := ⟨hσ.1.le,hσ.2.le.trans hb.2⟩
  have hti := F.branch_time_mem zX z hdom (hne σ hsT)
  exact (hGd _ ⟨hσ.1.trans hti.1,hti.2⟩).scomp σ (F.branch_differential zX z hdom (hne σ hsT)).2

lemma PhaseFlowOn.selected_multiplier_branch_formula {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX z : Phase)
    (hb : b∈Icc 0 T) (he : b+‖(F.flow zX T).1-(F.flow z b).1‖=T)
    (hne : ∀σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow z σ).1)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal}
    (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T))
    (hW' : ContinuousOn W' (Icc 0 T)) (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫σ : ℝ,selectedMultiplierForce s F.flow zX T Q ψ W (σ,z)) =
      (s.f (0,z)*ψ (branchTime F.flow zX z T 0)*
        selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX z 0)) •
      W (branchTime F.flow zX z T 0) (retardedPrimitive (branchTime F.flow zX z T 0) (velocity (F.flow zX (branchTime F.flow zX z T 0)).2)
        (velocity z.2) (branchDirection F.flow zX z T 0))+
        ∫σ : ℝ,selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z) := by
  classical
  have hT : 0≤T := hb.1.trans hb.2
  let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX z σ)
  let τ := branchTime F.flow zX z T
  let P := fun σ=>retardedPrimitive (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
  let K := fun σ=>signedForceKernel (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
    (phaseAcceleration s.E s.B F.flow z σ)
  let R := fun σ=>signedRemainder (τ σ-σ) (velocity (F.flow zX (τ σ)).2)
    (velocity (F.flow z σ).2) (branchDirection F.flow zX z T σ)
    (phaseAcceleration s.E s.B F.flow zX (τ σ))
  let G := fun σ=>(ψ (τ σ)*χ σ) • W (τ σ) (K σ)
  let H := fun σ=>(deriv ψ (τ σ)*branchRate F.flow zX z T σ*χ σ+
      ψ (τ σ)*branchSelectedRate s.E s.B F.flow T zX z Q σ) • W (τ σ) (P σ) +
      (ψ (τ σ)*χ σ) • ((branchRate F.flow zX z T σ • W' (τ σ)) (P σ)+W (τ σ) (R σ))
  have hd : ∀σ,(σ,z)∈labelBranchDomain F.flow zX T ↔ σ∈Ioo 0 b := by
    intro σ
    change (σ∈branchDomain F.flow zX z T ∧ _) ↔ _
    rw [F.branchDomain_eq hT zX z hb he]
    constructor
    · exact And.left
    · intro hσ
      exact ⟨hσ,hne σ ⟨hσ.1.le,hσ.2.le.trans hb.2⟩⟩
  have hK : (fun σ=>selectedMultiplierForce s F.flow zX T Q ψ W (σ,z))=
      (Ioo (0:ℝ) b).indicator (fun σ=>s.f (0,z) • G σ) := by
    funext σ
    by_cases hσ : σ∈Ioo (0:ℝ) b
    · have hp := (hd σ).mpr hσ
      have hp' : (σ,z)∈jointBranchDomain F.flow zX T := hp
      simp only [selectedMultiplierForce,selectedLabelSignedForce,labelWeight,labelReceiverTime,labelSelectedCutoff,
        actualLabelSignedForce,indicator_of_mem hp,indicator_of_mem hp',indicator_of_mem hσ,
        G,K,τ,χ,sourceAcceleration,phaseAcceleration,smul_smul,map_smul]
      congr 1
      ring
    · have hp := mt (hd σ).mp hσ
      simp only [selectedMultiplierForce,selectedLabelSignedForce,actualLabelSignedForce,indicator_of_notMem hp,
        indicator_of_notMem hσ,smul_zero,map_zero]
  have hH : (fun σ=>selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z))=
      (Ioo (0:ℝ) b).indicator (fun σ=>s.f (0,z) • H σ) := by
    funext σ
    by_cases hσ : σ∈Ioo (0:ℝ) b
    · have hp := (hd σ).mpr hσ
      have hp' : (σ,z)∈jointBranchDomain F.flow zX T := hp
      simp only [selectedMultiplierCosts,selectedLabelCosts,labelWeight,labelReceiverTime,labelSelectedCutoff,
        actualLabelRatePrimitive,actualLabelCutoffCost,actualLabelPrimitive,actualLabelRemainder,
        indicator_of_mem hp,indicator_of_mem hp',indicator_of_mem hσ,H,P,R,τ,χ,
        smul_smul,smul_add,add_smul,map_smul,map_add,smul_apply]
      module
    · have hp := mt (hd σ).mp hσ
      simp only [selectedMultiplierCosts,selectedLabelCosts,actualLabelRatePrimitive,actualLabelCutoffCost,
        actualLabelPrimitive,actualLabelRemainder,indicator_of_notMem hp,
        indicator_of_notMem hσ,smul_zero,add_zero,map_zero]
  have hI : (∫σ in 0..b,G σ)=(ψ (τ 0)*χ 0) • W (τ 0) (P 0)+∫σ in 0..b,H σ := by
    obtain ⟨hA,hA',hAd⟩ := F.receiver_multiplier_closed_regularity hs zX z hb he hne hW hW' hWd
    exact F.actual_selected_temporal_signed_formula hs zX z hb he hne Q hψ hψT hA hA' hAd
  rw [hK,hH,integral_indicator measurableSet_Ioo,integral_indicator measurableSet_Ioo,
    integral_smul,integral_smul,restrict_Ioo_eq_restrict_Ioc,
    ←intervalIntegral.integral_of_le hb.1,←intervalIntegral.integral_of_le hb.1,hI,smul_add]
  congr 1
  simp only [P,τ,χ,sub_zero,F.initial,smul_smul]
  congr 1
  ring

lemma PhaseFlowOn.ae_selected_multiplier_formula {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal}
    (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T))
    (hW' : ContinuousOn W' (Icc 0 T)) (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    ∀ᵐ z : Phase,(∫σ : ℝ,selectedMultiplierForce s F.flow zX T Q ψ W (σ,z)) =
      selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z+
        ∫σ : ℝ,selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z) := by
  classical
  have hn : ∀ᵐ z ∂(volume : Measure Phase),
      z∉{y : Phase | ∃t∈Icc 0 T,(F.flow y t).1=(F.flow zX t).1} :=
    ae_iff.mpr (by simpa only [mem_ofPred_eq,not_not] using F.closed_collision_null hT zX)
  filter_upwards [hn] with z hz
  have hne : ∀t∈Icc 0 T,(F.flow zX t).1≠(F.flow z t).1 := fun t ht he=>hz ⟨t,ht,he.symm⟩
  by_cases hy : z∈initialConeLabels T (F.flow zX T).1
  · obtain ⟨b,⟨hb,he⟩,_⟩ := F.exists_emission ⟨hT,le_rfl⟩ (F.flow zX T).1 hy
    have hp : z∈initialPuncturedCone F.flow zX T := ⟨hy,by
      have hn0 := hne 0 ⟨le_rfl,hT⟩
      change (F.flow zX 0).1 ≠ (F.flow z 0).1 at hn0
      simpa only [F.initial,mem_ofPred_eq,ne_eq,eq_comm] using hn0⟩
    rw [F.selected_multiplier_branch_formula hs zX z hb he hne Q hψ hψT hW hW' hWd]
    congr 1
    simp only [selectedInitialKernel,indicator_of_mem hp,
      actualCutoffCoordinates,sub_zero,F.initial,stateCutoff,initialConeState]
  · have hd := F.branchDomain_empty_of_not_initial hT zX z hy
    have hp : z∉initialPuncturedCone F.flow zX T := fun hz=>hy hz.1
    have he : ∀σ,(σ,z)∉labelBranchDomain F.flow zX T := fun σ hh=>by
      have hh' := hh.1
      rw [hd] at hh'
      exact hh'
    have hK : (fun σ=>selectedMultiplierForce s F.flow zX T Q ψ W (σ,z))=0 := by
      funext σ
      simp only [selectedMultiplierForce,selectedLabelSignedForce,actualLabelSignedForce,indicator_of_notMem (he σ),
        smul_zero,Pi.zero_apply,map_zero]
    have hC : (fun σ=>selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z))=0 := by
      funext σ
      simp only [selectedMultiplierCosts,selectedLabelCosts,actualLabelCutoffCost,actualLabelRatePrimitive,
        actualLabelPrimitive,actualLabelRemainder,indicator_of_notMem (he σ),
        smul_zero,add_zero,Pi.zero_apply,map_zero]
    simp only [hK,hC,selectedInitialKernel,indicator_of_notMem hp]
    simp

lemma PhaseFlowOn.selected_multiplier_fubini {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : Continuous W) (hW' : Continuous W')
    (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫σ : ℝ,∫z : Phase,selectedMultiplierForce s F.flow zX T Q ψ W (σ,z)) =
      (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z)+
      ∫σ : ℝ,∫z : Phase,selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z) := by
  obtain ⟨hiK,hiC⟩ := F.selectedMultiplier_integrable hs hT zX Q hψ hψb hW hW'
  have hfc : Continuous (fun z=>s.f (0,z)) := hs.f_smooth.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _=>⟨⟨le_rfl,hT⟩,mem_univ _⟩)
  obtain ⟨K,hK,hcompact⟩ := hs.compact
  have hfs : HasCompactSupport (fun z=>s.f (0,z)) := hK.of_isClosed_subset (isClosed_tsupport _)
    (hcompact 0 ⟨le_rfl,hT⟩)
  obtain ⟨C,_,hb⟩ := selectedInitialKernel_integrable_bound hfc hfs (hs.nonnegative 0 ⟨le_rfl,hT⟩)
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hW.continuousOn
  have hiB := (hb s.E s.B T F zX Q ψ W (max M 0) hT (le_max_right _ _)
    hψ.continuous.continuousOn hW.continuousOn (fun t ht=>(hM t ht).trans (le_max_left _ _))).1
  have hKi : Integrable (Function.uncurry (fun σ z=>selectedMultiplierForce s F.flow zX T Q ψ W (σ,z)))
      (volume.prod volume) := hiK
  have hCi : Integrable (Function.uncurry (fun σ z=>selectedMultiplierCosts s F.flow zX T Q ψ W W' (σ,z)))
      (volume.prod volume) := hiC
  rw [integral_integral_swap hKi]
  rw [integral_congr_ae (F.ae_selected_multiplier_formula hs hT zX Q hψ.lipschitzOnWith hψT
      hW.continuousOn hW'.continuousOn hWd),
    integral_add hiB hiC.integral_prod_right,←integral_integral_swap hCi]

end RVM

end

end OAI
