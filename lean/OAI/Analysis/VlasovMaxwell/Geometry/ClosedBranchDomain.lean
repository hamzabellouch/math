import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ReceiverQCLM
import OAI.Analysis.VlasovMaxwell.Flow.PhaseAcceleration

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
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def closedBranchDomain (α : Phase→ℝ→Phase) (zX zY : Phase) (T : ℝ) : Set ℝ :=
  {s | s∈Icc 0 T ∧ s+‖(α zX T).1-(α zY s).1‖ ≤ T}

lemma PhaseFlowOn.branch_spec_closed {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s∈closedBranchDomain F.flow zX zY T) :
    branchTime F.flow zX zY T s∈Icc s T ∧
      branchTime F.flow zX zY T s-s=
        ‖(F.flow zX (branchTime F.flow zX zY T s)).1-(F.flow zY s).1‖ := by
  have hsub : Icc s T⊆Icc 0 T := fun _ ht=>⟨hs.1.1.trans ht.1,ht.2⟩
  have hc : ContinuousOn (fun t=>t-‖(F.flow zX t).1-(F.flow zY s).1‖) (Icc s T) :=
    continuousOn_id.sub ((((F.continuousOn_time zX).mono hsub).fst.sub continuousOn_const).norm)
  have hstart : s-‖(F.flow zX s).1-(F.flow zY s).1‖ ≤ s := sub_le_self _ (norm_nonneg _)
  have hend : s ≤ T-‖(F.flow zX T).1-(F.flow zY s).1‖ := by linarith [hs.2]
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hs.1.2 hc ⟨hstart,hend⟩
  have hex : ∃ t,t∈Icc s T ∧ t-s=‖(F.flow zX t).1-(F.flow zY s).1‖ :=
    ⟨t,ht,by linarith⟩
  simpa only [branchTime,dite_eq_left hex] using hex.choose_spec

lemma PhaseFlowOn.branch_unique_closed {E B : Field} {T s t : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s∈closedBranchDomain F.flow zX zY T)
    (ht : t∈Icc s T) (he : t-s=‖(F.flow zX t).1-(F.flow zY s).1‖) :
    t=branchTime F.flow zX zY T s := by
  obtain ⟨hτ,hcone⟩ := F.branch_spec_closed zX zY hs
  apply (F.arrival_strictMono (hs.1.1.trans hs.1.2) zX (F.flow zY s).1).injOn
    ⟨hs.1.1.trans ht.1,ht.2⟩ ⟨hs.1.1.trans hτ.1,hτ.2⟩
  dsimp only
  linarith

lemma PhaseFlowOn.closedBranchDomain_eq {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX zY : Phase) {b : ℝ} (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T) :
    closedBranchDomain F.flow zX zY T=Icc 0 b := by
  have hm := F.emission_strictMono hT zY (F.flow zX T).1
  ext s
  constructor
  · intro hs
    refine ⟨hs.1.1,?_⟩
    by_contra h
    have hh := hm hb hs.1 (lt_of_not_ge h)
    linarith [hs.2]
  · intro hs
    have ht : s∈Icc 0 T := ⟨hs.1,hs.2.trans hb.2⟩
    refine ⟨ht,?_⟩
    have hh := hm.monotoneOn ht hb hs.2
    linarith

lemma PhaseFlowOn.branchDomain_eq {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX zY : Phase) {b : ℝ} (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T) :
    branchDomain F.flow zX zY T=Ioo 0 b := by
  have hm := F.emission_strictMono hT zY (F.flow zX T).1
  ext s
  constructor
  · intro hs
    refine ⟨hs.1.1,?_⟩
    by_contra h
    have hh := hm.monotoneOn hb (Ioo_subset_Icc_self hs.1) (le_of_not_gt h)
    linarith [hs.2]
  · intro hs
    have ht : s∈Ioo 0 T := ⟨hs.1,hs.2.trans_le hb.2⟩
    refine ⟨ht,?_⟩
    have hh := hm (Ioo_subset_Icc_self ht) hb hs.2
    linarith

lemma PhaseFlowOn.branch_final_endpoint {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) {b : ℝ} (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T) :
    branchTime F.flow zX zY T b=T := by
  symm
  apply F.branch_unique_closed zX zY ⟨hb,he.le⟩ ⟨hb.2,le_rfl⟩
  linarith

lemma PhaseFlowOn.branch_lipschitzOn_closed {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX zY : Phase) :
    ∃ C : ℝ≥0,LipschitzOnWith C (branchTime F.flow zX zY T)
      (closedBranchDomain F.flow zX zY T) := by
  obtain ⟨c,hc,hX⟩ := F.timelike hT zX
  obtain ⟨d,hd,hY⟩ := F.timelike hT zY
  let C : ℝ≥0 := ⟨2/(1-(c:ℝ)),by positivity⟩
  refine ⟨C,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro s hs r hr
  let t := branchTime F.flow zX zY T s
  let τ := branchTime F.flow zX zY T r
  obtain ⟨ht,hst⟩ := F.branch_spec_closed zX zY hs
  obtain ⟨hτ,hrt⟩ := F.branch_spec_closed zX zY hr
  have ht0 : t∈Icc 0 T := ⟨hs.1.1.trans ht.1,ht.2⟩
  have hτ0 : τ∈Icc 0 T := ⟨hr.1.1.trans hτ.1,hτ.2⟩
  have hdx := hX.dist_le_mul t ht0 τ hτ0
  have hdy := hY.dist_le_mul s hs.1 r hr.1
  have hy : dist (F.flow zY s).1 (F.flow zY r).1 ≤ dist s r :=
    hdy.trans (mul_le_of_le_one_left dist_nonneg hd.le)
  have heq : t-τ=(s-r)+(‖(F.flow zX t).1-(F.flow zY s).1‖-
      ‖(F.flow zX τ).1-(F.flow zY r).1‖) := by
    change t-s=_ at hst
    change τ-r=_ at hrt
    linarith
  have hn := abs_norm_sub_norm_le ((F.flow zX t).1-(F.flow zY s).1)
    ((F.flow zX τ).1-(F.flow zY r).1)
  have htriangle : ‖((F.flow zX t).1-(F.flow zY s).1)-
      ((F.flow zX τ).1-(F.flow zY r).1)‖ ≤
      dist (F.flow zX t).1 (F.flow zX τ).1+dist (F.flow zY s).1 (F.flow zY r).1 := by
    rw [dist_eq_norm,dist_eq_norm]
    calc
      _ = ‖((F.flow zX t).1-(F.flow zX τ).1)-((F.flow zY s).1-(F.flow zY r).1)‖ := by congr 1; abel
      _  ≤  _ := norm_sub_le _ _
  have hg : dist t τ ≤ dist s r+(c:ℝ)*dist t τ+dist s r := by
    have hab := abs_add_le (s-r)
      (‖(F.flow zX t).1-(F.flow zY s).1‖-‖(F.flow zX τ).1-(F.flow zY r).1‖)
    rw [← heq,← Real.dist_eq,← Real.dist_eq] at hab
    linarith [hn.trans htriangle]
  change dist t τ ≤ (2/(1-(c:ℝ)))*dist s r
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  nlinarith

lemma PhaseFlowOn.branch_radius_pos_closed {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈closedBranchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    0 < branchTime F.flow zX zY T σ-σ := by
  obtain ⟨ht,he⟩ := F.branch_spec_closed zX zY hσ
  apply sub_pos.mpr
  by_contra h
  have hh : branchTime F.flow zX zY T σ=σ := le_antisymm (le_of_not_gt h) ht.1
  rw [hh,sub_self] at he
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp he.symm))

lemma PhaseFlowOn.branchDirection_norm_closed {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈closedBranchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    ‖branchDirection F.flow zX zY T σ‖=1 := by
  have hp := F.branch_radius_pos_closed zX zY hσ hne
  have he := (F.branch_spec_closed zX zY hσ).2
  dsimp only [branchDirection]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),← he]
  exact inv_mul_cancel₀ hp.ne'

lemma PhaseFlowOn.acceleration_continuousOn_closed {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContinuousOn (phaseAcceleration s.E s.B F.flow z) (Icc 0 T) := by
  have hf := F.continuousOn_time z
  have hp : ContinuousOn (fun t => (t,(F.flow z t).1)) (Icc 0 T) := continuousOn_id.prodMk hf.fst
  have hE : ContinuousOn (fun t => s.E (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.E_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hB : ContinuousOn (fun t => s.B (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.B_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hu : ContinuousOn (fun t => velocity (F.flow z t).2) (Icc 0 T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  have hK : ContinuousOn (fun t => s.E (t,(F.flow z t).1)+
      cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))) (Icc 0 T) :=
    hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))
  exact (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp_continuousOn hf.snd).clm_apply hK

lemma continuousOn_retardedPrimitive {r : ℝ → ℝ} {a u n : ℝ → Vec} {S : Set ℝ}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S)
    (hu : ContinuousOn u S) (hn : ContinuousOn n S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hd : ∀ s ∈ S, 1-dot (n s) (u s) ≠ 0)
    (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContinuousOn (fun s => retardedPrimitive (r s) (a s) (u s) (n s)) S := by
  have hdu : ContinuousOn (fun s => 1-dot (n s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner hu)
  have hDa : ContinuousOn (fun s => 1-dot (n s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (hn.inner ha)
  have hea : ContinuousOn (fun s => 1-dot (a s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) S).sub (ha.inner hu)
  exact ((hr.mul hdu).inv₀ (fun s hs => mul_ne_zero (hr0 s hs) (hd s hs))).smul
    (hu.sub ((hea.div hDa hD).smul hn))

lemma PhaseFlowOn.actual_signed_identity_closed {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ) =
      retardedPrimitive (r 0) (a 0) (u 0) (n 0)-retardedPrimitive (r b) (a b) (u b) (n b)+
      ∫ σ in 0..b,signedRemainder (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zX (τ σ)) := by
  let τ := branchTime F.flow zX zY T
  let r := fun σ=>τ σ-σ
  let a := fun σ=>velocity (F.flow zX (τ σ)).2
  let u := fun σ=>velocity (F.flow zY σ).2
  let n := branchDirection F.flow zX zY T
  let P := fun σ=>retardedPrimitive (r σ) (a σ) (u σ) (n σ)
  let K := fun σ=>signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)
  let R := fun σ=>signedRemainder (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zX (τ σ))
  have hT : 0≤T := hb.1.trans hb.2
  have hsub : Icc 0 b⊆Icc 0 T := fun _ hx=>⟨hx.1,hx.2.trans hb.2⟩
  have hclosed := F.closedBranchDomain_eq hT zX zY hb he
  have hopen := F.branchDomain_eq hT zX zY hb he
  have hmem : ∀ σ∈Icc 0 b,σ∈closedBranchDomain F.flow zX zY T := by
    intro σ hσ
    rwa [hclosed]
  have htmem : ∀ σ∈Icc 0 b,τ σ∈Icc 0 T := fun σ hσ=>
    ⟨hσ.1.trans (F.branch_spec_closed zX zY (hmem σ hσ)).1.1,
      (F.branch_spec_closed zX zY (hmem σ hσ)).1.2⟩
  have hτ : ContinuousOn τ (Icc 0 b) := by
    obtain ⟨C,hC⟩ := F.branch_lipschitzOn_closed hT zX zY
    simpa only [hclosed] using hC.continuousOn
  have hr : ContinuousOn r (Icc 0 b) := hτ.sub continuousOn_id
  have hX := (F.continuousOn_time zX).comp hτ htmem
  have hY := (F.continuousOn_time zY).mono hsub
  have ha : ContinuousOn a (Icc 0 b) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hX.snd
  have hu : ContinuousOn u (Icc 0 b) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hY.snd
  have hr0 : ∀ σ∈Icc 0 b,r σ≠0 := fun σ hσ=>
    (F.branch_radius_pos_closed zX zY (hmem σ hσ) (hne σ (hsub hσ))).ne'
  have hn : ContinuousOn n (Icc 0 b) := (hr.inv₀ hr0).smul (hX.fst.sub hY.fst)
  have hnorm : ∀ σ∈Icc 0 b,‖n σ‖=1 := fun σ hσ=>
    F.branchDirection_norm_closed zX zY (hmem σ hσ) (hne σ (hsub hσ))
  have hd : ∀ σ∈Icc 0 b,1-dot (n σ) (u σ)≠0 := fun σ hσ=>
    (cone_denom_pos (F.flow zY σ).2 _ (hnorm σ hσ)).ne'
  have hD : ∀ σ∈Icc 0 b,1-dot (n σ) (a σ)≠0 := fun σ hσ=>
    (cone_denom_pos (F.flow zX (τ σ)).2 _ (hnorm σ hσ)).ne'
  have hP : ContinuousOn P (Icc 0 b) := continuousOn_retardedPrimitive hr ha hu hn hr0 hd hD
  have hK : ContinuousOn K (Icc 0 b) := continuousOn_signedForceKernel hr ha hu hn
    ((F.acceleration_continuousOn_closed hs zY).mono hsub) hr0 hd hD
  have hR : ContinuousOn R (Icc 0 b) := continuousOn_signedRemainder hr ha hu hn
    ((F.acceleration_continuousOn_closed hs zX).comp hτ htmem) hr0 hD
  have hder : ∀ σ∈Ioo 0 b,HasDerivAt P (R σ-K σ) σ := by
    intro σ hσ
    have hσ' : σ∈branchDomain F.flow zX zY T := by rwa [hopen]
    have hneσ := hne σ (hsub (Ioo_subset_Icc_self hσ))
    have ht := F.branch_time_mem zX zY hσ' hneσ
    have hτ' := (F.branch_differential zX zY hσ' hneσ).2
    have hr' : HasDerivAt r ((1-dot (n σ) (u σ))/(1-dot (n σ) (a σ))-1) σ :=
      hτ'.sub (hasDerivAt_id σ)
    have ha' : HasDerivAt a
        (((1-dot (n σ) (u σ))/(1-dot (n σ) (a σ))) • phaseAcceleration s.E s.B F.flow zX (τ σ)) σ :=
      (F.velocity_hasDerivAt zX ⟨hσ'.1.1.trans ht.1,ht.2⟩).scomp σ hτ'
    have hσc := Ioo_subset_Icc_self hσ
    have hp := hasDerivAt_retardedPrimitive hr' ha' (F.velocity_hasDerivAt zY hσ'.1)
      (F.branchDirection_hasDerivAt zX zY hσ' hneσ) (hr0 σ hσc) (hd σ hσc) (hD σ hσc)
    convert hp using 1
    have hh := signed_force_identity (r σ) (a σ) (u σ) (n σ)
      (phaseAcceleration s.E s.B F.flow zY σ) (phaseAcceleration s.E s.B F.flow zX (τ σ))
      (hr0 σ hσc) (hd σ hσc) (hD σ hσc)
    dsimp only [R,K]
    rw [hh]
    unfold signedRemainder
    abel
  have hKi : IntervalIntegrable K volume 0 b := hK.intervalIntegrable_of_Icc hb.1
  have hRi : IntervalIntegrable R volume 0 b := hR.intervalIntegrable_of_Icc hb.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.1 hP hder (hRi.sub hKi)
  rw [intervalIntegral.integral_sub hRi hKi] at hftc
  change (∫ σ in 0..b,K σ)=P 0-P b+∫ σ in 0..b,R σ
  have hh := congrArg (fun v=>(∫ σ in 0..b,R σ)-v) hftc
  convert hh using 1 <;> abel

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

def labelBranchDomain (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : Set (ℝ×Phase) :=
  {p | p.1∈branchDomain α zX p.2 T ∧ (α zX p.1).1≠(α p.2 p.1).1}

lemma labelBranchDomain_iff (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (p : ℝ×Phase) :
    p∈labelBranchDomain α zX T ↔ (p.1,α p.2 p.1)∈arrivalPhaseDomain α zX T := by
  change ((p.1∈Ioo 0 T ∧ p.1+‖(α zX T).1-(α p.2 p.1).1‖<T) ∧
    (α zX p.1).1≠(α p.2 p.1).1) ↔ _
  change _ ↔ (p.1∈Ioo 0 T ∧ p.1+‖(α zX T).1-(α p.2 p.1).1‖<T ∧
    (α zX p.1).1≠(α p.2 p.1).1)
  tauto

lemma PhaseFlowOn.arrivalTime_flow_eq_branchTime {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hp : (σ,zY)∈labelBranchDomain F.flow zX T) :
    arrivalTime F.flow zX T (σ,(F.flow zY σ).1)=branchTime F.flow zX zY T σ := by
  have hh := F.arrival_time_spec zX ((labelBranchDomain_iff _ _ _ _).mp hp)
  exact F.branch_unique zX zY hp.1 (Ioo_subset_Icc_self hh.1) hh.2

def actualLabelSignedForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→Vec :=
  (labelBranchDomain α zX T).indicator (fun p=>s.f (0,p.2) •
    signedForceKernel (branchTime α zX p.2 T p.1-p.1)
      (velocity (α zX (branchTime α zX p.2 T p.1)).2)
      (velocity (α p.2 p.1).2)
      (branchDirection α zX p.2 T p.1)
      (sourceAcceleration s (p.1,α p.2 p.1)))

lemma PhaseFlowOn.actualLabelSignedForce_eq_pullback {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    actualLabelSignedForce s F.flow zX T =
      phaseTimePullback F.flow T (actualArrivalSignedForce s F.flow zX T) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have he := (labelBranchDomain_iff _ _ _ _).mp hp
    have ht : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase) := ⟨hp.1.1,mem_univ _⟩
    rw [actualLabelSignedForce,indicator_of_mem hp,phaseTimePullback,indicator_of_mem ht,
      actualArrivalSignedForce,indicator_of_mem he]
    rw [F.transport hs.f_smooth hs.vlasov (Ioo_subset_Icc_self hp.1.1) p.2]
    simp only [arrivalRadius,arrivalDirection,branchDirection,F.arrivalTime_flow_eq_branchTime zX p.2 hp]
  · have he := mt (labelBranchDomain_iff _ _ _ _).mpr hp
    rw [actualLabelSignedForce,indicator_of_notMem hp]
    by_cases ht : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase)
    · rw [phaseTimePullback,indicator_of_mem ht,actualArrivalSignedForce,indicator_of_notMem he]
    · rw [phaseTimePullback,indicator_of_notMem ht]

lemma PhaseFlowOn.measurable_actualLabelSignedForce {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualLabelSignedForce s F.flow zX T) := by
  rw [F.actualLabelSignedForce_eq_pullback hs zX]
  exact F.measurable_phaseTimePullback (F.actualArrivalSignedForce_measurable hs zX)

lemma PhaseFlowOn.actualLabelSignedForce_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Integrable (actualLabelSignedForce s F.flow zX T) := by
  rw [F.actualLabelSignedForce_eq_pullback hs zX]
  exact (F.phaseTimePullback_integrable_iff (F.actualArrivalSignedForce_measurable hs zX)).mpr
    (F.actualArrivalSignedForce_integrable hs zX).integrableOn

lemma PhaseFlowOn.label_signed_integral_fubini {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    (∫ z : Phase,∫ σ : ℝ,actualLabelSignedForce s F.flow zX T (σ,z))=
      ∫ σ : ℝ,∫ z : Phase,actualLabelSignedForce s F.flow zX T (σ,z) := by
  exact (integral_integral_swap (f:=fun σ z=>actualLabelSignedForce s F.flow zX T (σ,z))
    (F.actualLabelSignedForce_integrable hs zX)).symm

def normalisedPrimitive (r : ℝ) (a u n : Vec) : Vec :=
  (r/(1-dot n u)) • signedPrimitive a u n

lemma normalisedPrimitive_eq {r : ℝ} (a u n : Vec) (hr : r≠0) :
    normalisedPrimitive r a u n=r^2 • retardedPrimitive r a u n := by
  rw [normalisedPrimitive,retardedPrimitive,smul_smul]
  congr 1
  field_simp

def normalisedRemainder (r : ℝ) (a u n b : Vec) : Vec :=
  ((1-dot a u)/(1-dot n a)^2) • (((1-dot a a)/(1-dot n a)) • n-a)+
    (r*dot b (signedPrimitive a u n)/(1-dot n a)^2) • n

lemma normalisedRemainder_eq {r : ℝ} (a u n b : Vec) (hr : r≠0) :
    normalisedRemainder r a u n b=r^2 • signedRemainder r a u n b := by
  simp only [normalisedRemainder,signedRemainder,smul_add,smul_smul]
  congr 2 <;> field_simp

lemma continuousOn_normalisedPrimitive {Q : Type*} [TopologicalSpace Q]
    {r : Q→ℝ} {a u n : Q→Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S) (hu : ContinuousOn u S)
    (hn : ContinuousOn n S) (hd : ∀p∈S,1-dot (n p) (u p)≠0)
    (hD : ∀p∈S,1-dot (n p) (a p)≠0) :
    ContinuousOn (fun p=>normalisedPrimitive (r p) (a p) (u p) (n p)) S := by
  have hdot {f g : Q→Vec} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun p=>dot (f p) (g p)) S := by
    simpa only [dot_eq_inner] using hf.inner hg
  exact (hr.div (continuousOn_const.sub (hdot hn hu)) hd).smul
    (hu.sub (((continuousOn_const.sub (hdot ha hu)).div
      (continuousOn_const.sub (hdot hn ha)) hD).smul hn))

lemma continuousOn_normalisedRemainder {Q : Type*} [TopologicalSpace Q]
    {r : Q→ℝ} {a u n b : Q→Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S) (hu : ContinuousOn u S)
    (hn : ContinuousOn n S) (hb : ContinuousOn b S)
    (hD : ∀p∈S,1-dot (n p) (a p)≠0) :
    ContinuousOn (fun p=>normalisedRemainder (r p) (a p) (u p) (n p) (b p)) S := by
  have hdot {f g : Q→Vec} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun p=>dot (f p) (g p)) S := by
    simpa only [dot_eq_inner] using hf.inner hg
  have hden : ContinuousOn (fun p=>1-dot (n p) (a p)) S :=
    continuousOn_const.sub (hdot hn ha)
  have hp : ContinuousOn (fun p=>signedPrimitive (a p) (u p) (n p)) S :=
    hu.sub (((continuousOn_const.sub (hdot ha hu)).div hden hD).smul hn)
  exact (((continuousOn_const.sub (hdot ha hu)).div (hden.pow 2)
    (fun p hp=>pow_ne_zero _ (hD p hp))).smul
      ((((continuousOn_const.sub (hdot ha ha)).div hden hD).smul hn).sub ha)).add
    (((hr.mul (hdot hb hp)).div (hden.pow 2) (fun p hp=>pow_ne_zero _ (hD p hp))).smul hn)

lemma PhaseFlowOn.normalised_primitive_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) :
    ContinuousOn (fun p : ConeKernelState=>normalisedPrimitive (p.1.1-p.1.2)
      (velocity (F.flow zX p.1.1).2) (velocity p.2.2.2) p.2.1) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  refine continuousOn_normalisedPrimitive (continuous_fst.fst.sub continuous_fst.snd).continuousOn
    ha hu.continuousOn continuous_snd.fst.continuousOn ?_ ?_
  · intro p hp
    exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  · intro p hp
    exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

lemma PhaseFlowOn.normalised_remainder_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (fun p : ConeKernelState=>normalisedRemainder (p.1.1-p.1.2)
      (velocity (F.flow zX p.1.1).2) (velocity p.2.2.2) p.2.1
      (phaseAcceleration s.E s.B F.flow zX p.1.1)) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  have hb : ContinuousOn (fun p : ConeKernelState=>phaseAcceleration s.E s.B F.flow zX p.1.1)
      (coneKernelDomain T) := (F.acceleration_continuousOn_closed hs zX).comp
        continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)
  refine continuousOn_normalisedRemainder (continuous_fst.fst.sub continuous_fst.snd).continuousOn
    ha hu.continuousOn continuous_snd.fst.continuousOn hb ?_
  intro p hp
  exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

def labelKernelState (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (p : ℝ×Phase) : ConeKernelState :=
  ((branchTime α zX p.2 T p.1,p.1),(branchDirection α zX p.2 T p.1,α p.2 p.1))

def labelConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A : ConeKernelState→Vec) : ℝ×Phase→Vec :=
  (labelBranchDomain α zX T).indicator (fun p=>(branchTime α zX p.2 T p.1-p.1)⁻¹^2 •
    (s.f (0,p.2) • A (labelKernelState α zX T p)))

lemma PhaseFlowOn.labelKernelState_eq_arrival {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈labelBranchDomain F.flow zX T) :
    labelKernelState F.flow zX T p=arrivalKernelState F.flow zX T (p.1,F.flow p.2 p.1) := by
  simp only [labelKernelState,arrivalKernelState,arrivalDirection,arrivalRadius,branchDirection,
    F.arrivalTime_flow_eq_branchTime zX p.2 hp]

lemma PhaseFlowOn.labelConeKernel_eq_pullback {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (A : ConeKernelState→Vec) :
    labelConeKernel s F.flow zX T A=phaseTimePullback F.flow T (arrivalConeKernel s F.flow zX T A) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have he := (labelBranchDomain_iff _ _ _ _).mp hp
    have ht : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase) := ⟨hp.1.1,mem_univ _⟩
    rw [labelConeKernel,indicator_of_mem hp,phaseTimePullback,indicator_of_mem ht,
      arrivalConeKernel,indicator_of_mem he,F.labelKernelState_eq_arrival zX hp,
      F.transport hs.f_smooth hs.vlasov (Ioo_subset_Icc_self hp.1.1) p.2]
    simp only [arrivalRadius,F.arrivalTime_flow_eq_branchTime zX p.2 hp]
  · have he := mt (labelBranchDomain_iff _ _ _ _).mpr hp
    rw [labelConeKernel,indicator_of_notMem hp]
    by_cases ht : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase)
    · rw [phaseTimePullback,indicator_of_mem ht,arrivalConeKernel,indicator_of_notMem he]
    · rw [phaseTimePullback,indicator_of_notMem ht]

lemma PhaseFlowOn.measurable_labelConeKernel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    Measurable (labelConeKernel s F.flow zX T A) := by
  rw [F.labelConeKernel_eq_pullback hs zX]
  exact F.measurable_phaseTimePullback (F.measurable_arrivalConeKernel hs zX hA)

lemma PhaseFlowOn.labelConeKernel_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    Integrable (labelConeKernel s F.flow zX T A) := by
  rw [F.labelConeKernel_eq_pullback hs zX]
  exact (F.phaseTimePullback_integrable_iff (F.measurable_arrivalConeKernel hs zX hA)).mpr
    (F.arrivalConeKernel_integrable hs zX hA).integrableOn

def actualLabelPrimitive (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→Vec :=
  (labelBranchDomain α zX T).indicator (fun p=>s.f (0,p.2) •
    retardedPrimitive (branchTime α zX p.2 T p.1-p.1)
      (velocity (α zX (branchTime α zX p.2 T p.1)).2) (velocity (α p.2 p.1).2)
      (branchDirection α zX p.2 T p.1))

def actualLabelRemainder (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→Vec :=
  (labelBranchDomain α zX T).indicator (fun p=>s.f (0,p.2) •
    signedRemainder (branchTime α zX p.2 T p.1-p.1)
      (velocity (α zX (branchTime α zX p.2 T p.1)).2) (velocity (α p.2 p.1).2)
      (branchDirection α zX p.2 T p.1)
      (phaseAcceleration s.E s.B α zX (branchTime α zX p.2 T p.1)))

lemma PhaseFlowOn.actualLabelPrimitive_eq_normalised {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) :
    actualLabelPrimitive s F.flow zX T=labelConeKernel s F.flow zX T
      (fun p=>normalisedPrimitive (p.1.1-p.1.2) (velocity (F.flow zX p.1.1).2)
        (velocity p.2.2.2) p.2.1) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hr : branchTime F.flow zX p.2 T p.1-p.1≠0 :=
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1).ne'
    simp only [actualLabelPrimitive,labelConeKernel,indicator_of_mem hp,labelKernelState,
      normalisedPrimitive_eq _ _ _ hr]
    rw [smul_comm (s.f (0,p.2)),smul_smul,←mul_pow,inv_mul_cancel₀ hr,one_pow,one_smul]
  · simp only [actualLabelPrimitive,labelConeKernel,indicator_of_notMem hp]

lemma PhaseFlowOn.actualLabelRemainder_eq_normalised {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) :
    actualLabelRemainder s F.flow zX T=labelConeKernel s F.flow zX T
      (fun p=>normalisedRemainder (p.1.1-p.1.2) (velocity (F.flow zX p.1.1).2)
        (velocity p.2.2.2) p.2.1 (phaseAcceleration s.E s.B F.flow zX p.1.1)) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hr : branchTime F.flow zX p.2 T p.1-p.1≠0 :=
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1).ne'
    simp only [actualLabelRemainder,labelConeKernel,indicator_of_mem hp,labelKernelState,
      normalisedRemainder_eq _ _ _ _ hr]
    rw [smul_comm (s.f (0,p.2)),smul_smul,←mul_pow,inv_mul_cancel₀ hr,one_pow,one_smul]
  · simp only [actualLabelRemainder,labelConeKernel,indicator_of_notMem hp]

lemma PhaseFlowOn.actualLabelPrimitive_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Integrable (actualLabelPrimitive s F.flow zX T) := by
  rw [F.actualLabelPrimitive_eq_normalised zX]
  exact F.labelConeKernel_integrable hs zX (F.normalised_primitive_continuousOn zX)

lemma PhaseFlowOn.actualLabelPrimitive_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualLabelPrimitive s F.flow zX T) := by
  rw [F.actualLabelPrimitive_eq_normalised zX]
  exact F.measurable_labelConeKernel hs zX (F.normalised_primitive_continuousOn zX)

lemma PhaseFlowOn.actualLabelRemainder_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Integrable (actualLabelRemainder s F.flow zX T) := by
  rw [F.actualLabelRemainder_eq_normalised zX]
  exact F.labelConeKernel_integrable hs zX (F.normalised_remainder_continuousOn hs zX)

lemma PhaseFlowOn.actualLabelRemainder_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualLabelRemainder s F.flow zX T) := by
  rw [F.actualLabelRemainder_eq_normalised zX]
  exact F.measurable_labelConeKernel hs zX (F.normalised_remainder_continuousOn hs zX)

end RVM

end

end OAI
