import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.InitialSignedBoundaryDensity
import OAI.Analysis.VlasovMaxwell.Regularity.AbsolutelyContinuousIntervalContinuousDerivative

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

lemma PhaseFlowOn.retarded_radius_separated_closed {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX zY : Phase)
    (hne : ∀ t∈Icc 0 T,(F.flow zX t).1≠(F.flow zY t).1) :
    ∃ δ : ℝ,0<δ ∧ ∀ σ∈closedBranchDomain F.flow zX zY T,
      δ≤branchTime F.flow zX zY T σ-σ := by
  have hc : ContinuousOn (fun t=>‖(F.flow zX t).1-(F.flow zY t).1‖) (Icc 0 T) :=
    ((F.continuousOn_time zX).fst.sub (F.continuousOn_time zY).fst).norm
  obtain ⟨t₀,ht₀,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT) hc
  have hpos : 0<‖(F.flow zX t₀).1-(F.flow zY t₀).1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hne t₀ ht₀))
  obtain ⟨c,hc1,hLip⟩ := F.timelike hT zY
  refine ⟨‖(F.flow zX t₀).1-(F.flow zY t₀).1‖/2,by positivity,?_⟩
  intro σ hσ
  let τ := branchTime F.flow zX zY T σ
  have ht := (F.branch_spec_closed zX zY hσ).1
  have ht0 : τ∈Icc 0 T := ⟨hσ.1.1.trans ht.1,ht.2⟩
  have hr : 0≤τ-σ := sub_nonneg.mpr ht.1
  have hdist := hLip.dist_le_mul τ ht0 σ hσ.1
  rw [dist_eq_norm,Real.dist_eq,abs_of_nonneg hr] at hdist
  have hbound : ‖(F.flow zY τ).1-(F.flow zY σ).1‖≤τ-σ :=
    hdist.trans (mul_le_of_le_one_left hr hc1.le)
  have hcone := (F.branch_spec_closed zX zY hσ).2
  have htriangle : ‖(F.flow zX τ).1-(F.flow zY τ).1‖ ≤
      ‖(F.flow zX τ).1-(F.flow zY σ).1‖+‖(F.flow zY σ).1-(F.flow zY τ).1‖ := by
    calc
      _ = ‖((F.flow zX τ).1-(F.flow zY σ).1)+((F.flow zY σ).1-(F.flow zY τ).1)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev (F.flow zY σ).1 (F.flow zY τ).1] at htriangle
  have hm := hmin ht0
  change ‖(F.flow zX t₀).1-(F.flow zY t₀).1‖≤‖(F.flow zX τ).1-(F.flow zY τ).1‖ at hm
  change τ-σ=‖(F.flow zX τ).1-(F.flow zY σ).1‖ at hcone
  change _≤τ-σ
  linarith

lemma PhaseFlowOn.ae_full_retarded_branch {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    ∀ᵐ zY ∂(volume : Measure Phase), zY∈initialConeLabels T (F.flow zX T).1 →
      ∃ b∈Ioo 0 T,closedBranchDomain F.flow zX zY T=Icc 0 b ∧
        branchTime F.flow zX zY T b=T ∧
        ∃ δ : ℝ,0<δ ∧ ∀ σ∈Icc 0 b,δ≤branchTime F.flow zX zY T σ-σ := by
  have hh : ∀ᵐ zY ∂(volume : Measure Phase),
      zY∉{y : Phase | ∃ t∈Icc 0 T,(F.flow y t).1=(F.flow zX t).1} :=
    ae_iff.mpr (by simpa only [Set.mem_ofPred_eq,not_not] using F.closed_collision_null hT zX)
  filter_upwards [hh] with zY hzY
  intro hy
  have hne : ∀ t∈Icc 0 T,(F.flow zX t).1≠(F.flow zY t).1 := fun t ht he=>hzY ⟨t,ht,he.symm⟩
  obtain ⟨b,⟨hb,he⟩,_⟩ := F.exists_emission ⟨hT,le_rfl⟩ (F.flow zX T).1 hy
  have hb0 : 0<b := by
    by_contra h
    have hbz : b=0 := le_antisymm (le_of_not_gt h) hb.1
    rw [hbz,F.initial,zero_add] at he
    change ‖(F.flow zX T).1-zY.1‖<T at hy
    linarith
  have hbT : b<T := by
    by_contra h
    have hbt : b=T := le_antisymm hb.2 (le_of_not_gt h)
    rw [hbt] at he
    have hn : ‖(F.flow zX T).1-(F.flow zY T).1‖=0 := by linarith
    exact hne T ⟨hT,le_rfl⟩ (sub_eq_zero.mp (norm_eq_zero.mp hn))
  have hc := F.closedBranchDomain_eq hT zX zY hb he
  refine ⟨b,⟨hb0,hbT⟩,hc,F.branch_final_endpoint zX zY hb he,?_⟩
  obtain ⟨δ,hδ,hd⟩ := F.retarded_radius_separated_closed hT zX zY hne
  exact ⟨δ,hδ,by simpa only [hc] using hd⟩

lemma PhaseFlowOn.initial_branch_pullback {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (ht : t∈Ioo 0 T) (n : Sphere) (v : Vec) :
    let y := (F.flow zX t).1-t • n.1
    branchTime F.flow zX (y,v) T 0=t ∧
      branchDirection F.flow zX (y,v) T 0=n.1 := by
  let y := (F.flow zX t).1-t • n.1
  have hT : 0≤T := ht.1.le.trans ht.2.le
  have hgeom : (F.flow zX t).1-y=t • n.1 := by dsimp only [y]; abel
  have hnorm : ‖(F.flow zX t).1-y‖=t := by
    rw [hgeom,norm_smul,Real.norm_eq_abs,abs_of_pos ht.1,sphere_norm n,mul_one]
  have hm := (F.arrival_strictMono hT zX y).monotoneOn
    (Ioo_subset_Icc_self ht) ⟨hT,le_rfl⟩ ht.2.le
  have hclosed : 0∈closedBranchDomain F.flow zX (y,v) T := by
    refine ⟨⟨le_rfl,hT⟩,?_⟩
    rw [F.initial,zero_add]
    rw [hnorm] at hm
    linarith
  have htime : branchTime F.flow zX (y,v) T 0=t := by
    symm
    apply F.branch_unique_closed zX (y,v) hclosed (Ioo_subset_Icc_self ht)
    rw [F.initial,sub_zero]
    exact hnorm.symm
  refine ⟨htime,?_⟩
  dsimp only [branchDirection]
  rw [htime,F.initial,sub_zero,hgeom,smul_smul,inv_mul_cancel₀ ht.1.ne',one_smul]

lemma PhaseFlowOn.initial_signed_boundary_pullback {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (ht : t∈Ioo 0 T)
    (f : Phase→ℝ) (ψ χ : ℝ) (P : Vec→L[ℝ]Vec) (n : Sphere) (v : Vec) :
    let y := (F.flow zX t).1-t • n.1
    let τ := branchTime F.flow zX (y,v) T 0
    let N := branchDirection F.flow zX (y,v) T 0
    (t^2*(1-dot n.1 (velocity (F.flow zX t).2))) •
      ((f (y,v)*ψ*χ) • P (retardedPrimitive τ
        (velocity (F.flow zX τ).2) (velocity (F.flow (y,v) 0).2) N)) =
      initialSignedBoundaryDensity f (F.flow zX t).1 (F.flow zX t).2 t ψ χ P n.1 v := by
  obtain ⟨hτ,hn⟩ := F.initial_branch_pullback zX ht n v
  dsimp only
  rw [hτ,hn,F.initial]
  simp only [initialSignedBoundaryDensity,smul_smul]
  congr 1
  ring

lemma PhaseFlowOn.branch_weight_ac {E B : Field} {T b : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    {ψ : ℝ→ℝ} {L : ℝ≥0} (hψ : LipschitzOnWith L ψ (Icc 0 T)) :
    AbsolutelyContinuousOnInterval (fun σ=>ψ (branchTime F.flow zX zY T σ)) 0 b := by
  have hT : 0≤T := hb.1.trans hb.2
  have hclosed := F.closedBranchDomain_eq hT zX zY hb he
  obtain ⟨C,hC⟩ := F.branch_lipschitzOn_closed hT zX zY
  have hm : MapsTo (branchTime F.flow zX zY T) (closedBranchDomain F.flow zX zY T) (Icc 0 T) := by
    intro σ hσ
    have ht := (F.branch_spec_closed zX zY hσ).1
    exact ⟨hσ.1.1.trans ht.1,ht.2⟩
  have h := hψ.comp hC hm
  rw [hclosed,← uIcc_of_le hb.1] at h
  exact h.absolutelyContinuousOnInterval

lemma PhaseFlowOn.actual_temporal_signed_identity_closed {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    {ψ : ℝ→ℝ} {L : ℝ≥0} (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : ContinuousOn W (Icc 0 b)) (hW' : ContinuousOn W' (Icc 0 b))
    (hWd : ∀ σ∈Ioo 0 b,HasDerivAt W (W' σ) σ) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,ψ (τ σ) • W σ
      (signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)) =
      ψ (τ 0) • W 0 (retardedPrimitive (r 0) (a 0) (u 0) (n 0))+
      ∫ σ in 0..b,deriv (fun σ=>ψ (τ σ)) σ • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
        ψ (τ σ) • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  have h := F.actual_weighted_signed_identity_closed hs zX zY hb he hne
    (F.branch_weight_ac zX zY hb he hψ) hW hW' hWd
  dsimp only at h ⊢
  simpa only [F.branch_final_endpoint zX zY hb he,hψT,zero_smul,sub_zero] using h
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
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma deriv_comp_of_nonzero_strict {f ψ : ℝ→ℝ} {x c : ℝ}
    (hf : HasStrictDerivAt f c x) (hc : c≠0) :
    deriv (fun r=>ψ (f r)) x=deriv ψ (f x)*c := by
  by_cases hψ : DifferentiableAt ℝ ψ (f x)
  · exact (hψ.hasDerivAt.comp x hf.hasDerivAt).deriv
  · have hnot : ¬DifferentiableAt ℝ (ψ ∘ f) x := by
      intro h
      let g := hf.localInverse f c x hc
      have hg : HasStrictDerivAt g c⁻¹ (f x) := hf.to_localInverse hc
      have hleft : g (f x)=x := (hf.eventually_left_inverse hc).self_of_nhds
      have hh : DifferentiableAt ℝ (ψ ∘ f) (g (f x)) := hleft.symm ▸ h
      have hi := hh.comp (f x) hg.hasDerivAt.differentiableAt
      apply hψ
      apply hi.congr_of_eventuallyEq
      filter_upwards [hf.eventually_right_inverse hc] with y hy
      exact congrArg ψ hy.symm
    rw [show (fun r=>ψ (f r))=ψ ∘ f from rfl,deriv_zero_of_not_differentiableAt hnot,
      deriv_zero_of_not_differentiableAt hψ,zero_mul]

lemma PhaseFlowOn.branch_weight_deriv {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) (ψ : ℝ→ℝ) :
    deriv (fun r=>ψ (branchTime F.flow zX zY T r)) σ=
      deriv ψ (branchTime F.flow zX zY T σ)*branchRate F.flow zX zY T σ := by
  obtain ⟨hc,hd⟩ := F.branch_differential zX zY hσ hne
  have hs : HasStrictDerivAt (branchTime F.flow zX zY T)
      (branchRate F.flow zX zY T σ) σ := hc.hasStrictDerivAt' hd (by norm_num)
  exact deriv_comp_of_nonzero_strict hs (F.branchRate_pos zX zY hσ hne).ne'

lemma PhaseFlowOn.branch_weight_deriv_integral {E B : Field} {T b : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    (ψ : ℝ→ℝ) (G H : ℝ→Vec) :
    (∫ σ in 0..b,deriv (fun r=>ψ (branchTime F.flow zX zY T r)) σ • G σ+H σ)=
      ∫ σ in 0..b,(deriv ψ (branchTime F.flow zX zY T σ)*branchRate F.flow zX zY T σ) • G σ+H σ := by
  apply intervalIntegral.integral_congr_uIoo
  intro σ hσ
  have hσo : σ∈Ioo 0 b := by simpa only [uIoo_of_le hb.1] using hσ
  have hdom : σ∈branchDomain F.flow zX zY T := by
    rwa [F.branchDomain_eq (hb.1.trans hb.2) zX zY hb he]
  dsimp only
  rw [F.branch_weight_deriv zX zY hdom (hne σ ⟨hσo.1.le,hσo.2.le.trans hb.2⟩) ψ]

lemma PhaseFlowOn.actual_temporal_signed_formula {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    {ψ : ℝ→ℝ} {L : ℝ≥0} (hψ : LipschitzOnWith L ψ (Icc 0 T)) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec}
    (hW : ContinuousOn W (Icc 0 b)) (hW' : ContinuousOn W' (Icc 0 b))
    (hWd : ∀ σ∈Ioo 0 b,HasDerivAt W (W' σ) σ) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,ψ (τ σ) • W σ
      (signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)) =
      ψ (τ 0) • W 0 (retardedPrimitive (r 0) (a 0) (u 0) (n 0))+
      ∫ σ in 0..b,(deriv ψ (τ σ)*branchRate F.flow zX zY T σ) • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
        ψ (τ σ) • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  have h := F.actual_temporal_signed_identity_closed hs zX zY hb he hne hψ hψT hW hW' hWd
  dsimp only at h ⊢
  rw [F.branch_weight_deriv_integral zX zY hb he hne ψ] at h
  exact h

lemma continuousOn_retardedPrimitive_space {Q : Type*} [TopologicalSpace Q] {r : Q → ℝ} {a u n : Q → Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S)
    (hu : ContinuousOn u S) (hn : ContinuousOn n S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hd : ∀ s ∈ S, 1-dot (n s) (u s) ≠ 0)
    (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContinuousOn (fun s => retardedPrimitive (r s) (a s) (u s) (n s)) S := by
  have hdu : ContinuousOn (fun s => 1-dot (n s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : Q => (1 : ℝ)) S).sub (hn.inner hu)
  have hDa : ContinuousOn (fun s => 1-dot (n s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : Q => (1 : ℝ)) S).sub (hn.inner ha)
  have hea : ContinuousOn (fun s => 1-dot (a s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : Q => (1 : ℝ)) S).sub (ha.inner hu)
  exact ((hr.mul hdu).inv₀ (fun s hs => mul_ne_zero (hr0 s hs) (hd s hs))).smul
    (hu.sub ((hea.div hDa hD).smul hn))

def initialClosedCone (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : Set Phase :=
  {z | ‖(α zX T).1-z.1‖≤T}

lemma PhaseFlowOn.initial_closed_branch_mem {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX zY : Phase)
    (hy : zY∈initialClosedCone F.flow zX T) :
    0∈closedBranchDomain F.flow zX zY T := by
  refine ⟨⟨le_rfl,hT⟩,?_⟩
  simpa only [initialClosedCone,Set.mem_ofPred,F.initial,zero_add] using hy

lemma PhaseFlowOn.initial_branch_lipschitz {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    ∃ C : ℝ≥0,LipschitzOnWith C (fun z=>branchTime F.flow zX z T 0)
      (initialClosedCone F.flow zX T) := by
  obtain ⟨c,hc,hX⟩ := F.timelike hT zX
  let C : ℝ≥0 := ⟨1/(1-(c:ℝ)),by positivity⟩
  refine ⟨C,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro z hz w hw
  obtain ⟨ht,het⟩ := F.branch_spec_closed zX z (F.initial_closed_branch_mem hT zX z hz)
  obtain ⟨hu,heu⟩ := F.branch_spec_closed zX w (F.initial_closed_branch_mem hT zX w hw)
  let t := branchTime F.flow zX z T 0
  let u := branchTime F.flow zX w T 0
  have htu := hX.dist_le_mul t ht u hu
  have he : t-u=‖(F.flow zX t).1-z.1‖-‖(F.flow zX u).1-w.1‖ := by
    rw [F.initial,sub_zero] at het heu
    exact congrArg₂ (fun a b : ℝ=>a-b) het heu
  have hdist : dist t u≤(c:ℝ)*dist t u+dist z w := by
    have hn := abs_norm_sub_norm_le ((F.flow zX t).1-z.1) ((F.flow zX u).1-w.1)
    have hh : ‖((F.flow zX t).1-z.1)-((F.flow zX u).1-w.1)‖≤
        dist (F.flow zX t).1 (F.flow zX u).1+dist z.1 w.1 := by
      rw [dist_eq_norm,dist_eq_norm]
      calc
        _ = ‖((F.flow zX t).1-(F.flow zX u).1)-(z.1-w.1)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    rw [← he,← Real.dist_eq] at hn
    exact (hn.trans hh).trans (add_le_add htu (show dist z.1 w.1≤dist z w from le_max_left _ _))
  change dist t u≤(1/(1-(c:ℝ)))*dist z w
  rw [div_mul_eq_mul_div,one_mul]
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  nlinarith

lemma PhaseFlowOn.initial_primitive_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    ContinuousOn (fun z : Phase=>
      retardedPrimitive (branchTime F.flow zX z T 0)
        (velocity (F.flow zX (branchTime F.flow zX z T 0)).2)
        (velocity z.2) (branchDirection F.flow zX z T 0))
      (initialClosedCone F.flow zX T ∩ {z : Phase | z.1≠zX.1}) := by
  let A := initialClosedCone F.flow zX T ∩ {z : Phase | z.1≠zX.1}
  let τ := fun z=>branchTime F.flow zX z T 0
  have hm : ∀ z∈A,0∈closedBranchDomain F.flow zX z T := fun z hz=>
    F.initial_closed_branch_mem hT zX z hz.1
  have htm : MapsTo τ A (Icc 0 T) := fun z hz=>(F.branch_spec_closed zX z (hm z hz)).1
  have hne : ∀ z∈A,(F.flow zX 0).1≠(F.flow z 0).1 := by
    intro z hz
    simpa only [F.initial] using Ne.symm hz.2
  have hpos : ∀ z∈A,τ z≠0 := by
    intro z hz
    have hh := F.branch_radius_pos_closed zX z (hm z hz) (hne z hz)
    simpa only [sub_zero] using hh.ne'
  have ht : ContinuousOn τ A := by
    obtain ⟨C,hC⟩ := F.initial_branch_lipschitz hT zX
    exact hC.continuousOn.mono inter_subset_left
  have hX := (F.continuousOn_time zX).comp ht htm
  have hn : ContinuousOn (fun z=>branchDirection F.flow zX z T 0) A := by
    convert (ht.inv₀ hpos).smul (hX.fst.sub continuous_fst.continuousOn) using 1
    funext z
    simp only [branchDirection,sub_zero,F.initial,τ,Function.comp_apply]
    rfl
  have ha := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hX.snd
  have hu : ContinuousOn (fun z : Phase=>velocity z.2) A :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn continuous_snd.continuousOn
  have hn1 : ∀ z∈A,‖branchDirection F.flow zX z T 0‖=1 := fun z hz=>
    F.branchDirection_norm_closed zX z (hm z hz) (hne z hz)
  exact continuousOn_retardedPrimitive_space ht ha hu hn hpos
    (fun z hz=>(cone_denom_pos z.2 _ (hn1 z hz)).ne')
    (fun z hz=>(cone_denom_pos (F.flow zX (τ z)).2 _ (hn1 z hz)).ne')

lemma PhaseFlowOn.initial_primitive_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    Measurable ((initialClosedCone F.flow zX T ∩ {z : Phase | z.1≠zX.1}).indicator
      (fun z : Phase=>retardedPrimitive (branchTime F.flow zX z T 0)
        (velocity (F.flow zX (branchTime F.flow zX z T 0)).2)
        (velocity z.2) (branchDirection F.flow zX z T 0))) := by
  classical
  let A := initialClosedCone F.flow zX T ∩ {z : Phase | z.1≠zX.1}
  have h₁ : IsClosed (initialClosedCone F.flow zX T) :=
    isClosed_le ((continuous_const.sub continuous_fst).norm) continuous_const
  have h₂ : IsOpen {z : Phase | z.1≠zX.1} := (isClosed_eq continuous_fst continuous_const).isOpen_compl
  have hA : MeasurableSet A := h₁.measurableSet.inter h₂.measurableSet
  have h := (F.initial_primitive_continuousOn hT zX).measurable_piecewise
    (continuousOn_const (c:=(0:Vec))) hA
  convert h using 1
  funext z
  by_cases hz : z∈A <;> simp [A,Set.piecewise,Set.indicator] at hz ⊢
end RVM

end

end OAI
