import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ClosedBranchDomain

namespace OAI

noncomputable section

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

lemma absolutelyContinuousOnInterval_of_continuous_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g g' : ℝ → V} {a b : ℝ} (hab : a<b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t∈Ioo a b,HasDerivAt g (g' t) t) :
    AbsolutelyContinuousOnInterval g a b := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'
  let M : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hLip : LipschitzOnWith M g (Ioo a b) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun t ht=>(hd t ht).differentiableAt) _ (convex_Ioo a b)
    intro t ht
    rw [(hd t ht).deriv]
    exact_mod_cast (hC t (Ioo_subset_Icc_self ht)).trans (le_max_left C 0)
  have hc : ContinuousOn g (closure (Ioo a b)) := by simpa only [closure_Ioo hab.ne] using hg
  have hLc := LipschitzOnWith.closure hc hLip
  rw [closure_Ioo hab.ne,← uIcc_of_le hab.le] at hLc
  exact hLc.absolutelyContinuousOnInterval

lemma ac_weighted_vector_ibp_closed {ψ : ℝ → ℝ} {g g' : ℝ → Vec} {a b : ℝ}
    (hab : a≤b) (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t∈Ioo a b,HasDerivAt g (g' t) t) :
    ∫ t in a..b, ψ t • g' t =
      ψ b • g b - ψ a • g a - ∫ t in a..b, deriv ψ t • g t := by
  rcases hab.eq_or_lt with rfl|hab
  · simp
  have hgu : ContinuousOn g (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hg
  have hg'u : ContinuousOn g' (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hg'
  have h₁ : IntervalIntegrable (fun t=>ψ t • g' t) volume a b :=
    (hψ.continuousOn.smul hg'u).intervalIntegrable
  have h₂ : IntervalIntegrable (fun t=>deriv ψ t • g t) volume a b :=
    hψ.intervalIntegrable_deriv.smul_continuousOn hgu
  ext i
  rw [intervalIntegral_vec_apply h₁,PiLp.sub_apply,PiLp.sub_apply,
    PiLp.smul_apply,PiLp.smul_apply,intervalIntegral_vec_apply h₂]
  simp only [PiLp.smul_apply,smul_eq_mul]
  have hdi : ∀ t∈Ioo a b,HasDerivAt (fun r=>g r i) (g' t i) t := fun t ht=>
    (PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hgi : AbsolutelyContinuousOnInterval (fun t=>g t i) a b :=
    absolutelyContinuousOnInterval_of_continuous_derivative hab
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).continuous.comp_continuousOn hg)
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).continuous.comp_continuousOn hg') hdi
  have he : (∫ t in a..b,ψ t*g' t i)=∫ t in a..b,ψ t*deriv (fun r=>g r i) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have hti : t∈Ioo a b := by simpa only [uIoo_of_le hab.le] using ht
    exact congrArg (fun x=>ψ t*x) (hdi t hti).deriv.symm
  rw [he]
  exact hψ.integral_mul_deriv_eq_deriv_mul hgi

lemma ac_weighted_signed_ibp_closed {ψ : ℝ → ℝ} {P K R : ℝ → Vec}
    {W W' : ℝ → Vec →L[ℝ] Vec} {a b : ℝ} (hab : a≤b)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hP : ContinuousOn P (Icc a b)) (hW : ContinuousOn W (Icc a b))
    (hW' : ContinuousOn W' (Icc a b))
    (hK : ContinuousOn K (Icc a b)) (hR : ContinuousOn R (Icc a b))
    (hPd : ∀ t∈Ioo a b,HasDerivAt P (-K t+R t) t)
    (hWd : ∀ t∈Ioo a b,HasDerivAt W (W' t) t) :
    ∫ t in a..b,ψ t • W t (K t) =
      ψ a • W a (P a)-ψ b • W b (P b)+
      ∫ t in a..b,deriv ψ t • W t (P t)+ψ t • (W' t (P t)+W t (R t)) := by
  have hg : ContinuousOn (fun t=>W t (P t)) (Icc a b) := hW.clm_apply hP
  have hg' : ContinuousOn (fun t=>W' t (P t)+W t (-K t+R t)) (Icc a b) :=
    (hW'.clm_apply hP).add (hW.clm_apply (hK.neg.add hR))
  have h := ac_weighted_vector_ibp_closed hab hψ hg hg'
    (fun t ht=>(hWd t ht).clm_apply (hPd t ht))
  have hI₁ : IntervalIntegrable (fun t=>ψ t • W t (K t)) volume a b :=
    (hψ.continuousOn.smul (by simpa only [uIcc_of_le hab] using hW.clm_apply hK)).intervalIntegrable
  have hI₂ : IntervalIntegrable (fun t=>ψ t • (W' t (P t)+W t (R t))) volume a b :=
    (hψ.continuousOn.smul (by simpa only [uIcc_of_le hab] using (show ContinuousOn (fun t=>W' t (P t)+W t (R t)) (Icc a b) from (hW'.clm_apply hP).add (hW.clm_apply hR)))).intervalIntegrable
  have hI₃ : IntervalIntegrable (fun t=>deriv ψ t • W t (P t)) volume a b :=
    hψ.intervalIntegrable_deriv.smul_continuousOn (by simpa only [uIcc_of_le hab] using hg)
  have he : (fun t=>ψ t • (W' t (P t)+W t (-K t+R t))) =
      (fun t=>ψ t • (W' t (P t)+W t (R t))-ψ t • W t (K t)) := by
    funext t
    simp only [map_add,map_neg,smul_add,smul_neg]
    abel
  rw [he,intervalIntegral.integral_sub hI₂ hI₁] at h
  rw [intervalIntegral.integral_add hI₃ hI₂]
  have hh := congrArg (fun v=>(∫ t in a..b,ψ t • (W' t (P t)+W t (R t)))-v) h
  convert hh using 1 <;> abel

lemma PhaseFlowOn.actual_weighted_signed_identity_closed {s : Solution} {T b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX zY : Phase) (hb : b∈Icc 0 T)
    (he : b+‖(F.flow zX T).1-(F.flow zY b).1‖=T)
    (hne : ∀ σ∈Icc 0 T,(F.flow zX σ).1≠(F.flow zY σ).1)
    {ψ : ℝ→ℝ} {W W' : ℝ→Vec→L[ℝ]Vec}
    (hψ : AbsolutelyContinuousOnInterval ψ 0 b)
    (hW : ContinuousOn W (Icc 0 b)) (hW' : ContinuousOn W' (Icc 0 b))
    (hWd : ∀ σ∈Ioo 0 b,HasDerivAt W (W' σ) σ) :
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    ∫ σ in 0..b,ψ σ • W σ
      (signedForceKernel (r σ) (a σ) (u σ) (n σ) (phaseAcceleration s.E s.B F.flow zY σ)) =
      ψ 0 • W 0 (retardedPrimitive (r 0) (a 0) (u 0) (n 0))-
      ψ b • W b (retardedPrimitive (r b) (a b) (u b) (n b))+
      ∫ σ in 0..b,deriv ψ σ • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
        ψ σ • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ))+
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
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
  apply ac_weighted_signed_ibp_closed hb.1 hψ hP hW hW' hK hR _ hWd
  intro σ hσ
  simpa only [sub_eq_neg_add] using hder σ hσ

end RVM

end

end OAI
