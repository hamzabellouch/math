import Mathlib
import OAI.Probability.LogConcave.Dynamics.Truncated

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology NNReal

def variationalField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (p : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (f p.1,(fderiv ℝ f p.1).comp p.2)

lemma variationalField_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {n : ℕ} (hf : ContDiff ℝ ((n:WithTop ℕ∞)+1) f) :
    ContDiff ℝ (n:WithTop ℕ∞) (variationalField f) :=
  ((hf.of_le (by exact_mod_cast Nat.le_succ n)).comp contDiff_fst).prodMk
    (((hf.fderiv_right le_rfl).comp contDiff_fst).clm_comp contDiff_snd)

lemma truncated_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} {k : ℕ} (hf : ContDiff ℝ (k:WithTop ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (k:WithTop ℕ∞) (LinearGrowthODE.truncated f n) :=
  (((PoincareCutoff.bump (E:=E)).contDiff).comp (contDiff_id.const_smul _)).smul hf

theorem autonomous_flow_contDiff (n : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {f : E → E} (hf : ContDiff ℝ (n:WithTop ℕ∞) f) {K : ℝ≥0}
      (hL : LipschitzWith K f) {a b : ℝ} (hab : a≤b) (t : Icc a b),
      ContDiff ℝ (n:WithTop ℕ∞) (fun x => flow (fun _ _ => hL)
        (hf.continuous.comp continuous_snd) ⟨a,le_rfl,hab⟩ x t) := by
  induction n with
  | zero =>
    intro E _ _ _ f hf K hL a b hab t
    exact contDiff_zero.mpr (flow_lipschitz (fun _ _ => hL)
      (hf.continuous.comp continuous_snd) ⟨a,le_rfl,hab⟩ t).continuous
  | succ n ih =>
    intro E _ _ _ f hf K hL a b hab t
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos n)
    let hc : Continuous (uncurry (fun (_ : ℝ) => f)) := hf.continuous.comp continuous_snd
    let hD : Continuous (uncurry (fun (_ : ℝ) => fderiv ℝ f)) :=
      (hf1.continuous_fderiv (by norm_num)).comp continuous_snd
    let hd : ∀ (u : ℝ) (z : E),HasFDerivAt f (fderiv ℝ f z) z :=
      fun _ z => (hf1.differentiable (by norm_num) z).hasFDerivAt
    cases n with
    | zero =>
      exact flow_contDiff_one_left hab hc (fun _ _ => hL) hD hd t
    | succ m =>
      let J := flowLinearization hab hc (fun _ _ => hL) hD hd
      let X := fun x => flow (fun _ _ => hL) hc ⟨a,le_rfl,hab⟩ x
      have hXd (x : E) : HasFDerivAt (fun z => X z t) (J x t) x :=
        flow_hasFDerivAt_left hab hc (fun _ _ => hL) hD hd x t
      change ContDiff ℝ (((m+1:ℕ):WithTop ℕ∞)+1) (fun x => X x t)
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => J x t,?_,hXd⟩
      apply contDiff_iff_contDiffAt.mpr
      intro x₀
      let V := variationalField f
      have hV : ContDiff ℝ ((m+1:ℕ):WithTop ℕ∞) V := variationalField_smooth (by simpa using hf)
      have hV1 : ContDiff ℝ 1 V := hV.of_le (by exact_mod_cast Nat.succ_pos m)
      obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (flow_continuous (fun _ _ => hL) hc ⟨a,le_rfl,hab⟩ (0:E)).continuousOn
      let C := Real.exp ((K:ℝ)*(b-a))
      have hC : 0<C := Real.exp_pos _
      obtain ⟨N,hN⟩ := exists_nat_gt (max (A+C*(‖x₀‖+1)) C)
      let W := LinearGrowthODE.truncated V N
      have hW : ContDiff ℝ ((m+1:ℕ):WithTop ℕ∞) W := truncated_contDiff hV N
      obtain ⟨L,hWL⟩ := LinearGrowthODE.truncated_lipschitz hV1 N
      have hWc : Continuous (uncurry (fun (_ : ℝ) => W)) := hW.continuous.comp continuous_snd
      let Z (p : E × (E →L[ℝ] E)) := flow (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ p t
      have hZ : ContDiff ℝ ((m+1:ℕ):WithTop ℕ∞) Z := ih hW hWL hab t
      have hloc : (fun x => J x t) =ᶠ[𝓝 x₀]
          (fun x => (Z (x,ContinuousLinearMap.id ℝ E)).2) := by
        filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
        have hxn : ‖x‖≤‖x₀‖+1 := by
          have hh := norm_le_norm_add_norm_sub x₀ x
          rw [←dist_eq_norm, dist_comm] at hh
          linarith [Metric.mem_ball.mp hx]
        have hb (u : Icc a b) : ‖(X x u,J x u)‖≤(N:ℝ)+1 := by
          have hu : |(u:ℝ)-a|≤b-a := by
            rw [abs_of_nonneg (sub_nonneg.mpr u.2.1)]; linarith [u.2.2]
          have hex : Real.exp ((K:ℝ)*|(u:ℝ)-a|)≤C :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu K.coe_nonneg)
          have hX : ‖X x u‖≤A+C*(‖x₀‖+1) := by
            have hs := (flow_lipschitz (fun _ _ => hL) hc ⟨a,le_rfl,hab⟩ u).dist_le_mul x 0
            simp only [dist_zero_right] at hs
            have hn : ‖X x u‖≤‖X 0 u‖+dist (X x u) (X 0 u) := by
              simpa only [dist_eq_norm, norm_sub_rev] using
                (norm_le_norm_add_norm_sub (X 0 u) (X x u))
            exact hn.trans (add_le_add (hA u u.2) (hs.trans
              (mul_le_mul hex hxn (norm_nonneg _) hC.le)))
          have hJ : ‖J x u‖≤C :=
            (fundamental_norm_bound ⟨a,le_rfl,hab⟩
              (flowSpatialCoefficient_continuous hab hc (fun _ _ => hL) hD x)
              (flowSpatialCoefficient_bound hab hc (fun _ _ => hL) hd x) u).trans hex
          rw [Prod.norm_def]
          exact (max_le_max hX hJ).trans (by linarith)
        have he (u : ℝ) (hu : u∈Icc a b) : W (X x u,J x u)=V (X x u,J x u) :=
          LinearGrowthODE.truncated_eq (hb ⟨u,hu⟩)
        have hcP : Continuous (fun u => (X x u,J x u)) :=
          (flow_continuous (fun _ _ => hL) hc _ x).prodMk
            (fundamental_continuous ⟨a,le_rfl,hab⟩
              (flowSpatialCoefficient_continuous hab hc (fun _ _ => hL) hD x)
              (flowSpatialCoefficient_bound hab hc (fun _ _ => hL) hd x))
        have hdP (u : ℝ) (hu : u∈Icc a b) :
            HasDerivWithinAt (fun u => (X x u,J x u)) (W (X x u,J x u)) (Icc a b) u := by
          rw [he u hu]
          exact (flow_deriv (fun _ _ => hL) hc _ x u hu).prodMk
            (fundamental_deriv ⟨a,le_rfl,hab⟩
              (flowSpatialCoefficient_continuous hab hc (fun _ _ => hL) hD x)
              (flowSpatialCoefficient_bound hab hc (fun _ _ => hL) hd x) u hu)
        have hs := trajectory_dist (fun (_ : ℝ) _ => hWL) hcP.continuousOn hdP
          (flow_continuous (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ (x,ContinuousLinearMap.id ℝ E)).continuousOn
          (flow_deriv (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ (x,ContinuousLinearMap.id ℝ E))
          ⟨a,le_rfl,hab⟩ t
        have hi : (X x a,J x a)=(x,ContinuousLinearMap.id ℝ E) := by
          apply Prod.ext
          · exact flow_initial (fun _ _ => hL) hc ⟨a,le_rfl,hab⟩ x
          · exact fundamental_initial ⟨a,le_rfl,hab⟩
              (flowSpatialCoefficient_continuous hab hc (fun _ _ => hL) hD x)
              (flowSpatialCoefficient_bound hab hc (fun _ _ => hL) hd x)
        rw [show (⟨a,le_rfl,hab⟩ : Icc a b).val=a from rfl,hi,flow_initial,
          dist_self,zero_mul,dist_le_zero] at hs
        exact congrArg Prod.snd hs
      exact (hZ.comp (contDiff_id.prodMk contDiff_const)).snd.contDiffAt.congr_of_eventuallyEq hloc
end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology NNReal

theorem smooth_flow_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} {f : ℝ → E → E}
    (hf : ContDiff ℝ (n:WithTop ℕ∞) (uncurry f)) {K : ℝ≥0} {a b : ℝ}
    (hL : ∀t∈Icc a b,LipschitzWith K (f t)) (hab : a≤b) (t : Icc a b) :
    ContDiff ℝ (n:WithTop ℕ∞) (fun x => flow hL hf.continuous ⟨a,le_rfl,hab⟩ x t) := by
  cases n with
  | zero => exact contDiff_zero.mpr (flow_lipschitz hL hf.continuous _ t).continuous
  | succ n =>
    let V : ℝ × E → ℝ × E := fun p => (1,f p.1 p.2)
    have hV : ContDiff ℝ ((n+1:ℕ):WithTop ℕ∞) V := contDiff_const.prodMk hf
    have hV1 : ContDiff ℝ 1 V := hV.of_le (by exact_mod_cast Nat.succ_pos n)
    let X := fun x => flow hL hf.continuous ⟨a,le_rfl,hab⟩ x
    apply contDiff_iff_contDiffAt.mpr
    intro x₀
    obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((flow_continuous hL hf.continuous ⟨a,le_rfl,hab⟩ (0:E)).continuousOn :
        ContinuousOn (X 0) (Icc a b))
    let C := Real.exp ((K:ℝ)*(b-a))
    have hC : 0<C := Real.exp_pos _
    obtain ⟨N,hN⟩ := exists_nat_gt (max (max |a| |b|) (A+C*(‖x₀‖+1)))
    let W := LinearGrowthODE.truncated V N
    have hW : ContDiff ℝ ((n+1:ℕ):WithTop ℕ∞) W := truncated_contDiff hV N
    obtain ⟨L,hWL⟩ := LinearGrowthODE.truncated_lipschitz hV1 N
    have hWc : Continuous (uncurry (fun (_ : ℝ) => W)) := hW.continuous.comp continuous_snd
    let Z (p : ℝ × E) := flow (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ p t
    have hZ : ContDiff ℝ ((n+1:ℕ):WithTop ℕ∞) Z := autonomous_flow_contDiff _ hW hWL hab t
    have he : (fun x => X x t) =ᶠ[𝓝 x₀] (fun x => (Z (a,x)).2) := by
      filter_upwards [ball_mem_nhds x₀ zero_lt_one] with x hx
      have hxn : ‖x‖≤‖x₀‖+1 := by
        have hh := norm_le_norm_add_norm_sub x₀ x
        rw [←dist_eq_norm,dist_comm] at hh
        linarith [mem_ball.mp hx]
      have hb (u : Icc a b) : ‖((u:ℝ),X x u)‖≤(N:ℝ)+1 := by
        have hu : |(u:ℝ)-a|≤b-a := by
          rw [abs_of_nonneg (sub_nonneg.mpr u.2.1)]; linarith [u.2.2]
        have hex : Real.exp ((K:ℝ)*|(u:ℝ)-a|)≤C :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu K.coe_nonneg)
        have hX : ‖X x u‖≤A+C*(‖x₀‖+1) := by
          have hs := (flow_lipschitz hL hf.continuous ⟨a,le_rfl,hab⟩ u).dist_le_mul x 0
          simp only [dist_zero_right] at hs
          have hn : ‖X x u‖≤‖X 0 u‖+dist (X x u) (X 0 u) := by
            simpa only [dist_eq_norm,norm_sub_rev] using (norm_le_norm_add_norm_sub (X 0 u) (X x u))
          exact hn.trans (add_le_add (hA u u.2) (hs.trans
            (mul_le_mul hex hxn (norm_nonneg _) hC.le)))
        have hau : |(u:ℝ)| ≤ max |a| |b| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le a,le_max_left |a| |b|,u.2.1],
            by linarith [le_abs_self b,le_max_right |a| |b|,u.2.2]⟩
        rw [Prod.norm_def,Real.norm_eq_abs]
        exact (max_le_max hau hX).trans (by linarith)
      have heW (u : ℝ) (hu : u∈Icc a b) : W (u,X x u)=V (u,X x u) :=
        LinearGrowthODE.truncated_eq (hb ⟨u,hu⟩)
      have hcP : Continuous (fun u => (u,X x u)) :=
        continuous_id.prodMk (flow_continuous hL hf.continuous _ x)
      have hdP (u : ℝ) (hu : u∈Icc a b) :
          HasDerivWithinAt (fun u => (u,X x u)) (W (u,X x u)) (Icc a b) u := by
        rw [heW u hu]
        exact (hasDerivWithinAt_id u (Icc a b)).prodMk (flow_deriv hL hf.continuous _ x u hu)
      have hs := trajectory_dist (fun (_ : ℝ) _ => hWL) hcP.continuousOn hdP
        (flow_continuous (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ (a,x)).continuousOn
        (flow_deriv (fun _ _ => hWL) hWc ⟨a,le_rfl,hab⟩ (a,x)) ⟨a,le_rfl,hab⟩ t
      have hi : (a,X x a)=(a,x) := by rw [show X x a=x from flow_initial hL hf.continuous _ x]
      rw [show (⟨a,le_rfl,hab⟩ : Icc a b).val=a from rfl,hi,flow_initial,
        dist_self,zero_mul,dist_le_zero] at hs
      exact congrArg Prod.snd hs
    exact (hZ.comp (contDiff_const.prodMk contDiff_id)).snd.contDiffAt.congr_of_eventuallyEq he

lemma flow_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f g : ℝ → E → E} {K L : ℝ≥0}
    (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g))
    (hL : ∀t∈Icc a b,LipschitzWith K (f t))
    (hJ : ∀t∈Icc a b,LipschitzWith L (g t))
    (he : ∀t∈Icc a b,∀x,f t x=g t x) (s t : Icc a b) (x : E) :
    flow hL hf s x t=flow hJ hg s x t := by
  have hd (u : ℝ) (hu : u∈Icc a b) := flow_deriv hJ hg s x u hu
  have hh := trajectory_dist hL (flow_continuous hL hf s x).continuousOn
    (flow_deriv hL hf s x) (flow_continuous hJ hg s x).continuousOn
    (fun u hu => (he u hu _) ▸ flow_deriv hJ hg s x u hu) s t
  simpa only [flow_initial,dist_self,zero_mul,dist_le_zero] using hh
end LogConcaveSampling.GlobalODE

namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology NNReal

theorem smooth_flow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} {f : ℝ → E → E}
    (hf : ContDiff ℝ (n:WithTop ℕ∞) (uncurry f)) {K : ℝ≥0} {a b : ℝ}
    (hL : ∀t∈Icc a b,LipschitzWith K (f t)) (hab : a≤b) (s t : Icc a b) :
    ContDiff ℝ (n:WithTop ℕ∞) (fun x => flow hL hf.continuous s x t) := by
  cases n with
  | zero => exact contDiff_zero.mpr (flow_lipschitz hL hf.continuous s t).continuous
  | succ n =>
    have hf1 : ContDiff ℝ 1 (uncurry f) := hf.of_le (by exact_mod_cast Nat.succ_pos n)
    let D : ℝ → E → E →L[ℝ] E := fun u x =>
      (fderiv ℝ (uncurry f) (u,x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
    have hD : Continuous (uncurry D) :=
      (hf1.continuous_fderiv (by norm_num)).clm_comp continuous_const
    have hd (u : ℝ) (z : E) : HasFDerivAt (f u) (D u z) z := by
      exact ((hf1.differentiable (by norm_num) (u,z)).hasFDerivAt).comp z
        ((hasFDerivAt_const u z).prodMk (hasFDerivAt_id z))
    have hi (u : Icc a b) : ContDiff ℝ ((n+1:ℕ):WithTop ℕ∞)
        (fun x => flow hL hf.continuous u x a) := by
      let H := flowHomeomorph hL hf.continuous ⟨a,le_rfl,hab⟩ u
      let J (x : E) := fundamentalEquiv
        (flowSpatialCoefficient_continuous hab hf.continuous hL hD x)
        (flowSpatialCoefficient_bound hab hf.continuous hL hd x) ⟨a,le_rfl,hab⟩ u
      have hJ (x : E) : HasFDerivAt H (J x : E →L[ℝ] E) x :=
        flow_hasFDerivAt_left hab hf.continuous hL hD hd x u
      exact H.contDiff_symm hJ (smooth_flow_left hf hL hab u)
    have hh := (smooth_flow_left hf hL hab t).comp (hi s)
    convert! hh using 1
    funext x
    exact (flow_cocycle hL hf.continuous s ⟨a,le_rfl,hab⟩ t x).symm
end LogConcaveSampling.GlobalODE

end

end

end

end OAI
