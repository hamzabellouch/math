import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.GlobalODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} (t₀ : Icc a b) (f : ℝ → E → E)

abbrev Curve := C(Icc a b,E)

def extend (α : Curve (a:=a) (b:=b) (E:=E)) (t : ℝ) : E :=
  α (projIcc a b (le_trans t₀.2.1 t₀.2.2) t)

omit [NormedSpace ℝ E] in
lemma extend_of_mem (α : Curve (a:=a) (b:=b) (E:=E)) {t : ℝ} (ht : t∈Icc a b) :
    extend t₀ α t=α ⟨t,ht⟩ := by simp [extend,projIcc_of_mem _ ht]

omit [NormedSpace ℝ E] in
lemma extend_continuous (α : Curve (a:=a) (b:=b) (E:=E)) : Continuous (extend t₀ α) :=
  α.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] in
lemma continuous_comp (hf : Continuous (uncurry f)) (α : Curve (a:=a) (b:=b) (E:=E)) :
    Continuous (fun t => f t (extend t₀ α t)) :=
  hf.comp (continuous_id.prodMk (extend_continuous t₀ α))

def next (hf : Continuous (uncurry f)) (x : E) (α : Curve (a:=a) (b:=b) (E:=E)) :
    Curve (a:=a) (b:=b) (E:=E) where
  toFun t := x+∫ τ in (t₀:ℝ)..(t:ℝ),f τ (extend t₀ α τ)
  continuous_toFun := (continuous_const.add
    (intervalIntegral.continuous_primitive
      (fun _ _ => (continuous_comp t₀ f hf α).intervalIntegrable _ _) t₀)).comp continuous_subtype_val

lemma next_apply (hf : Continuous (uncurry f)) (x : E)
    (α : Curve (a:=a) (b:=b) (E:=E)) (t : Icc a b) :
    next t₀ f hf x α t=x+∫ τ in (t₀:ℝ)..(t:ℝ),f τ (extend t₀ α τ) := rfl

variable {f} (hf : Continuous (uncurry f)) {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
include hf hL

lemma iterate_dist_point (x : E) (α β : Curve (a:=a) (b:=b) (E:=E)) (n : ℕ) (t : Icc a b) :
    dist ((next t₀ f hf x)^[n] α t) ((next t₀ f hf x)^[n] β t) ≤
      ((K:ℝ)*|(t:ℝ)-(t₀:ℝ)|)^n/(n.factorial:ℝ)*dist α β := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f:=α) (g:=β) t
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',dist_eq_norm,next_apply,next_apply,
      add_sub_add_left_eq_sub,←intervalIntegral.integral_sub
        ((continuous_comp t₀ f hf _).intervalIntegrable _ _)
        ((continuous_comp t₀ f hf _).intervalIntegrable _ _)]
    calc
      _ ≤ ∫ τ in uIoc (t₀:ℝ) (t:ℝ), (K:ℝ)^(n+1)*|τ-(t₀:ℝ)|^n/(n.factorial:ℝ)*dist α β := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le (Continuous.integrableOn_uIoc (by fun_prop))
        apply ae_restrict_mem measurableSet_Ioc |>.mono
        intro s hs
        have hs' : s∈Icc a b := (uIoc_subset_uIcc.trans (uIcc_subset_Icc t₀.2 t.2)) hs
        rw [←dist_eq_norm,extend_of_mem _ _ hs',extend_of_mem _ _ hs']
        calc
          _ ≤ (K:ℝ)*dist ((next t₀ f hf x)^[n] α ⟨s,hs'⟩) ((next t₀ f hf x)^[n] β ⟨s,hs'⟩) :=
            (hL s hs').dist_le_mul _ _
          _ ≤ _ := by
            rw [pow_succ',mul_assoc,mul_div_assoc,mul_assoc]
            gcongr
            simpa only [←mul_pow] using ih ⟨s,hs'⟩
      _ ≤ ((K:ℝ)*|(t:ℝ)-(t₀:ℝ)|)^(n+1)/((n+1).factorial:ℝ)*dist α β := by
        apply le_of_abs_le
        rw [←intervalIntegral.abs_intervalIntegral_eq,intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div,intervalIntegral.integral_const_mul,abs_mul,abs_div,
          abs_mul,intervalIntegral.abs_intervalIntegral_eq,integral_pow_abs_sub_uIoc,abs_div,
          abs_pow,abs_pow,abs_dist,NNReal.abs_eq,abs_abs,mul_div,div_div,←abs_mul,
          ←Nat.cast_succ,←Nat.cast_mul,←Nat.factorial_succ,Nat.abs_cast,←mul_pow]

lemma iterate_dist (x : E) (α β : Curve (a:=a) (b:=b) (E:=E)) (n : ℕ) :
    dist ((next t₀ f hf x)^[n] α) ((next t₀ f hf x)^[n] β) ≤
      ((K:ℝ)*max (b-(t₀:ℝ)) ((t₀:ℝ)-a))^n/(n.factorial:ℝ)*dist α β := by
  have hmax : 0 ≤ max (b-(t₀:ℝ)) ((t₀:ℝ)-a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  apply (iterate_dist_point t₀ hf hL x α β n t).trans
  gcongr
  exact abs_sub_le_max_sub t.2.1 t.2.2 _

lemma contracting_iterate : ∃ n : ℕ, ∃ C : ℝ≥0, ∀ x : E,
    ContractingWith C (next t₀ f hf x)^[n] := by
  obtain ⟨n,hn⟩ := (FloorSemiring.tendsto_pow_div_factorial_atTop
    ((K:ℝ)*max (b-(t₀:ℝ)) ((t₀:ℝ)-a))).eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hmax : 0 ≤ max (b-(t₀:ℝ)) ((t₀:ℝ)-a) := le_max_of_le_left (sub_nonneg.mpr t₀.2.2)
  refine ⟨n,⟨_,by positivity⟩,fun x => ⟨hn,?_⟩⟩
  exact LipschitzWith.of_dist_le_mul fun α β => iterate_dist t₀ hf hL x α β n

theorem exists_curve [CompleteSpace E] (x : E) :
    ∃ α : ℝ → E, Continuous α ∧ α t₀=x ∧
      ∀ t∈Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t := by
  obtain ⟨n,C,hC⟩ := contracting_iterate t₀ hf hL
  let α : Curve (a:=a) (b:=b) (E:=E) := (hC x).fixedPoint _
  have hα : IsFixedPt (next t₀ f hf x) α := (hC x).isFixedPt_fixedPoint_iterate
  have he (t : ℝ) (ht : t∈Icc a b) : extend t₀ α t=ODE.picard f t₀ x (extend t₀ α) t := by
    rw [extend_of_mem _ _ ht]
    exact (congrArg (fun g : Curve (a:=a) (b:=b) (E:=E) => g ⟨t,ht⟩) hα).symm
  refine ⟨extend t₀ α,extend_continuous t₀ α,?_,fun t ht => ?_⟩
  · rw [he t₀ t₀.2,ODE.picard_apply₀]
  · exact (ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn
      (extend_continuous t₀ α).continuousOn (fun _ _ => Set.mem_univ _) x ht).congr
        (fun s hs => he s hs) (he t ht)
end LogConcaveSampling.GlobalODE

namespace LogConcaveSampling.GlobalODE
open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E → E} {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

lemma right_deriv {α : ℝ → E}
    (hd : ∀ t∈Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (t : ℝ) (ht : t∈Ico a b) : HasDerivWithinAt α (f t (α t)) (Ici t) t := by
  apply (hd t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
  exact inter_mem (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr ht.1))
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2))

include hL in

theorem trajectory_dist_right {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t∈Icc a b,HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t∈Icc a b,HasDerivWithinAt β (f t (β t)) (Icc a b) t)
    (t : ℝ) (ht : t∈Icc a b) :
    dist (α t) (β t) ≤ dist (α a) (β a)*Real.exp ((K:ℝ)*(t-a)) := by
  exact dist_le_of_trajectories_ODE_of_mem (s:=fun _ => univ)
    (fun t ht => (hL t ⟨ht.1,ht.2.le⟩).lipschitzOnWith) hα
    (right_deriv hdα) (fun _ _ => mem_univ _) hβ (right_deriv hdβ)
    (fun _ _ => mem_univ _) le_rfl t ht

lemma left_deriv {α : ℝ → E}
    (hd : ∀ t∈Icc a b, HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (t : ℝ) (ht : t∈Ioc a b) : HasDerivWithinAt α (f t (α t)) (Iic t) t := by
  apply (hd t ⟨ht.1.le,ht.2⟩).mono_of_mem_nhdsWithin
  exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds ht.1))
    (Filter.mem_of_superset self_mem_nhdsWithin (Iic_subset_Iic.mpr ht.2))

include hL in
lemma trajectory_unique_left {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t∈Icc a b,HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t∈Icc a b,HasDerivWithinAt β (f t (β t)) (Icc a b) t)
    (he : α b=β b) : EqOn α β (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_left (s:=fun _ => univ)
    (fun t ht => (hL t ⟨ht.1.le,ht.2⟩).lipschitzOnWith) hα
      (left_deriv hdα) (fun _ _ => mem_univ _) hβ (left_deriv hdβ)
      (fun _ _ => mem_univ _) he

include hL in
lemma trajectory_unique_right {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t∈Icc a b,HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t∈Icc a b,HasDerivWithinAt β (f t (β t)) (Icc a b) t)
    (he : α a=β a) : EqOn α β (Icc a b) := by
  intro t ht
  have hh := trajectory_dist_right hL hα hdα hβ hdβ t ht
  rw [he,dist_self,zero_mul,dist_le_zero] at hh
  exact hh
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ → E → E} {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t))

include hL in
lemma trajectory_dist_left {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t∈Icc a b,HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t∈Icc a b,HasDerivWithinAt β (f t (β t)) (Icc a b) t)
    (t : ℝ) (ht : t∈Icc a b) :
    dist (α t) (β t) ≤ dist (α b) (β b)*Real.exp ((K:ℝ)*(b-t)) := by
  have hmap : MapsTo Neg.neg (Icc (-b) (-a)) (Icc a b) :=
    fun _ h => ⟨le_neg.mp h.2,neg_le.mp h.1⟩
  have hL' : ∀ t∈Icc (-b) (-a),LipschitzWith K (fun z => -f (-t) z) := by
    intro u hu
    exact (hL (-u) (hmap hu)).neg
  have hd {γ : ℝ → E}
      (hh : ∀ t∈Icc a b,HasDerivWithinAt γ (f t (γ t)) (Icc a b) t)
      (u : ℝ) (hu : u∈Icc (-b) (-a)) :
      HasDerivWithinAt (γ ∘ Neg.neg) (-f (-u) (γ (-u))) (Icc (-b) (-a)) u := by
    convert! HasFDerivWithinAt.comp_hasDerivWithinAt u (hh (-u) (hmap hu))
      (hasDerivAt_neg u).hasDerivWithinAt hmap using 1
    simp
  have hh := trajectory_dist_right hL' (hα.comp continuousOn_neg hmap) (hd hdα)
    (hβ.comp continuousOn_neg hmap) (hd hdβ) (-t) ⟨neg_le_neg ht.2,neg_le_neg ht.1⟩
  simpa only [Function.comp_apply,neg_neg,sub_neg_eq_add,neg_add_eq_sub] using hh

include hL in
lemma trajectory_dist {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b))
    (hdα : ∀ t∈Icc a b,HasDerivWithinAt α (f t (α t)) (Icc a b) t)
    (hβ : ContinuousOn β (Icc a b))
    (hdβ : ∀ t∈Icc a b,HasDerivWithinAt β (f t (β t)) (Icc a b) t)
    (s t : Icc a b) :
    dist (α t) (β t) ≤ dist (α s) (β s)*Real.exp ((K:ℝ)*|(t:ℝ)-(s:ℝ)|) := by
  by_cases hst : (s:ℝ)≤t
  · have hsub : Icc (s:ℝ) b ⊆ Icc a b := Icc_subset_Icc_left s.2.1
    have hh := trajectory_dist_right (fun u hu => hL u (hsub hu)) (hα.mono hsub)
      (fun u hu => (hdα u (hsub hu)).mono hsub) (hβ.mono hsub)
      (fun u hu => (hdβ u (hsub hu)).mono hsub) t ⟨hst,t.2.2⟩
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hh
  · have hts : (t:ℝ) ≤ s := (lt_of_not_ge hst).le
    have hsub : Icc a (s:ℝ) ⊆ Icc a b := Icc_subset_Icc_right s.2.2
    have hh := trajectory_dist_left (fun u hu => hL u (hsub hu)) (hα.mono hsub)
      (fun u hu => (hdα u (hsub hu)).mono hsub) (hβ.mono hsub)
      (fun u hu => (hdβ u (hsub hu)).mono hsub) t ⟨t.2.1,hts⟩
    simpa only [abs_of_nonpos (sub_nonpos.mpr hts),neg_sub] using hh

variable [CompleteSpace E] (hf : Continuous (uncurry f))

def flow (s : Icc a b) (x : E) : ℝ → E := (exists_curve s hf hL x).choose

lemma flow_continuous (s : Icc a b) (x : E) : Continuous (flow hL hf s x) :=
  (exists_curve s hf hL x).choose_spec.1

lemma flow_initial (s : Icc a b) (x : E) : flow hL hf s x s=x :=
  (exists_curve s hf hL x).choose_spec.2.1

lemma flow_deriv (s : Icc a b) (x : E) (t : ℝ) (ht : t∈Icc a b) :
    HasDerivWithinAt (flow hL hf s x) (f t (flow hL hf s x t)) (Icc a b) t :=
  (exists_curve s hf hL x).choose_spec.2.2 t ht

lemma flow_lipschitz (s t : Icc a b) :
    LipschitzWith ⟨Real.exp ((K:ℝ)*|(t:ℝ)-(s:ℝ)|), (Real.exp_pos _).le⟩
      (fun x => flow hL hf s x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := trajectory_dist hL (flow_continuous hL hf s x).continuousOn
    (flow_deriv hL hf s x) (flow_continuous hL hf s y).continuousOn
    (flow_deriv hL hf s y) s t
  rw [flow_initial,flow_initial,mul_comm] at hh
  exact hh

lemma flow_cocycle (s t u : Icc a b) (x : E) :
    flow hL hf t (flow hL hf s x t) u=flow hL hf s x u := by
  have hh := trajectory_dist hL
    (flow_continuous hL hf t (flow hL hf s x t)).continuousOn
    (flow_deriv hL hf t (flow hL hf s x t))
    (flow_continuous hL hf s x).continuousOn (flow_deriv hL hf s x) t u
  rw [flow_initial,dist_self,zero_mul,dist_le_zero] at hh
  exact hh

def flowHomeomorph (s t : Icc a b) : E ≃ₜ E where
  toFun x := flow hL hf s x t
  invFun y := flow hL hf t y s
  left_inv x := by dsimp; rw [flow_cocycle,flow_initial]
  right_inv y := by dsimp; rw [flow_cocycle,flow_initial]
  continuous_toFun := (flow_lipschitz hL hf s t).continuous
  continuous_invFun := (flow_lipschitz hL hf t s).continuous
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (s : Icc a b) {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    {K : ℝ≥0} (hK : ∀ t∈Icc a b,‖A t‖≤K)

omit [CompleteSpace E] in
include hK in
lemma linear_field_lipschitz (t : ℝ) (ht : t∈Icc a b) :
    LipschitzWith K (fun J : E →L[ℝ] E => (A t).comp J) := by
  apply LipschitzWith.of_dist_le_mul
  intro J L
  rw [dist_eq_norm,←ContinuousLinearMap.comp_sub,dist_eq_norm]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hK t ht) (norm_nonneg _))

def fundamental : ℝ → E →L[ℝ] E :=
  flow (linear_field_lipschitz hK) ((hA.comp continuous_fst).clm_comp continuous_snd) s (ContinuousLinearMap.id ℝ E)

lemma fundamental_continuous : Continuous (fundamental s hA hK) :=
  flow_continuous _ _ _ _

lemma fundamental_initial : fundamental s hA hK s=ContinuousLinearMap.id ℝ E :=
  flow_initial _ _ _ _

lemma fundamental_deriv (t : ℝ) (ht : t∈Icc a b) :
    HasDerivWithinAt (fundamental s hA hK) ((A t).comp (fundamental s hA hK t)) (Icc a b) t :=
  flow_deriv _ _ _ _ t ht

lemma fundamental_apply_deriv (v : E) (t : ℝ) (ht : t∈Icc a b) :
    HasDerivWithinAt (fun u => fundamental s hA hK u v)
      (A t (fundamental s hA hK t v)) (Icc a b) t := by
  simpa using (fundamental_deriv s hA hK t ht).clm_apply (hasDerivWithinAt_const t (Icc a b) v)

lemma fundamental_apply_initial (v : E) : fundamental s hA hK s v=v := by
  rw [fundamental_initial]; rfl

lemma fundamental_apply_bound (v : E) (t : Icc a b) :
    ‖fundamental s hA hK t v‖≤‖v‖*Real.exp ((K:ℝ)*|(t:ℝ)-(s:ℝ)|) := by
  have hL : ∀ t∈Icc a b,LipschitzWith K (fun v : E => A t v) := by
    intro t ht
    exact (A t).lipschitzWith.weaken (hK t ht)
  have hh := trajectory_dist hL
    ((fundamental_continuous s hA hK).clm_apply continuous_const).continuousOn
    (fundamental_apply_deriv s hA hK v)
    (continuousOn_const (c:=(0:E))) (fun t ht => by simpa using hasDerivWithinAt_const t (Icc a b) (0:E)) s t
  simpa [fundamental_apply_initial,dist_zero_right] using hh

lemma fundamental_norm_bound (t : Icc a b) :
    ‖fundamental s hA hK t‖≤Real.exp ((K:ℝ)*|(t:ℝ)-(s:ℝ)|) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  simpa only [mul_comm] using fundamental_apply_bound s hA hK v t
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {f : ℝ → E → E} {D : ℝ → E → E →L[ℝ] E}

lemma uniform_taylor_compact (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z) (a b R ε : ℝ) (hε : 0<ε) :
    ∃ δ>0,∀ t∈Icc a b,∀ x : E,‖x‖≤R → ∀ v : E,‖v‖<δ →
      ‖f t (x+v)-f t x-D t x v‖≤ε*‖v‖ := by
  let S : Set (ℝ × E) := Icc a b ×ˢ closedBall (0:E) (R+1)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hD.continuousOn) ε hε
  refine ⟨min 1 δ,lt_min zero_lt_one hδ,fun t ht x hx v hv => ?_⟩
  have hv1 : ‖v‖<1 := lt_of_lt_of_le hv (min_le_left _ _)
  have hvδ : ‖v‖<δ := lt_of_lt_of_le hv (min_le_right _ _)
  have hxin : (t,x)∈S := ⟨ht,by simpa [mem_closedBall,dist_zero_right] using (by linarith : ‖x‖≤R+1)⟩
  have hbound : ∀ z∈closedBall x ‖v‖,‖D t z-D t x‖≤ε := by
    intro z hz
    have hzx : ‖z-x‖≤‖v‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have hzin : (t,z)∈S := by
      refine ⟨ht,?_⟩
      simp only [mem_closedBall,dist_zero_right]
      have hn : ‖z‖≤‖z-x‖+‖x‖ := by simpa [add_comm] using norm_le_insert' z x
      linarith
    have hdist : dist (t,z) (t,x)<δ := by
      simp only [dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero]
      exact max_lt hδ (hzx.trans_lt hvδ)
    simpa only [dist_eq_norm,uncurry_apply_pair] using (hclose (t,z) hzin (t,x) hxin hdist).le
  have hm := (convex_closedBall x ‖v‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => ((hf t z).sub (D t x).hasFDerivAt).hasFDerivWithinAt)
    hbound (mem_closedBall_self (norm_nonneg v))
    (show x+v∈closedBall x ‖v‖ by simp [mem_closedBall,dist_eq_norm])
  have he : (f t (x+v)-D t x (x+v))-(f t x-D t x x)=
      f t (x+v)-f t x-D t x v := by rw [map_add]; abel
  simpa only [Pi.sub_apply,he,add_sub_cancel_left] using hm
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology

lemma gronwallBound_zero_linear (K ε t : ℝ) :
    gronwallBound 0 K ε t=ε*gronwallBound 0 K 1 t := by
  unfold gronwallBound
  split_ifs <;> ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ProperSpace E]
    {a b : ℝ} (hab : a≤b) {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

def flowSpatialCoefficient (x : E) (u : ℝ) : E →L[ℝ] E :=
  D u (flow hL hc ⟨a,le_rfl,hab⟩ x u)

omit [ProperSpace E] in
include hD in
lemma flowSpatialCoefficient_continuous (x : E) :
    Continuous (flowSpatialCoefficient hab hc hL (D:=D) x) :=
  hD.comp (continuous_id.prodMk (flow_continuous hL hc ⟨a,le_rfl,hab⟩ x))

omit [ProperSpace E] in
include hf in
lemma flowSpatialCoefficient_bound (x : E) (u : ℝ) (hu : u∈Icc a b) :
    ‖flowSpatialCoefficient hab hc hL (D:=D) x u‖≤K := by
  rw [show flowSpatialCoefficient hab hc hL (D:=D) x u =
      fderiv ℝ (f u) (flow hL hc ⟨a,le_rfl,hab⟩ x u) from (hf u _).fderiv.symm]
  exact norm_fderiv_le_of_lipschitz ℝ (hL u hu)

def flowLinearization (x : E) : ℝ → E →L[ℝ] E :=
  fundamental ⟨a,le_rfl,hab⟩ (flowSpatialCoefficient_continuous hab hc hL hD x)
    (flowSpatialCoefficient_bound hab hc hL hf x)

include hD hf in

theorem flow_hasFDerivAt_left (x : E) (t : Icc a b) :
    HasFDerivAt (fun z => flow hL hc ⟨a,le_rfl,hab⟩ z t)
      (flowLinearization hab hc hL hD hf x t) x := by
  let s : Icc a b := ⟨a,le_rfl,hab⟩
  let α (z : E) := flow hL hc s z
  let A (u : ℝ) := D u (α x u)
  have hA : Continuous A := hD.comp (continuous_id.prodMk (flow_continuous hL hc s x))
  have hK : ∀ u∈Icc a b,‖A u‖≤K := by
    intro u hu
    rw [show A u=fderiv ℝ (f u) (α x u) from (hf u (α x u)).fderiv.symm]
    exact norm_fderiv_le_of_lipschitz ℝ (hL u hu)
  let J := fundamental s hA hK
  change HasFDerivAt _ (J t) x
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro c hcpos
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (flow_continuous hL hc s x).continuousOn
  let B := Real.exp ((K:ℝ)*(b-a))
  have hB : 0<B := Real.exp_pos _
  let G := gronwallBound 0 (K:ℝ) 1 ((t:ℝ)-a)
  let ε := c/(B*(|G|+1))
  have hε : 0<ε := div_pos hcpos (mul_pos hB (by positivity))
  obtain ⟨δ,hδ,hT⟩ := uniform_taylor_compact hD hf a b R ε hε
  filter_upwards [Metric.ball_mem_nhds (0:E) (div_pos hδ hB)] with v hv
  have hvδ : ‖v‖<δ/B := by simpa only [mem_ball,dist_zero_right] using hv
  have hΔ (u : Icc a b) : ‖α (x+v) u-α x u‖≤B*‖v‖ := by
    have hh := (flow_lipschitz hL hc s u).dist_le_mul (x+v) x
    simp only [dist_eq_norm,add_sub_cancel_left] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by
        change |(u:ℝ)-a|≤b-a
        rw [abs_of_nonneg (sub_nonneg.mpr u.2.1)]
        linarith [u.2.2]) K.coe_nonneg)) (norm_nonneg v))
  let w (u : ℝ) := α (x+v) u-α x u-J u v
  let w' (u : ℝ) := f u (α (x+v) u)-f u (α x u)-A u (J u v)
  have hw : Continuous w := ((flow_continuous hL hc s (x+v)).sub
    (flow_continuous hL hc s x)).sub ((fundamental_continuous s hA hK).clm_apply continuous_const)
  have hwd (u : ℝ) (hu : u∈Icc a b) : HasDerivWithinAt w (w' u) (Icc a b) u :=
    ((flow_deriv hL hc s (x+v) u hu).sub (flow_deriv hL hc s x u hu)).sub
      (fundamental_apply_deriv s hA hK v u hu)
  have hw0 : w a=0 := by
    change flow hL hc s (x+v) s-flow hL hc s x s-fundamental s hA hK s v=0
    rw [flow_initial,flow_initial,fundamental_apply_initial]
    abel
  have hwb (u : ℝ) (hu : u∈Icc a b) : ‖w' u‖≤(K:ℝ)*‖w u‖+ε*B*‖v‖ := by
    let Δ := α (x+v) u-α x u
    have hsmall : ‖Δ‖<δ := (hΔ ⟨u,hu⟩).trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hB).mp hvδ)
    have he := hT u hu (α x u) (hR u hu) Δ hsmall
    have hid : α x u+Δ=α (x+v) u := by dsimp [Δ]; abel
    rw [hid] at he
    have heq : w' u=A u (w u)+(f u (α (x+v) u)-f u (α x u)-A u Δ) := by
      dsimp [w',w,Δ]
      simp only [map_sub]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (A u).le_of_opNorm_le (hK u hu) _
    · exact (he.trans (mul_le_mul_of_nonneg_left (hΔ ⟨u,hu⟩) hε.le)).trans_eq (by ring)
  have hwd' (u : ℝ) (hu : u∈Ico a b) : HasDerivWithinAt w (w' u) (Ici u) u := by
    apply (hwd u ⟨hu.1,hu.2.le⟩).mono_of_mem_nhdsWithin
    exact inter_mem (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr hu.1))
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hu.2))
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hw.continuousOn hwd'
    (by simp [hw0] : ‖w a‖≤(0:ℝ)) (fun u hu => hwb u ⟨hu.1,hu.2.le⟩) t t.2
  rw [gronwallBound_zero_linear] at hg
  change ‖w t‖≤c*‖v‖
  calc
    _ ≤ (ε*B*‖v‖)*G := hg
    _ ≤ (ε*B*‖v‖)*(|G|+1) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self G]) (by positivity)
    _ = c*‖v‖ := by dsimp [ε]; field_simp
include hD hf in
lemma flow_differentiable_left (x : E) (t : Icc a b) :
    DifferentiableAt ℝ (fun z => flow hL hc ⟨a,le_rfl,hab⟩ z t) x :=
  (flow_hasFDerivAt_left hab hc hL hD hf x t).differentiableAt
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} {f : ℝ → E → E} {K : ℝ≥0}
  (hL : ∀ t∈Icc a b,LipschitzWith K (f t)) (hc : Continuous (uncurry f))

lemma flow_joint_continuous (s : Icc a b) :
    Continuous (fun p : E × Icc a b => flow hL hc s p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith _
    ⟨Real.exp ((K:ℝ)*(b-a)),(Real.exp_pos _).le⟩
  · intro x
    exact (flow_continuous hL hc s x).comp continuous_subtype_val
  · intro t
    apply (flow_lipschitz hL hc s t).weaken
    change Real.exp _ ≤ Real.exp _
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
    rw [abs_le]
    constructor <;> linarith [s.2.1,s.2.2,t.2.1,t.2.2]

variable (hab : a≤b) {A B : ℝ → E →L[ℝ] E}
  (hA : Continuous A) (hB : Continuous B)
  (hKA : ∀ t∈Icc a b,‖A t‖≤K) (hKB : ∀ t∈Icc a b,‖B t‖≤K)

lemma fundamental_difference_bound {δ : ℝ} (hδ : 0≤δ)
    (hAB : ∀ t∈Icc a b,‖A t-B t‖≤δ) (t : Icc a b) :
    ‖fundamental ⟨a,le_rfl,hab⟩ hA hKA t-fundamental ⟨a,le_rfl,hab⟩ hB hKB t‖ ≤
      gronwallBound 0 (K:ℝ) (δ*Real.exp ((K:ℝ)*(b-a))) ((t:ℝ)-a) := by
  let s : Icc a b := ⟨a,le_rfl,hab⟩
  let J := fundamental s hA hKA
  let L := fundamental s hB hKB
  let w (u : ℝ) := J u-L u
  let w' (u : ℝ) := (A u).comp (J u)-(B u).comp (L u)
  have hd (u : ℝ) (hu : u∈Icc a b) : HasDerivWithinAt w (w' u) (Icc a b) u :=
    (fundamental_deriv s hA hKA u hu).sub (fundamental_deriv s hB hKB u hu)
  have hn (u : ℝ) (hu : u∈Icc a b) :
      ‖w' u‖≤(K:ℝ)*‖w u‖+δ*Real.exp ((K:ℝ)*(b-a)) := by
    have he : w' u=(A u).comp (w u)+(A u-B u).comp (L u) := by
      dsimp [w',w]
      simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp]
      abel
    rw [he]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hKA u hu) (norm_nonneg _))
    · apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      apply mul_le_mul (hAB u hu) _ (norm_nonneg _) hδ
      apply (fundamental_norm_bound s hB hKB ⟨u,hu⟩).trans
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
      change |u-a|≤b-a
      rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
      linarith [hu.2]
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    ((fundamental_continuous s hA hKA).sub (fundamental_continuous s hB hKB)).continuousOn
    (fun u hu => ?_) (by
      change ‖fundamental s hA hKA s-fundamental s hB hKB s‖≤0
      rw [fundamental_initial,fundamental_initial,sub_self,norm_zero]) (fun u hu => hn u ⟨hu.1,hu.2.le⟩) t t.2
  apply (hd u ⟨hu.1,hu.2.le⟩).mono_of_mem_nhdsWithin
  exact inter_mem (Filter.mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr hu.1))
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hu.2))
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : Type*} [TopologicalSpace X] {a b : ℝ} (hab : a≤b)
  {K : ℝ≥0} {A : X → ℝ → E →L[ℝ] E}
  (hA : ∀ x,Continuous (A x))
  (hK : ∀ x t,t∈Icc a b → ‖A x t‖≤K)
  (hpA : Continuous (fun p : X × Icc a b => A p.1 p.2))

include hpA in
lemma fundamental_parameter_continuous (t : Icc a b) :
    Continuous (fun x => fundamental ⟨a,le_rfl,hab⟩ (hA x) (hK x) t) := by
  let P (x : X) : C(Icc a b,E →L[ℝ] E) :=
    ⟨fun u => A x u,(hA x).comp continuous_subtype_val⟩
  have hP : Continuous P := ContinuousMap.continuous_of_continuous_uncurry P hpA
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let B := Real.exp ((K:ℝ)*(b-a))
  let G := gronwallBound 0 (K:ℝ) 1 ((t:ℝ)-a)
  have hC : 0<B*(|G|+1) := mul_pos (Real.exp_pos _) (by positivity)
  filter_upwards [((Metric.tendsto_nhds (u:=P) (a:=P x)).mp (hP.tendsto x)) (ε/(B*(|G|+1))) (div_pos hε hC)] with y hy
  have hh := fundamental_difference_bound hab (hA y) (hA x) (hK y) (hK x)
    (dist_nonneg (x:=P y) (y:=P x)) (fun u hu => by
      rw [←dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist (f:=P y) (g:=P x) ⟨u,hu⟩) t
  rw [gronwallBound_zero_linear] at hh
  rw [dist_eq_norm]
  calc
    _ ≤ (dist (P y) (P x)*B)*G := hh
    _ ≤ (dist (P y) (P x)*B)*(|G|+1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self G]) (mul_nonneg dist_nonneg (Real.exp_pos _).le)
    _ < ε := by
      rw [mul_assoc]
      exact (lt_div_iff₀ hC).mp hy
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] {a b : ℝ} (hab : a≤b)
    {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

omit [ProperSpace E] in
lemma flowLinearization_continuous_initial (t : Icc a b) :
    Continuous (fun x => flowLinearization hab hc hL hD hf x t) := by
  apply fundamental_parameter_continuous hab
    (flowSpatialCoefficient_continuous hab hc hL hD)
    (flowSpatialCoefficient_bound hab hc hL hf) _ t
  exact hD.comp ((continuous_subtype_val.comp continuous_snd).prodMk
    (flow_joint_continuous hL hc ⟨a,le_rfl,hab⟩))

include hD hf in

lemma flow_contDiff_one_left (t : Icc a b) :
    ContDiff ℝ 1 (fun x => flow hL hc ⟨a,le_rfl,hab⟩ x t) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => flowLinearization hab hc hL hD hf x t,
    flowLinearization_continuous_initial hab hc hL hD hf t,
    fun x => flow_hasFDerivAt_left hab hc hL hD hf x t⟩
end LogConcaveSampling.GlobalODE
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    {K : ℝ≥0} (hK : ∀ t∈Icc a b,‖A t‖≤K)

lemma fundamental_cocycle (s t u : Icc a b) (v : E) :
    fundamental t hA hK u (fundamental s hA hK t v)=fundamental s hA hK u v := by
  have hL : ∀ t∈Icc a b,LipschitzWith K (A t) := fun t ht =>
    (A t).lipschitzWith.weaken (by exact_mod_cast hK t ht)
  have hh := trajectory_dist hL
    ((fundamental_continuous t hA hK).clm_apply continuous_const).continuousOn
    (fundamental_apply_deriv t hA hK (fundamental s hA hK t v))
    ((fundamental_continuous s hA hK).clm_apply continuous_const).continuousOn
    (fundamental_apply_deriv s hA hK v) t u
  rw [fundamental_apply_initial,dist_self,zero_mul,dist_le_zero] at hh
  exact hh

def fundamentalEquiv (s t : Icc a b) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { (fundamental s hA hK t).toLinearMap with
      invFun := fundamental t hA hK s
      left_inv := fun v => by
        change fundamental t hA hK s (fundamental s hA hK t v)=v
        rw [fundamental_cocycle,fundamental_apply_initial]
      right_inv := fun v => by
        change fundamental s hA hK t (fundamental t hA hK s v)=v
        rw [fundamental_cocycle,fundamental_apply_initial] }
  continuous_toFun := (fundamental s hA hK t).continuous
  continuous_invFun := (fundamental t hA hK s).continuous

end LogConcaveSampling.GlobalODE

namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] {a b : ℝ} (hab : a≤b)
    {f : ℝ → E → E} (hc : Continuous (uncurry f))
    {K : ℝ≥0} (hL : ∀ t∈Icc a b,LipschitzWith K (f t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hf : ∀ t z,HasFDerivAt (f t) (D t z) z)

include hab hD hf in
lemma flow_contDiff_one_to_left (t : Icc a b) :
    ContDiff ℝ 1 (fun x => flow hL hc t x a) := by
  let H := flowHomeomorph hL hc ⟨a,le_rfl,hab⟩ t
  let J (x : E) := fundamentalEquiv
    (flowSpatialCoefficient_continuous hab hc hL hD x)
    (flowSpatialCoefficient_bound hab hc hL hf x) ⟨a,le_rfl,hab⟩ t
  have hJ (x : E) : HasFDerivAt H (J x : E →L[ℝ] E) x :=
    flow_hasFDerivAt_left hab hc hL hD hf x t
  exact H.contDiff_symm hJ (flow_contDiff_one_left hab hc hL hD hf t)

include hab hD hf in

theorem flow_contDiff_one (s t : Icc a b) :
    ContDiff ℝ 1 (fun x => flow hL hc s x t) := by
  have hh := (flow_contDiff_one_left hab hc hL hD hf t).comp
    (flow_contDiff_one_to_left hab hc hL hD hf s)
  convert! hh using 1
  funext x
  exact (flow_cocycle hL hc s ⟨a,le_rfl,hab⟩ t x).symm
end LogConcaveSampling.GlobalODE

end UpperProof
end
end
end

end OAI
