import Mathlib

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
abbrev Time := Icc (0:ℝ) 1
instance : Fact ((0:ℝ) ≤ 1) := ⟨zero_le_one⟩
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def extend (f : C(Time,F)) : C(ℝ,F) := ContinuousMap.IccExtendCM f
omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma extend_apply (f : C(Time,F)) (t : Time) : extend f t=f t := by
  exact ContinuousMap.IccExtendCM_of_mem t.property
omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma extend_norm_le (f : C(Time,F)) (t : ℝ) : ‖extend f t‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

lemma weighted_continuous (k : ℝ) (f : C(Time,F)) :
    Continuous (fun t : ℝ => Real.exp (-k*t) • ∫ s in (0:ℝ)..t, Real.exp (k*s) • extend f s) := by
  have hc : Continuous (fun s : ℝ => Real.exp (k*s) • extend f s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (extend f).continuous
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (intervalIntegral.differentiable_integral_of_continuous hc).continuous

def weighted (k : ℝ) (f : C(Time,F)) : C(Time,F) :=
  ⟨fun t => Real.exp (-k*(t:ℝ)) • ∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s,
    (weighted_continuous k f).comp continuous_subtype_val⟩

lemma integral_exp_mul (k t : ℝ) (hk : k ≠ 0) :
    ∫ s in (0:ℝ)..t, Real.exp (k*s)=(Real.exp (k*t)-1)/k := by
  have hd (s : ℝ) : HasDerivAt (fun s => Real.exp (k*s)/k) (Real.exp (k*s)) s := by
    convert ((Real.hasDerivAt_exp (k*s)).comp s ((hasDerivAt_id s).const_mul k)).div_const k using 1 <;> first | rfl | simp [hk]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 t)
  simpa only [mul_zero,Real.exp_zero,sub_div] using h

lemma weighted_bound (k : ℝ) (hk : 0<k) (f : C(Time,F)) : ‖weighted k f‖ ≤ k⁻¹*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (inv_nonneg.mpr hk.le) (norm_nonneg f))).mpr
  intro t
  change ‖Real.exp (-k*(t:ℝ)) • ∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have hb : ‖∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s‖ ≤
      ∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s)*‖f‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
    · exact Filter.Eventually.of_forall (fun s _ => by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (extend_norm_le f s) (Real.exp_pos _).le)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_mul_const,integral_exp_mul k _ hk.ne'] at hb
  calc
    _ ≤ Real.exp (-k*(t:ℝ))*(((Real.exp (k*(t:ℝ))-1)/k)*‖f‖) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = ((1-Real.exp (-k*(t:ℝ)))/k)*‖f‖ := by
      have he : Real.exp (-k*(t:ℝ))*Real.exp (k*(t:ℝ))=1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc
        _ = (Real.exp (-k*(t:ℝ))*(Real.exp (k*(t:ℝ))-1))/k*‖f‖ := by ring
        _ = _ := by rw [mul_sub,he,mul_one]
    _ ≤ k⁻¹*‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-k*(t:ℝ))]) hk.le

/-- The actual exponentially weighted integration operator on the time interval.
Its norm is at most 1/k; this supplies a uniform contraction for arbitrary bounded
linear ODE coefficients, without an assumed global flow theorem. -/
def weightedCLM (k : ℝ) (hk : 0<k) : C(Time,F) →L[ℝ] C(Time,F) :=
  LinearMap.mkContinuous
    ({ toFun := weighted k
       map_add' := fun f g => by
         ext t
         change Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • (extend f s+extend g s)) =
           Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s)+
           Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend g s)
         have hc (v : C(Time,F)) : Continuous (fun s : ℝ => Real.exp (k*s) • extend v s) :=
           (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul (extend v).continuous
         simp_rw [smul_add]
         rw [intervalIntegral.integral_add ((hc f).intervalIntegrable _ _) ((hc g).intervalIntegrable _ _),smul_add]
       map_smul' := fun c f => by
         ext t
         change Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • (c • extend f s)) =
           c • (Real.exp (-k*(t:ℝ)) • (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend f s))
         simp_rw [smul_comm (Real.exp (k*_)) c]
         rw [intervalIntegral.integral_smul,smul_comm]
 } : C(Time,F) →ₗ[ℝ] C(Time,F))
    k⁻¹ (fun f => weighted_bound k hk f)
lemma weightedCLM_apply (k : ℝ) (hk : 0<k) (f : C(Time,F)) : weightedCLM k hk f=weighted k f := rfl
lemma weightedCLM_norm (k : ℝ) (hk : 0<k) : ‖weightedCLM (F := F) k hk‖ ≤ k⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hk.le) (fun f => weighted_bound k hk f)

end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
def pointwise (b : C(Time,F →L[ℝ] F)) (f : C(Time,F)) : C(Time,F) :=
  ⟨fun t => b t (f t),b.continuous.clm_apply f.continuous⟩
omit [CompleteSpace F] in
lemma pointwise_bound (b : C(Time,F →L[ℝ] F)) (f : C(Time,F)) : ‖pointwise b f‖ ≤ ‖b‖*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg b) (norm_nonneg f))).mpr
  intro t
  exact (b t).le_opNorm (f t) |>.trans (mul_le_mul (b.norm_coe_le_norm t)
    (f.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))
omit [CompleteSpace F] in
def pointwiseLM : C(Time,F →L[ℝ] F) →ₗ[ℝ] (C(Time,F) →ₗ[ℝ] C(Time,F)) where
  toFun b :=
    { toFun := pointwise b
      map_add' := fun f g => by ext t; exact map_add (b t) (f t) (g t)
      map_smul' := fun c f => by ext t; exact map_smul (b t) c (f t) }
  map_add' b c := by ext f t; rfl
  map_smul' c b := by ext f t; rfl
omit [CompleteSpace F] in
def pointwiseCLM : C(Time,F →L[ℝ] F) →L[ℝ] (C(Time,F) →L[ℝ] C(Time,F)) :=
  LinearMap.mkContinuous₂ (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ)
    (pointwiseLM (F := F)) 1 (fun (b : C(Time,F →L[ℝ] F)) (f : C(Time,F)) => by
    change ‖pointwise b f‖ ≤ 1*‖b‖*‖f‖
    simpa only [one_mul] using pointwise_bound (F := F) b f)
omit [CompleteSpace F] in
lemma pointwiseCLM_apply (b : C(Time,F →L[ℝ] F)) (f : C(Time,F)) (t : Time) :
    pointwiseCLM b f t=b t (f t) := rfl
omit [CompleteSpace F] in
lemma pointwiseCLM_norm (b : C(Time,F →L[ℝ] F)) : ‖pointwiseCLM b‖ ≤ ‖b‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b) (pointwise_bound b)

omit [CompleteSpace F] in
def expScale (k : ℝ) : C(Time,F) →L[ℝ] C(Time,F) :=
  pointwiseCLM ⟨fun t => Real.exp (k*(t:ℝ)) • ContinuousLinearMap.id ℝ F,
    ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul continuous_const)⟩
omit [CompleteSpace F] in
lemma expScale_apply (k : ℝ) (f : C(Time,F)) (t : Time) :
    expScale k f t=Real.exp (k*(t:ℝ)) • f t := rfl

lemma volterra_unit (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F)) (hb : ‖b‖<k) :
    IsUnit (1-weightedCLM k hk*pointwiseCLM b) := by
  apply isUnit_one_sub_of_norm_lt_one (R := C(Time,F) →L[ℝ] C(Time,F))
  calc
    ‖weightedCLM k hk*pointwiseCLM b‖ ≤ ‖weightedCLM (F := F) k hk‖*‖pointwiseCLM b‖ := norm_mul_le (weightedCLM (F := F) k hk) (pointwiseCLM b)
    _ ≤ k⁻¹*‖b‖ := mul_le_mul (weightedCLM_norm k hk) (pointwiseCLM_norm b)
      (norm_nonneg (pointwiseCLM b)) (inv_nonneg.mpr hk.le)
    _ < 1 := by rw [mul_comm,← div_eq_mul_inv]; exact (div_lt_one hk).mpr hb

/-- Actual continuous evolution, defined by the invertible weighted Volterra
operator. The coefficient need only be continuous in time. -/
def evolution (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F)) (y : F) : C(Time,F) :=
  expScale k ((Ring.inverse ((1 : C(Time,F) →L[ℝ] C(Time,F))-weightedCLM k hk*pointwiseCLM b) : C(Time,F) →L[ℝ] C(Time,F))
    (expScale (-k) (ContinuousMap.const Time y)))

lemma evolution_integral (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F)) (hb : ‖b‖<k)
    (y : F) (t : Time) :
    evolution k hk b y t=y+∫ s in (0:ℝ)..(t:ℝ), extend b s (extend (evolution k hk b y) s) := by
  let q : C(Time,F) := expScale (-k) (ContinuousMap.const Time y)
  let w : C(Time,F) := (Ring.inverse ((1 : C(Time,F) →L[ℝ] C(Time,F))-weightedCLM k hk*pointwiseCLM b) : C(Time,F) →L[ℝ] C(Time,F)) q
  have hw : w-weightedCLM k hk (pointwiseCLM b w)=q := by
    have h := congrArg (fun L : C(Time,F) →L[ℝ] C(Time,F) => L q)
      (Ring.mul_inverse_cancel _ (volterra_unit k hk b hb))
    simpa only [mul_apply_eq_comp,sub_apply,one_apply_eq_self] using h
  have hwt := congrArg (fun f : C(Time,F) => f t) hw
  change w t-Real.exp (-k*(t:ℝ)) •
    (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend (pointwiseCLM b w) s)=
      Real.exp (-k*(t:ℝ)) • y at hwt
  have he : Real.exp (k*(t:ℝ))*Real.exp (-k*(t:ℝ))=1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hscaled := congrArg (fun z : F => Real.exp (k*(t:ℝ)) • z) hwt
  rw [smul_sub,smul_smul,he,one_smul,smul_smul,he,one_smul] at hscaled
  have hint : (∫ s in (0:ℝ)..(t:ℝ), Real.exp (k*s) • extend (pointwiseCLM b w) s)=
      ∫ s in (0:ℝ)..(t:ℝ), extend b s (extend (evolution k hk b y) s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsi : s∈Icc (0:ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hs
      exact ⟨hs.1,hs.2.trans t.property.2⟩
    have hs' : s=(⟨s,hsi⟩ : Time) := rfl
    change Real.exp (k*s) • extend (pointwiseCLM b w) s =
      extend b s (extend (evolution k hk b y) s)
    rw [hs',extend_apply,extend_apply,extend_apply,pointwiseCLM_apply]
    change Real.exp (k*s) • b ⟨s,hsi⟩ (w ⟨s,hsi⟩)=
      b ⟨s,hsi⟩ (Real.exp (k*s) • w ⟨s,hsi⟩)
    exact (map_smul (b ⟨s,hsi⟩) (Real.exp (k*s)) (w ⟨s,hsi⟩)).symm
  rw [hint] at hscaled
  change Real.exp (k*(t:ℝ)) • w t=_
  exact sub_eq_iff_eq_add.mp hscaled

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
/-- Strong smooth parameter dependence of the entire continuous trajectory. -/
theorem evolution_contDiffAt (k : ℝ) (hk : 0<k)
    (b : P → C(Time,F →L[ℝ] F)) (y : P → F) (p : P)
    (hb : ContDiffAt ℝ (⊤ : ℕ∞) b p) (hy : ContDiffAt ℝ (⊤ : ℕ∞) y p)
    (hsmall : ‖b p‖<k) : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => evolution k hk (b p) (y p)) p := by
  have hB : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => pointwiseCLM (b q)) p := by
    exact (ContinuousLinearMap.contDiff (E := C(Time,F →L[ℝ] F))
      (F := C(Time,F) →L[ℝ] C(Time,F)) (pointwiseCLM (F := F))).contDiffAt.comp p hb
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => (1 : C(Time,F) →L[ℝ] C(Time,F))-
      weightedCLM k hk*pointwiseCLM (b p)) p :=
    by
      apply ContDiffAt.sub contDiffAt_const
      exact ContDiffAt.mul (𝕜 := ℝ) (f := fun _ : P => weightedCLM (F := F) k hk)
        (g := fun q => pointwiseCLM (b q)) contDiffAt_const hB
  obtain ⟨a,ha⟩ := volterra_unit k hk (b p) hsmall
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) Ring.inverse
      ((1 : C(Time,F) →L[ℝ] C(Time,F))-weightedCLM k hk*pointwiseCLM (b p)) := by
    rw [← ha]
    exact contDiffAt_ringInverse (R := C(Time,F) →L[ℝ] C(Time,F)) ℝ a
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun p => expScale (-k) (ContinuousMap.const Time (y p))) p :=
    (expScale (F := F) (-k)).contDiff.contDiffAt.comp p ((ContinuousLinearMap.contDiff (E := F) (F := C(Time,F))
      (ContinuousLinearMap.const ℝ Time)).contDiffAt.comp p hy)
  have hic := hi.comp p hA
  exact (expScale (F := F) k).contDiff.contDiffAt.comp p (hic.clm_apply hq)
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Integral solutions are genuine classical solutions, including one-sided
endpoint derivatives. -/
lemma evolution_hasDerivWithinAt (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F))
    (hb : ‖b‖<k) (y : F) (t : Time) :
    HasDerivWithinAt (extend (evolution k hk b y)) (b t (evolution k hk b y t)) Time t := by
  let u := evolution k hk b y
  have hc : Continuous (fun s : ℝ => extend b s (extend u s)) :=
    (extend b).continuous.clm_apply (extend u).continuous
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 (t:ℝ))
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add y
  have he : ∀ s∈Time, y+(∫ r in (0:ℝ)..s, extend b r (extend u r))=extend u s := by
    intro s hs
    change _=extend u (⟨s,hs⟩ : Time)
    rw [extend_apply]
    exact (evolution_integral k hk b hb y ⟨s,hs⟩).symm
  have ht := h.hasDerivWithinAt.congr_of_mem (fun s hs => (he s hs).symm) t.property
  simpa only [extend_apply] using ht

lemma evolution_initial (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F))
    (hb : ‖b‖<k) (y : F) : evolution k hk b y ⟨0,by simp [Time]⟩=y := by
  simpa only [intervalIntegral.integral_same,add_zero] using
    evolution_integral k hk b hb y ⟨0,by simp [Time]⟩

omit [CompleteSpace F] in
/-- Uniqueness on the entire time interval, with no smallness hypothesis. -/
lemma linear_ode_unique (b : C(Time,F →L[ℝ] F)) (u v : C(Time,F))
    (hu : ∀ t : Time, HasDerivWithinAt (extend u) (b t (u t)) Time t)
    (hv : ∀ t : Time, HasDerivWithinAt (extend v) (b t (v t)) Time t)
    (hzero : u ⟨0,by simp [Time]⟩=v ⟨0,by simp [Time]⟩) : u=v := by
  have hLip (t : ℝ) : LipschitzWith ‖b‖₊ (extend b t) :=
    (extend b t).lipschitzWith.weaken (by exact_mod_cast extend_norm_le b t)
  have he := ODE_solution_unique_of_mem_Icc_right
    (v := fun t x => extend b t x) (s := fun _ => univ) (K := ‖b‖₊)
    (fun t _ => (hLip t).lipschitzOnWith) (extend u).continuous.continuousOn
    (fun t ht => by
      have h := (hu ⟨t,mem_Icc_of_Ico ht⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
      simpa only [extend_apply b ⟨t,mem_Icc_of_Ico ht⟩,
        extend_apply u ⟨t,mem_Icc_of_Ico ht⟩] using h)
    (fun _ _ => mem_univ _) (extend v).continuous.continuousOn
    (fun t ht => by
      have h := (hv ⟨t,mem_Icc_of_Ico ht⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
      simpa only [extend_apply b ⟨t,mem_Icc_of_Ico ht⟩,
        extend_apply v ⟨t,mem_Icc_of_Ico ht⟩] using h)
    (fun _ _ => mem_univ _) (by
      change extend u (⟨0,by simp [Time]⟩ : Time)=extend v (⟨0,by simp [Time]⟩ : Time)
      simpa only [extend_apply u ⟨0,by simp [Time]⟩,extend_apply v ⟨0,by simp [Time]⟩] using hzero)
  ext t
  have h := he t.property
  simpa only [extend_apply] using h

/-- A globally defined linear evolution, not restricted to small coefficients. -/
def flow (b : C(Time,F →L[ℝ] F)) (y : F) : C(Time,F) :=
  evolution (‖b‖+1) (by positivity) b y
lemma flow_hasDerivWithinAt (b : C(Time,F →L[ℝ] F)) (y : F) (t : Time) :
    HasDerivWithinAt (extend (flow b y)) (b t (flow b y t)) Time t :=
  evolution_hasDerivWithinAt _ _ b (by linarith) y t
lemma flow_initial (b : C(Time,F →L[ℝ] F)) (y : F) :
    flow b y ⟨0,by simp [Time]⟩=y := evolution_initial _ _ b (by linarith) y
lemma flow_eq_evolution (k : ℝ) (hk : 0<k) (b : C(Time,F →L[ℝ] F))
    (hb : ‖b‖<k) (y : F) : flow b y=evolution k hk b y := by
  apply linear_ode_unique b _ _ (flow_hasDerivWithinAt b y) (evolution_hasDerivWithinAt k hk b hb y)
  rw [flow_initial,evolution_initial k hk b hb y]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma evolution_contDiff (k : ℝ) (hk : 0<k)
    (b : P → C(Time,F →L[ℝ] F)) (y : P → F)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hy : ContDiff ℝ (⊤ : ℕ∞) y)
    (hsmall : ∀ p, ‖b p‖<k) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => evolution k hk (b p) (y p)) := by
  rw [contDiff_iff_contDiffAt]
  exact fun p => evolution_contDiffAt k hk b y p hb.contDiffAt hy.contDiffAt (hsmall p)
theorem flow_contDiff (b : P → C(Time,F →L[ℝ] F)) (y : P → F)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hy : ContDiff ℝ (⊤ : ℕ∞) y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => flow (b p) (y p)) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let k : ℝ := ‖b p‖+1
  have hk : 0<k := by dsimp [k]; positivity
  have hsmall : ‖b p‖<k := by dsimp [k]; linarith
  apply (evolution_contDiffAt k hk b y p hb.contDiffAt hy.contDiffAt hsmall).congr_of_eventuallyEq
  have hbc : ContinuousAt b p := hb.continuous.continuousAt
  have hn : ContinuousAt (fun q => ‖b q‖) p := ContinuousAt.norm (f := b) hbc
  filter_upwards [hn.eventually_lt_const hsmall] with q hq
  exact flow_eq_evolution k hk (b q) hq (y q)
end ElasticityODE

end
end
section
noncomputable section
open Set
namespace ElasticityODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
def leftCoeff (b : C(Time,R)) : C(Time,R →L[ℝ] R) :=
  ⟨fun t => ContinuousLinearMap.mul ℝ R (b t),
    (ContinuousLinearMap.mul ℝ R).continuous.comp b.continuous⟩
def rightCoeff (b : C(Time,R)) : C(Time,R →L[ℝ] R) :=
  ⟨fun t => (ContinuousLinearMap.mul ℝ R).flip (b t),
    (ContinuousLinearMap.mul ℝ R).flip.continuous.comp b.continuous⟩
def fundamental (b : C(Time,R)) : C(Time,R) := flow (leftCoeff b) 1
def reciprocal (b : C(Time,R)) : C(Time,R) := flow (-rightCoeff b) 1
lemma fundamental_deriv (b : C(Time,R)) (t : Time) :
    HasDerivWithinAt (extend (fundamental b)) (b t*fundamental b t) Time t :=
  flow_hasDerivWithinAt (leftCoeff b) 1 t
lemma reciprocal_deriv (b : C(Time,R)) (t : Time) :
    HasDerivWithinAt (extend (reciprocal b)) (-(reciprocal b t*b t)) Time t :=
  flow_hasDerivWithinAt (-rightCoeff b) 1 t
lemma fundamental_initial (b : C(Time,R)) : fundamental b ⟨0,by simp [Time]⟩=1 :=
  flow_initial (leftCoeff b) 1
lemma reciprocal_initial (b : C(Time,R)) : reciprocal b ⟨0,by simp [Time]⟩=1 :=
  flow_initial (-rightCoeff b) 1
lemma reciprocal_mul_fundamental (b : C(Time,R)) (t : Time) :
    reciprocal b t*fundamental b t=1 := by
  let f : ℝ → R := fun s => extend (reciprocal b) s*extend (fundamental b) s
  have hder (s : Time) : HasDerivWithinAt f 0 Time s := by
    have h := (reciprocal_deriv b s).mul (fundamental_deriv b s)
    simpa only [f,Pi.mul_def,extend_apply,neg_mul,mul_assoc,neg_add_cancel] using h
  have he := constant_of_has_deriv_right_zero
    ((extend (reciprocal b)).continuous.mul (extend (fundamental b)).continuous).continuousOn
    (fun s hs => (hder ⟨s,mem_Icc_of_Ico hs⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)) t t.property
  change f t=f (⟨0,by simp [Time]⟩ : Time) at he
  have hz : f (⟨0,by simp [Time]⟩ : Time)=1 := by
    change extend (reciprocal b) (⟨0,by simp [Time]⟩ : Time)*
      extend (fundamental b) (⟨0,by simp [Time]⟩ : Time)=1
    rw [extend_apply,extend_apply,reciprocal_initial,fundamental_initial,mul_one]
  have hh := he.trans hz
  simpa only [f,extend_apply] using hh
lemma fundamental_mul_reciprocal (b : C(Time,R)) (t : Time) :
    fundamental b t*reciprocal b t=1 := by
  let a := leftCoeff b-rightCoeff b
  let u := fundamental b*reciprocal b
  let v : C(Time,R) := ContinuousMap.const Time 1
  have hu (s : Time) : HasDerivWithinAt (extend u) (a s (u s)) Time s := by
    have h := (fundamental_deriv b s).mul (reciprocal_deriv b s)
    have hh : HasDerivWithinAt (fun x => extend (fundamental b) x*extend (reciprocal b) x)
        (b s*(fundamental b s*reciprocal b s)-(fundamental b s*reciprocal b s)*b s) Time s := by
      simpa only [Pi.mul_def,extend_apply,mul_neg,mul_assoc,sub_eq_add_neg] using h
    exact hh.congr_of_mem (fun x hx => by
      change extend u (⟨x,hx⟩ : Time)=_
      rw [extend_apply]
      change fundamental b ⟨x,hx⟩*reciprocal b ⟨x,hx⟩=_
      rw [← extend_apply (fundamental b) ⟨x,hx⟩,← extend_apply (reciprocal b) ⟨x,hx⟩]) s.property
  have hv (s : Time) : HasDerivWithinAt (extend v) (a s (v s)) Time s := by
    have h : a s (v s)=0 := by change b s*1-1*b s=0; simp
    rw [h]
    have hh : HasDerivWithinAt (fun _ : ℝ => (1:R)) 0 Time s := hasDerivWithinAt_const _ _ _
    exact hh.congr_of_mem (fun x hx => by
      change extend v (⟨x,hx⟩ : Time)=1
      rw [extend_apply]
      rfl) s.property
  have hi : u ⟨0,by simp [Time]⟩=v ⟨0,by simp [Time]⟩ := by
    change fundamental b ⟨0,by simp [Time]⟩*reciprocal b ⟨0,by simp [Time]⟩=1
    rw [fundamental_initial,reciprocal_initial,mul_one]
  exact congrArg (fun f : C(Time,R) => f t) (linear_ode_unique a u v hu hv hi)
theorem fundamental_isUnit (b : C(Time,R)) (t : Time) : IsUnit (fundamental b t) :=
  ⟨⟨fundamental b t,reciprocal b t,fundamental_mul_reciprocal b t,reciprocal_mul_fundamental b t⟩,rfl⟩
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
def integrate (f : C(Time,F)) : C(Time,F) :=
  ⟨fun t => ∫ s in (0:ℝ)..(t:ℝ), extend f s,
    (intervalIntegral.differentiable_integral_of_continuous (extend f).continuous).continuous.comp
      continuous_subtype_val⟩
lemma integrate_bound (f : C(Time,F)) : ‖integrate f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  change ‖∫ s in (0:ℝ)..(t:ℝ), extend f s‖ ≤ ‖f‖
  have h := intervalIntegral.norm_integral_le_of_norm_le t.property.1
    (Filter.Eventually.of_forall (fun s (_ : s ∈ Ioc (0:ℝ) (t:ℝ)) => extend_norm_le f s))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖f‖) volume 0 (t:ℝ))
  calc
    _ ≤ ∫ s in (0:ℝ)..(t:ℝ), ‖f‖ := h
    _ = (t:ℝ)*‖f‖ := by simp
    _ ≤ ‖f‖ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg f)

def integrateCLM : C(Time,F) →L[ℝ] C(Time,F) :=
  LinearMap.mkContinuous
    ({ toFun := integrate
       map_add' := fun f g => by
         ext t
         change (∫ s in (0:ℝ)..(t:ℝ), (extend f s+extend g s)) =
           (∫ s in (0:ℝ)..(t:ℝ), extend f s)+(∫ s in (0:ℝ)..(t:ℝ), extend g s)
         exact intervalIntegral.integral_add ((extend f).continuous.intervalIntegrable _ _)
           ((extend g).continuous.intervalIntegrable _ _)
       map_smul' := fun c f => by
         ext t
         exact intervalIntegral.integral_smul c (fun s => extend f s)
    } : C(Time,F) →ₗ[ℝ] C(Time,F)) 1 (fun f => by
      change ‖integrate f‖ ≤ 1*‖f‖
      simpa only [one_mul] using integrate_bound f)
lemma integrateCLM_apply (f : C(Time,F)) (t : Time) :
    integrateCLM f t=∫ s in (0:ℝ)..(t:ℝ), extend f s := rfl

lemma integral_curve_hasDerivWithinAt (u f : C(Time,F)) (y : F)
    (he : u=ContinuousMap.const Time y+integrateCLM f) (t : Time) :
    HasDerivWithinAt (extend u) (f t) Time t := by
  have hc := (extend f).continuous
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 (t:ℝ))
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add y
  apply (h.hasDerivWithinAt.congr_of_mem ?_ t.property).congr_deriv (extend_apply f t)
  intro s hs
  change extend u (⟨s,hs⟩ : Time)=_
  rw [extend_apply,he]
  rfl
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
lemma integral_family_variation (b : P → C(Time,F →L[ℝ] F)) (u : P → C(Time,F)) (y : P → F)
    (p : P) (b' : P →L[ℝ] C(Time,F →L[ℝ] F)) (u' : P →L[ℝ] C(Time,F)) (y' : P →L[ℝ] F)
    (hb : HasFDerivAt b b' p) (hu : HasFDerivAt u u' p) (hy : HasFDerivAt y y' p)
    (he : ∀ q, u q=ContinuousMap.const Time (y q)+integrateCLM (pointwiseCLM (b q) (u q))) (v : P) :
    u' v=ContinuousMap.const Time (y' v)+
      integrateCLM (pointwiseCLM (b p) (u' v)+pointwiseCLM (b' v) (u p)) := by
  have hB : HasFDerivAt (fun q => pointwiseCLM (b q))
      ((pointwiseCLM (F := F)).comp b') p := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (f := b) (g := pointwiseCLM (F := F))
      (f' := b') (g' := pointwiseCLM (F := F)) p
      (pointwiseCLM (F := F)).hasFDerivAt hb
  have hprod := hB.clm_apply hu
  have hI := (integrateCLM (F := F)).hasFDerivAt.comp p hprod
  have hyc := (ContinuousLinearMap.const ℝ Time : F →L[ℝ] C(Time,F)).hasFDerivAt.comp p hy
  have hall := (hyc.add hI).congr_of_eventuallyEq (Filter.Eventually.of_forall he)
  have hd := hu.unique hall
  have h := congrArg (fun L : P →L[ℝ] C(Time,F) => L v) hd
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply] at h
  exact h

lemma integral_family_variation_hasDerivWithinAt
    (b : P → C(Time,F →L[ℝ] F)) (u : P → C(Time,F)) (y : P → F)
    (p : P) (b' : P →L[ℝ] C(Time,F →L[ℝ] F)) (u' : P →L[ℝ] C(Time,F)) (y' : P →L[ℝ] F)
    (hb : HasFDerivAt b b' p) (hu : HasFDerivAt u u' p) (hy : HasFDerivAt y y' p)
    (he : ∀ q, u q=ContinuousMap.const Time (y q)+integrateCLM (pointwiseCLM (b q) (u q)))
    (v : P) (t : Time) :
    HasDerivWithinAt (extend (u' v)) (b p t (u' v t)+b' v t (u p t)) Time t := by
  have h := integral_curve_hasDerivWithinAt (u' v) _ (y' v)
    (integral_family_variation b u y p b' u' y' hb hu hy he v) t
  simpa only [ContinuousMap.add_apply,pointwiseCLM_apply] using h
end ElasticityODE

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace ElasticityODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
lemma flow_integral_curve (b : C(Time,F →L[ℝ] F)) (y : F) :
    flow b y=ContinuousMap.const Time y+integrateCLM (pointwiseCLM b (flow b y)) := by
  ext t
  have h := evolution_integral (‖b‖+1) (by positivity) b (by linarith) y t
  change flow b y t=y+∫ s in (0:ℝ)..(t:ℝ), extend b s (extend (flow b y) s) at h
  rw [h]
  rfl
variable {R P : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
def leftCoeffCLM : C(Time,R) →L[ℝ] C(Time,R →L[ℝ] R) :=
  (ContinuousLinearMap.mul ℝ R).compLeftContinuous ℝ Time
omit [CompleteSpace R] in
lemma leftCoeffCLM_eq (b : C(Time,R)) : leftCoeffCLM b=leftCoeff b := rfl
lemma fundamental_contDiff (b : P → C(Time,R)) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => fundamental (b p)) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (leftCoeffCLM (R := R)) :=
    ContinuousLinearMap.contDiff (E := C(Time,R)) (F := C(Time,R →L[ℝ] R)) _
  have hcomp := hL.comp hb
  have hcoeff : ContDiff ℝ (⊤ : ℕ∞) (fun p => leftCoeff (b p)) := by
    simpa only [Function.comp_def,leftCoeffCLM_eq] using hcomp
  exact flow_contDiff (fun p => leftCoeff (b p)) (fun _ => 1) hcoeff contDiff_const
lemma fundamental_variation_hasDerivWithinAt (b : P → C(Time,R))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p v : P) (t : Time) :
    HasDerivWithinAt (extend (fderiv ℝ (fun p => fundamental (b p)) p v))
      (b p t*(fderiv ℝ (fun p => fundamental (b p)) p v t)+
        fderiv ℝ b p v t*fundamental (b p) t) Time t := by
  have hL : HasFDerivAt (leftCoeffCLM (R := R)) (leftCoeffCLM (R := R)) (b p) :=
    ContinuousLinearMap.hasFDerivAt _
  have hc := HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := C(Time,R))
    (G := C(Time,R →L[ℝ] R)) (f := b) (g := leftCoeffCLM (R := R))
    (f' := fderiv ℝ b p) (g' := leftCoeffCLM (R := R)) p hL
    (hb.differentiable (by simp) p).hasFDerivAt
  have hb' : HasFDerivAt (fun q => leftCoeff (b q))
      ((leftCoeffCLM (R := R)).comp (fderiv ℝ b p)) p := by
    simpa only [Function.comp_def,leftCoeffCLM_eq] using hc
  have hu := ((fundamental_contDiff b hb).differentiable (by simp) p).hasFDerivAt
  have hy : HasFDerivAt (fun _ : P => (1:R)) 0 p := hasFDerivAt_const (𝕜 := ℝ) _ _
  exact integral_family_variation_hasDerivWithinAt (fun q => leftCoeff (b q))
    (fun q => fundamental (b q)) (fun _ => 1) p _ _ _ hb' hu hy
    (fun q => flow_integral_curve (leftCoeff (b q)) 1) v t
lemma fundamental_variation_initial (b : P → C(Time,R))
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p v : P) :
    fderiv ℝ (fun p => fundamental (b p)) p v ⟨0,by simp [Time]⟩=0 := by
  let t : Time := ⟨0,by simp [Time]⟩
  have hu := ((fundamental_contDiff b hb).differentiable (by simp) p).hasFDerivAt
  have h := (ContinuousMap.evalCLM ℝ t : C(Time,R) →L[ℝ] R).hasFDerivAt.comp p hu
  have hh : (fun q => fundamental (b q) t)=(fun _ : P => (1:R)) :=
    funext (fun q => fundamental_initial (b q))
  change HasFDerivAt (fun q => fundamental (b q) t) _ p at h
  rw [hh] at h
  have he := h.unique (hasFDerivAt_const (1:R) p)
  exact congrArg (fun L : P →L[ℝ] R => L v) he
end ElasticityODE

end
end

end OAI
