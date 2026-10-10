import OAI.Geometry.HarmonicGrowth.Variation

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open Set
/-- Positive scalar initial value cannot cross zero: the equation itself
makes y*y' nonnegative and y² nondecreasing. -/
lemma scalar_value_positive {A p y v : ℝ → ℝ} (hp : Continuous p)
    (hA : ∀ t,0 ≤ t → 0 ≤ A t)
    (hy : ∀ t,HasDerivAt y (v t) t)
    (hv : ∀ t,HasDerivAt v (A t*y t-p t*v t) t)
    (hy0 : 0 < y 0) (hv0 : 0 ≤ v 0) {t : ℝ} (ht : 0 ≤ t) :
    y 0 ≤ y t ∧ 0 < y t := by
  have hpair : ∀ t,0 ≤ t → 0 ≤ y t*v t := by
    intro s hs
    apply integrating_factor_nonnegative p (fun t => y t*v t)
      (fun t => v t*v t+y t*(A t*y t-p t*v t)) hp
      (fun t => (hy t).mul (hv t)) (mul_nonneg hy0.le hv0) _ hs
    intro u hu
    have h := mul_nonneg (hA u hu) (sq_nonneg (y u))
    nlinarith [sq_nonneg (v u)]
  have hd (t : ℝ) : HasDerivAt (fun s => y s^2) (2*y t*v t) t := by
    simpa using (hy t).fun_pow 2
  have hm : MonotoneOn (fun s => y s^2) (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.2 (fun t => (hd t).continuousAt)).continuousOn
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t ht => by have h := hpair t (interior_subset ht);nlinarith)
  have hsq (s : ℝ) (hs : 0 ≤ s) : y 0^2 ≤ y s^2 :=
    hm (by simp) hs hs
  have hpos : 0 < y t := by
    by_contra hn
    have hc : ContinuousOn y (Icc 0 t) := (continuous_iff_continuousAt.2 (fun s => (hy s).continuousAt)).continuousOn
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc' ht hc
      (show (0:ℝ) ∈ Icc (y t) (y 0) from ⟨le_of_not_gt hn,hy0.le⟩)
    have h := hsq s hs.1
    rw [he] at h
    nlinarith
  exact ⟨by have h := hsq t ht;nlinarith,hpos⟩

/-- Generic initial data for the actual scalar second-order propagator. -/
def scalarPhase (A p : ℝ → ℝ) (a b t : ℝ) : ℝ×ℝ :=
  flow (block (fun t => ContinuousLinearMap.mul ℝ ℝ (A t)) p) (a,b) t

def scalarU (A p : ℝ → ℝ) (t : ℝ) : ℝ := (scalarPhase A p 1 0 t).1
def scalarV (A p : ℝ → ℝ) (t : ℝ) : ℝ := (scalarPhase A p 0 1 t).1

lemma scalarPhase_init (A p : ℝ → ℝ) (a b : ℝ) : scalarPhase A p a b 0=(a,b) :=
  flow_initial _ _

lemma scalarPhase_deriv {A p : ℝ → ℝ} (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp) (a b t : ℝ) :
    HasDerivAt (scalarPhase A p a b)
      ((scalarPhase A p a b t).2,
        A t*(scalarPhase A p a b t).1-p t*(scalarPhase A p a b t).2) t := by
  have hAc : Continuous (fun t => ContinuousLinearMap.mul ℝ ℝ (A t)) :=
    (ContinuousLinearMap.mul ℝ ℝ).continuous.comp hA
  have hAb (t : ℝ) : ‖ContinuousLinearMap.mul ℝ ℝ (A t)‖ ≤ MA :=
    (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℝ _).trans (by simpa only [Real.norm_eq_abs] using hAn t)
  exact flow_hasDerivAt (block_continuous hAc hp) (by positivity : 0 ≤ 1+MA+Mp)
    (block_bound hMA hMp hAb hpn) (a,b) t

lemma scalarPhase_value_deriv {A p : ℝ → ℝ} (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp) (a b t : ℝ) :
    HasDerivAt (fun s => (scalarPhase A p a b s).1) (scalarPhase A p a b t).2 t :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (scalarPhase_deriv hA hp hMA hMp hAn hpn a b t)

lemma scalarPhase_velocity_deriv {A p : ℝ → ℝ} (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp) (a b t : ℝ) :
    HasDerivAt (fun s => (scalarPhase A p a b s).2)
      (A t*(scalarPhase A p a b t).1-p t*(scalarPhase A p a b t).2) t :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (scalarPhase_deriv hA hp hMA hMp hAn hpn a b t)

lemma scalarPhase_linear {A p : ℝ → ℝ} (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp) (a b t : ℝ) :
    (scalarPhase A p a b t).1=a*scalarU A p t+b*scalarV A p t := by
  have hAc : Continuous (fun t => ContinuousLinearMap.mul ℝ ℝ (A t)) :=
    (ContinuousLinearMap.mul ℝ ℝ).continuous.comp hA
  have hAb (t : ℝ) : ‖ContinuousLinearMap.mul ℝ ℝ (A t)‖ ≤ MA :=
    (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℝ _).trans (by simpa only [Real.norm_eq_abs] using hAn t)
  have hinit : (a,b)=a • (1,0)+b • (0,1) := by ext <;> simp
  unfold scalarPhase scalarU scalarV
  rw [hinit,flow_add (block_continuous hAc hp) (by positivity : 0 ≤ 1+MA+Mp)
    (block_bound hMA hMp hAb hpn),
    flow_smul (block_continuous hAc hp) (by positivity : 0 ≤ 1+MA+Mp)
      (block_bound hMA hMp hAb hpn),
    flow_smul (block_continuous hAc hp) (by positivity : 0 ≤ 1+MA+Mp)
      (block_bound hMA hMp hAb hpn)]
  rfl

/-- Positivity is proved for the actual propagation columns, not imposed as
an assumption. The estimate is independent of the length of the leg. -/
theorem actual_scalar_leg_nonnegative {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ scalarU A p t ∧ 0 ≤ scalarV A p t := by
  have hpos (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
      a ≤ (scalarPhase A p a b t).1 ∧ 0 < (scalarPhase A p a b t).1 := by
    simpa only [scalarPhase_init] using scalar_value_positive hp hAp
      (scalarPhase_value_deriv hA hp hMA hMp hAn hpn a b)
      (scalarPhase_velocity_deriv hA hp hMA hMp hAn hpn a b)
      (by simpa only [scalarPhase_init] using ha)
      (by simpa only [scalarPhase_init] using hb) ht
  have hu : 1 ≤ scalarU A p t := (hpos 1 0 (by norm_num) (by norm_num)).1
  refine ⟨hu,?_⟩
  by_contra hn
  have hv : scalarV A p t < 0 := lt_of_not_ge hn
  let e := -scalarV A p t/(2*scalarU A p t)
  have hue : 0 < scalarU A p t := lt_of_lt_of_le (by norm_num) hu
  have he : 0 < e := div_pos (neg_pos.2 hv) (mul_pos (by norm_num) hue)
  have hh := (hpos e 1 he (by norm_num)).2
  rw [scalarPhase_linear hA hp hMA hMp hAn hpn] at hh
  have heval : e*scalarU A p t = -scalarV A p t/2 := by
    dsimp only [e]
    field_simp
  rw [heval,one_mul] at hh
  linarith

/-- The uniform K bound in manuscript (full-normalization), with U and V
produced by the actual scalar ODE. -/
theorem actual_scalar_normalizer_bounds {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {t θ : ℝ} (ht : 0 ≤ t) (hθ : 0 < θ) :
    0 < scalarU A p t+θ*scalarV A p t ∧
      0 ≤ scalarV A p t/(scalarU A p t+θ*scalarV A p t) ∧
      scalarV A p t/(scalarU A p t+θ*scalarV A p t) ≤ θ⁻¹ := by
  obtain ⟨hu,hv⟩ := actual_scalar_leg_nonnegative hA hp hMA hMp hAn hpn hAp ht
  have hd : 0 < scalarU A p t+θ*scalarV A p t := by positivity
  refine ⟨hd,div_nonneg hv hd.le,?_⟩
  apply (div_le_iff₀ hd).2
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hθ).2
  nlinarith

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open Set

lemma scalar_velocity_positive {A p y v : ℝ → ℝ} (hp : Continuous p)
    (hA : ∀ t,0 ≤ t → 0 ≤ A t)
    (hy : ∀ t,0 ≤ t → 0 ≤ y t)
    (hv : ∀ t,HasDerivAt v (A t*y t-p t*v t) t)
    (hv0 : 0 < v 0) {t : ℝ} (ht : 0 ≤ t) : 0 < v t := by
  let Q := fun s => ∫ u in (0:ℝ)..s,p u
  have hQ (s : ℝ) : HasDerivAt Q (p s) s :=
    intervalIntegral.integral_hasDerivAt_right (hp.intervalIntegrable 0 s)
      hp.stronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt
  have hd (s : ℝ) : HasDerivAt (fun u => v u*Real.exp (Q u))
      (A s*y s*Real.exp (Q s)) s := by
    apply ((hv s).mul (hQ s).exp).congr_deriv
    ring
  have hm : MonotoneOn (fun u => v u*Real.exp (Q u)) (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.2 (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
      (fun s hs => mul_nonneg (mul_nonneg (hA s (interior_subset hs))
        (hy s (interior_subset hs))) (Real.exp_pos _).le)
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) ht ht
  have hstart : 0 < v 0*Real.exp (Q 0) := mul_pos hv0 (Real.exp_pos _)
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 (hstart.trans_le h)

/-- Both diagonal propagation columns are genuinely STRICTLY positive at
positive leg times, as claimed in the manuscript. -/
theorem actual_scalar_leg_positive {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {t : ℝ} (ht : 0 < t) :
    0 < scalarU A p t ∧ 0 < scalarV A p t := by
  have hun := (actual_scalar_leg_nonnegative hA hp hMA hMp hAn hpn hAp ht.le).1
  refine ⟨by linarith,?_⟩
  have hv (s : ℝ) (hs : 0 ≤ s) : 0 < (scalarPhase A p 0 1 s).2 :=
    scalar_velocity_positive hp hAp
      (fun u hu => (actual_scalar_leg_nonnegative hA hp hMA hMp hAn hpn hAp hu).2)
      (scalarPhase_velocity_deriv hA hp hMA hMp hAn hpn 0 1)
      (by rw [scalarPhase_init];norm_num) hs
  have hm : StrictMonoOn (scalarV A p) (Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (continuous_iff_continuousAt.2 (fun s =>
        (scalarPhase_value_deriv hA hp hMA hMp hAn hpn 0 1 s).continuousAt)).continuousOn
      (fun s _ => (scalarPhase_value_deriv hA hp hMA hMp hAn hpn 0 1 s).hasDerivWithinAt)
      (fun s hs => hv s (interior_subset hs))
  have h := hm (by simp) ht.le ht
  simpa only [scalarV,scalarPhase_init] using h

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
/-- The exact parameter-free scalar baseline, produced from the convergent
Peano--Baker solution rather than assumed as a Riccati solution. -/
def scalarBaseline (A p : ℝ → ℝ) (θ t : ℝ) : ℝ :=
  (scalarPhase A p 1 θ t).2/(scalarPhase A p 1 θ t).1

lemma scalarBaseline_init (A p : ℝ → ℝ) (θ : ℝ) : scalarBaseline A p θ 0=θ := by
  simp only [scalarBaseline,scalarPhase_init,div_one]

lemma actual_scalar_baseline_positive {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ : ℝ} (hθ : 0 ≤ θ) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (scalarPhase A p 1 θ t).1 ∧ 0 ≤ scalarBaseline A p θ t := by
  have hy := scalarPhase_value_deriv hA hp hMA hMp hAn hpn 1 θ
  have hv := scalarPhase_velocity_deriv hA hp hMA hMp hAn hpn 1 θ
  have hpos (s : ℝ) (hs : 0 ≤ s) : 1 ≤ (scalarPhase A p 1 θ s).1 := by
    simpa only [scalarPhase_init] using
      (scalar_value_positive hp hAp hy hv (by simp [scalarPhase_init])
        (by simpa only [scalarPhase_init] using hθ) hs).1
  have hn : 0 ≤ (scalarPhase A p 1 θ t).2 := by
    apply integrating_factor_nonnegative p _ _ hp hv
      (by simpa only [scalarPhase_init] using hθ) _ ht
    intro s hs
    have h := mul_nonneg (hAp s hs) (le_trans (by norm_num : (0:ℝ) ≤ 1) (hpos s hs))
    nlinarith
  exact ⟨hpos t ht,div_nonneg hn (le_trans (by norm_num) (hpos t ht))⟩

lemma actual_scalar_baseline_deriv {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ : ℝ} (hθ : 0 ≤ θ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (scalarBaseline A p θ)
      (A t-p t*scalarBaseline A p θ t-(scalarBaseline A p θ t)^2) t := by
  have hn : (scalarPhase A p 1 θ t).1 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (actual_scalar_baseline_positive hA hp hMA hMp hAn hpn hAp hθ ht).1)
  apply ((scalarPhase_velocity_deriv hA hp hMA hMp hAn hpn 1 θ t).div
    (scalarPhase_value_deriv hA hp hMA hMp hAn hpn 1 θ t) hn).congr_deriv
  dsimp only [scalarBaseline]
  field_simp


/-- The exact baseline remains uniformly close to the limiting positive root.
The estimate has no pulse-duration factor, and is independent of all current
control parameters and of incoming matrix Riccati data. -/
theorem actual_scalar_baseline_close {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ γ M T : ℝ}
    (hθ : 0 ≤ θ) (hγ : 0 < γ) (hM : 0 ≤ M)
    (hpl : ∀ t ∈ Set.Icc 0 T,γ ≤ p t)
    (hF : ∀ t ∈ Set.Icc 0 T,|A t-p t*θ-θ^2| ≤ M) :
    ∀ t ∈ Set.Icc 0 T,|scalarBaseline A p θ t-θ| ≤ M/γ := by
  let v := scalarBaseline A p θ
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      HasDerivAt (fun s => v s-θ) ((A t-p t*θ-θ^2)-(p t+v t+θ)*(v t-θ)) t := by
    apply ((actual_scalar_baseline_deriv hA hp hMA hMp hAn hpn hAp hθ ht.1).sub_const θ).congr_deriv
    dsimp only [v]; ring
  have he (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
      ⟪v t-θ,(A t-p t*θ-θ^2)-(p t+v t+θ)*(v t-θ)⟫_ℝ ≤
        -γ*‖v t-θ‖^2+M*‖v t-θ‖ := by
    have hv := (actual_scalar_baseline_positive hA hp hMA hMp hAn hpn hAp hθ ht.1).2
    change 0 ≤ v t at hv
    have hc : γ ≤ p t+v t+θ := by linarith [hpl t ht]
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (v t-θ))
    have hf : (v t-θ)*(A t-p t*θ-θ^2) ≤ M*|v t-θ| := by
      calc
        _ ≤ |(v t-θ)*(A t-p t*θ-θ^2)| := le_abs_self _
        _ = |v t-θ| *|A t-p t*θ-θ^2| := abs_mul _ _
        _ ≤ |v t-θ| *M := mul_le_mul_of_nonneg_left (hF t ht) (abs_nonneg _)
        _ = _ := mul_comm _ _
    simp only [RCLike.inner_apply,conj_trivial,Real.norm_eq_abs,sq_abs]
    nlinarith
  have hz (t : ℝ) (ht : t ∈ Set.Icc 0 T) (h : v t-θ=0) :
      ‖(A t-p t*θ-θ^2)-(p t+v t+θ)*(v t-θ)‖ ≤ M := by
    simpa only [h,mul_zero,sub_zero,Real.norm_eq_abs] using hF t ht
  intro t ht
  have hh := dissipative_gronwall_on hd he hz t ht
  have hzero : v 0-θ=0 := by simp only [v,scalarBaseline_init,sub_self]
  rw [hzero,norm_zero,sub_zero] at hh
  have hb := damped_gronwall_bound (le_refl (0:ℝ)) hM hγ ht.1
  simpa only [zero_add,Real.norm_eq_abs] using hh.trans hb

end HarmonicCounterexample.LinearODE

end

end OAI
