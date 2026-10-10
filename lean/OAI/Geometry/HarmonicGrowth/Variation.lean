import OAI.Geometry.HarmonicGrowth.Damping

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open scoped InnerProductSpace Matrix.Norms.Frobenius
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

lemma actual_value_round_core {A : ℝ → E →L[ℝ] E} {p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p) {MA Mp : ℝ}
    (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,‖A t‖ ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    {l B : ℝ} (hAc : ∀ t ≤ 0,∀ x,A t x=(l*(l+B)) • x)
    (hpc : ∀ t ≤ 0,p t=B) {t : ℝ} (ht : t ≤ 0) :
    operatorValue A p l t=Real.exp (l*t) • (1 : E →L[ℝ] E) := by
  ext x
  simpa only [smul_apply,one_apply_eq_self,
    operatorValue_apply hA hp hMA hMp hAn hpn] using
    value_euclidean_tail hA hp hMA hMp hAn hpn hAc hpc x ht

/-- No hidden assumption of a globally invertible value evolution: positivity
proves invertibility forward, and the exact Euclidean tail proves it backward. -/
lemma actual_value_unit_all_time {A : ℝ → E →L[ℝ] E} {p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p) {MA Mp : ℝ}
    (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,‖A t‖ ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t x,0 ≤ inner ℝ x (A t x))
    {l B : ℝ} (hl : 0 < l) (hAc : ∀ t ≤ 0,∀ x,A t x=(l*(l+B)) • x)
    (hpc : ∀ t ≤ 0,p t=B) (t : ℝ) : IsUnit (operatorValue A p l t) := by
  rcases le_total 0 t with ht | ht
  · exact operatorValue_isUnit hA hp hMA hMp hAn hpn hAp hl ht
  · rw [actual_value_round_core hA hp hMA hMp hAn hpn hAc hpc ht]
    simpa using IsUnit.smul (Units.mk0 (Real.exp (l*t)) (Real.exp_ne_zero _))
      (isUnit_one : IsUnit (1 : E →L[ℝ] E))

/-- Uniform round reset for the ACTUAL center-regular Peano--Baker solution,
expressed in genuine orthonormal coordinates. Its incoming slope bound C is
an arbitrary history-independent barrier, not an assumed reset conclusion. -/
theorem actual_round_reset (basis : OrthonormalBasis ι ℝ E)
    {A : ℝ → E →L[ℝ] E} {p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p) {MA Mp : ℝ}
    (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,‖A t‖ ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t x,0 ≤ inner ℝ x (A t x))
    {l B : ℝ} (hl : 0 < l) (hAc : ∀ t ≤ 0,∀ x,A t x=(l*(l+B)) • x)
    (hpc : ∀ t ≤ 0,p t=B) {a b pmin θ M C : ℝ}
    (ha : 0 ≤ a) (hγ : 0 < pmin+θ) (hM : 0 ≤ M)
    (hpl : ∀ t ∈ Set.Icc a b,pmin ≤ p t)
    (hforce : ∀ t ∈ Set.Icc a b,
      ‖orthogonalMatrix basis (A t)-(p t*θ+θ^2) • (1 : Matrix ι ι ℝ)‖ ≤ M)
    (hinit : ‖orthogonalMatrix basis (slope A p l a)-θ • (1 : Matrix ι ι ℝ)‖ ≤ C) :
    ∀ t ∈ Set.Icc a b,
      ‖orthogonalMatrix basis (slope A p l t)-θ • (1 : Matrix ι ι ℝ)‖ ≤
        C*Real.exp (-(pmin+θ)*(t-a))+M/(pmin+θ) := by
  have hu := actual_value_unit_all_time hA hp hMA hMp hAn hpn hAp hl hAc hpc
  have hd (t : ℝ) := orthogonalMatrix_riccati_deriv basis
    (slope_deriv hA hp hMA hMp hAn hpn l t (hu t))
  have hpos (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι → ℝ) :
      (0:ℝ)*(∑ i,(v i)^2) ≤
        ∑ i,∑ j,v i*(orthogonalMatrix basis (slope A p l t)) i j*v j := by
    apply orthogonalMatrix_coercive
    intro x
    simpa only [zero_mul] using slope_nonnegative hA hp hMA hMp hAn hpn hAp hl
      (ha.trans ht.1) (hu t) x
  simpa only [add_zero] using round_reset_estimate (α := 0) (by simpa using hγ)
    hM hd hpl hpos hforce hinit

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Actual parameter-jet Peano–Baker terms. -/
def termD (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (x : E) (p : H) : ℕ → ℝ → H →L[ℝ] E
  | 0,_ => 0
  | n+1,t => ∫ s in (0:ℝ)..t,
      (A p s).comp (termD A A' x p n s) + (A' p s).flip (term (A p) x n s)

lemma termD_continuous (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hA' : ∀ p,Continuous (A' p))
    (x : E) (p : H) (n : ℕ) : Continuous (termD A A' x p n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun s => (A p s).comp (termD A A' x p n s) +
        (A' p s).flip (term (A p) x n s)) :=
      ((hA p).clm_comp ih).add (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp (hA' p)).clm_apply (term_continuous (hA p) x n))
    apply continuous_iff_continuousAt.2
    intro t
    exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt

lemma param_integrand_bound (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ p s,‖A p s‖ ≤ M) (hb' : ∀ p s,‖A' p s‖ ≤ M)
    (x : E) (n : ℕ) (p : H) (s : ℝ)
    (hd : ‖termD A A' x p n s‖ ≤ ‖x‖*(2*M)^n*|s|^n/(n.factorial:ℝ)) :
    ‖(A p s).comp (termD A A' x p n s) + (A' p s).flip (term (A p) x n s)‖ ≤
      (‖x‖*(2*M)^(n+1)/(n.factorial:ℝ))*|s|^n := by
  have ht := term_bound (hA p) (show 0 ≤ 2*M by positivity)
    (fun s => (hb p s).trans (by linarith)) x n s
  have hn : ‖(A' p s).flip‖=‖A' p s‖ := ContinuousLinearMap.opNorm_flip _
  calc
    _ ≤ ‖(A p s).comp (termD A A' x p n s)‖ +
      ‖(A' p s).flip (term (A p) x n s)‖ := norm_add_le _ _
    _ ≤ ‖A p s‖*‖termD A A' x p n s‖ + ‖(A' p s).flip‖*‖term (A p) x n s‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ M*(‖x‖*(2*M)^n*|s|^n/(n.factorial:ℝ)) +
      M*(‖x‖*(2*M)^n*|s|^n/(n.factorial:ℝ)) := by
        rw [hn]
        exact add_le_add (mul_le_mul (hb p s) hd (norm_nonneg _) hM)
          (mul_le_mul (hb' p s) ht (norm_nonneg _) hM)
    _ = _ := by rw [pow_succ]; ring

lemma termD_bound (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hA' : ∀ p,Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p s,‖A p s‖ ≤ M) (hb' : ∀ p s,‖A' p s‖ ≤ M)
    (x : E) (p : H) (n : ℕ) (t : ℝ) :
    ‖termD A A' x p n t‖ ≤ ‖x‖*(2*M)^n*|t|^n/(n.factorial:ℝ) := by
  induction n generalizing t with
  | zero => simp [termD]
  | succ n ih =>
    have hc : Continuous (fun s => (A p s).comp (termD A A' x p n s) +
        (A' p s).flip (term (A p) x n s)) :=
      ((hA p).clm_comp (termD_continuous A A' hA hA' x p n)).add
        (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp (hA' p)).clm_apply (term_continuous (hA p) x n))
    change ‖∫ s in (0:ℝ)..t,_‖ ≤ _
    calc
      _ ≤ ∫ s in Set.uIoc 0 t,
          ‖(A p s).comp (termD A A' x p n s) + (A' p s).flip (term (A p) x n s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Set.uIoc 0 t,(‖x‖*(2*M)^(n+1)/(n.factorial:ℝ))*|s|^n := by
        apply integral_mono_ae (hc.intervalIntegrable 0 t).def'.norm
          ((continuous_const.mul (continuous_abs.pow n)).intervalIntegrable 0 t).def'
        exact Filter.Eventually.of_forall (fun s => param_integrand_bound A A' hA hM hb hb' x n p s (ih s))
      _ = _ := by
        rw [integral_const_mul]
        have hi := integral_pow_abs_sub_uIoc (a := (0:ℝ)) (b := t) (n := n)
        simp only [sub_zero] at hi
        rw [hi,Nat.factorial_succ]
        push_cast
        field_simp

/-- Differentiate the actual iterated integrals, not an assumed parameter flow. -/
lemma term_hasFDerivAt_parameter (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hA' : ∀ p,Continuous (A' p))
    (hdA : ∀ p t,HasFDerivAt (fun q => A q t) (A' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p s,‖A p s‖ ≤ M) (hb' : ∀ p s,‖A' p s‖ ≤ M)
    (x : E) (n : ℕ) (p : H) (t : ℝ) :
    HasFDerivAt (fun q => term (A q) x n t) (termD A A' x p n t) p := by
  induction n generalizing p t with
  | zero => exact hasFDerivAt_const x p
  | succ n ih =>
    have hc (q : H) : Continuous (fun s => A q s (term (A q) x n s)) :=
      (hA q).clm_apply (term_continuous (hA q) x n)
    have hd (q : H) : Continuous (fun s => (A q s).comp (termD A A' x q n s) +
        (A' q s).flip (term (A q) x n s)) :=
      ((hA q).clm_comp (termD_continuous A A' hA hA' x q n)).add
        (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp (hA' q)).clm_apply (term_continuous (hA q) x n))
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le'' (s := Set.univ)
      (bound := fun s => (‖x‖*(2*M)^(n+1)/(n.factorial:ℝ))*|s|^n)
      Filter.univ_mem (Filter.Eventually.of_forall (fun q => (hc q).aestronglyMeasurable))
      ((hc p).intervalIntegrable 0 t) (hd p).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s q _ => param_integrand_bound A A' hA hM hb hb' x n q s
        (termD_bound A A' hA hA' hM hb hb' x q n s)))
      ((continuous_const.mul (continuous_abs.pow n)).intervalIntegrable 0 t)
      (Filter.Eventually.of_forall (fun s q _ => (hdA q s).clm_apply (ih q s)))

/-- Genuine parameter differentiability of the global Peano–Baker solution,
with an explicit convergent series for its derivative. -/
theorem flow_hasFDerivAt_parameter (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hA' : ∀ p,Continuous (A' p))
    (hdA : ∀ p t,HasFDerivAt (fun q => A q t) (A' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p s,‖A p s‖ ≤ M) (hb' : ∀ p s,‖A' p s‖ ≤ M)
    (x : E) (p : H) (t : ℝ) :
    HasFDerivAt (fun q => flow (A q) x t) (∑' n,termD A A' x p n t) p := by
  unfold flow
  refine hasFDerivAt_tsum (f := fun n q => term (A q) x n t)
    (f' := fun n q => termD A A' x q n t) (x₀ := p)
    (u := fun n : ℕ => ‖x‖*(2*M)^n*|t|^n/(n.factorial:ℝ)) ?_ ?_ ?_ ?_ p
  · simpa only [mul_pow,mul_div_assoc,mul_assoc] using
      (Real.summable_pow_div_factorial (2*M*|t|)).mul_left ‖x‖
  · exact fun n q => term_hasFDerivAt_parameter A A' hA hA' hdA hM hb hb' x n q t
  · exact fun n q => termD_bound A A' hA hA' hM hb hb' x q n t
  · exact term_summable (hA p) hM (hb p) x t

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def flowD (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (x : E) (p : H) (t : ℝ) : H →L[ℝ] E := ∑' n,termD A A' x p n t

lemma termD_summable (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hA' : ∀ p,Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p s,‖A p s‖ ≤ M) (hb' : ∀ p s,‖A' p s‖ ≤ M)
    (x : E) (p : H) (t : ℝ) : Summable (fun n => termD A A' x p n t) := by
  have hs := (Real.summable_pow_div_factorial (2*M*|t|)).mul_left ‖x‖
  apply hs.of_norm_bounded
  intro n
  simpa only [mul_pow,mul_div_assoc,mul_assoc] using termD_bound A A' hA hA' hM hb hb' x p n t

omit [CompleteSpace E] in
lemma flowD_initial (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (x : E) (p : H) : flowD A A' x p 0=0 := by
  unfold flowD
  have hz : ∀ n,termD A A' x p n 0=0 := by
    intro n
    cases n <;> simp [termD]
  simp only [hz,tsum_zero]

/-- The derivative in the actual control parameter satisfies the actual
variational ODE, with zero initial value. -/
theorem flowD_hasDerivAt (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hA' : ∀ p,Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p s,‖A p s‖ ≤ M) (hb' : ∀ p s,‖A' p s‖ ≤ M)
    (x : E) (p : H) (t : ℝ) :
    HasDerivAt (flowD A A' x p)
      ((A p t).comp (flowD A A' x p t)+(A' p t).flip (flow (A p) x t)) t := by
  let R : ℝ := |t|+1
  have hR : 0 < R := by dsimp [R]; positivity
  let F : ℕ → ℝ → H →L[ℝ] E := fun n s =>
    (A p s).comp (termD A A' x p n s)+(A' p s).flip (term (A p) x n s)
  have hFc (n : ℕ) : Continuous (F n) :=
    ((hA p).clm_comp (termD_continuous A A' hA hA' x p n)).add
      (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp (hA' p)).clm_apply
        (term_continuous (hA p) x n))
  have hf (n : ℕ) (s : ℝ) : HasDerivAt (termD A A' x p (n+1)) (F n s) s :=
    intervalIntegral.integral_hasDerivAt_right ((hFc n).intervalIntegrable 0 s)
      (hFc n).stronglyMeasurable.stronglyMeasurableAtFilter (hFc n).continuousAt
  have hu : Summable (fun n : ℕ => (‖x‖*(2*M))*(2*M*R)^n/(n.factorial:ℝ)) := by
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial (2*M*R)).mul_left (‖x‖*(2*M))
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ Set.Ioo (-R) R) :
      ‖F n s‖ ≤ (‖x‖*(2*M))*(2*M*R)^n/(n.factorial:ℝ) := by
    have ha : |s| ≤ R := abs_le.2 ⟨hs.1.le,hs.2.le⟩
    calc
      _ ≤ (‖x‖*(2*M)^(n+1)/(n.factorial:ℝ))*|s|^n :=
        param_integrand_bound A A' hA hM hb hb' x n p s
          (termD_bound A A' hA hA' hM hb hb' x p n s)
      _ ≤ (‖x‖*(2*M)^(n+1)/(n.factorial:ℝ))*R^n := by gcongr
      _ = _ := by simp only [pow_succ,mul_pow]; ring
  have hzero : Summable (fun n => termD A A' x p (n+1) 0) := by
    simp only [termD,intervalIntegral.integral_same]
    exact summable_zero
  have ht : t ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [le_abs_self t,neg_abs_le t]
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n s _ => hf n s) hbound
    (show (0:ℝ) ∈ Set.Ioo (-R) R by constructor <;> linarith) hzero ht
  have he : flowD A A' x p = fun s => ∑' n,termD A A' x p (n+1) s := by
    funext s
    have h := (termD_summable A A' hA hA' hM hb hb' x p s).tsum_eq_zero_add
    simpa only [flowD,termD,zero_add] using h
  rw [← he] at hd
  have hp := ((ContinuousLinearMap.compL ℝ H E E) (A p t)).map_tsum
    (termD_summable A A' hA hA' hM hb hb' x p t)
  have hq := (A' p t).flip.map_tsum (term_summable (hA p) hM (hb p) x t)
  have hs₁ := ((ContinuousLinearMap.compL ℝ H E E) (A p t)).summable
    (termD_summable A A' hA hA' hM hb hb' x p t)
  have hs₂ := (A' p t).flip.summable (term_summable (hA p) hM (hb p) x t)
  apply hd.congr_deriv
  symm
  change (A p t).comp (∑' n,termD A A' x p n t)+(A' p t).flip (∑' n,term (A p) x n t) = _
  simp only [ContinuousLinearMap.compL_apply] at hp
  rw [hp,hq]
  exact (hs₁.tsum_add hs₂).symm

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Inversion is differentiated only at a genuinely invertible value operator. -/
lemma clm_inverse_fderiv {V : H → E →L[ℝ] E} {V' : H →L[ℝ] E →L[ℝ] E} {p : H}
    (hV : IsUnit (V p)) (hD : HasFDerivAt V V' p) :
    HasFDerivAt (fun q => Ring.inverse (V q))
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
        (Ring.inverse (V p)) (Ring.inverse (V p))).comp V') p := by
  obtain ⟨v,hv⟩ := hV
  have hf : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (↑v⁻¹) (↑v⁻¹)) (V p) :=
    hv ▸ hasFDerivAt_ringInverse (𝕜 := ℝ) v
  simpa only [Function.comp_def,← hv,Ring.inverse_unit] using hf.comp p hD

/-- The actual slope has a genuine parameter derivative, without a prior bound
on that derivative. The two inputs are the actual variational value jets. -/
lemma slope_parameter_deriv {V W : H → E →L[ℝ] E}
    {V' W' : H →L[ℝ] E →L[ℝ] E} {p : H}
    (hV : IsUnit (V p)) (hVD : HasFDerivAt V V' p) (hWD : HasFDerivAt W W' p) :
    HasFDerivAt (fun q => W q * Ring.inverse (V q))
      ((ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) 1 (Ring.inverse (V p))).comp W' -
       (ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
         (W p * Ring.inverse (V p)) (Ring.inverse (V p))).comp V') p := by
  have hd := hWD.mul' (clm_inverse_fderiv hV hVD)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro h
  change W p * (-(Ring.inverse (V p) * V' h * Ring.inverse (V p))) +
    W' h * Ring.inverse (V p) =
      1 * W' h * Ring.inverse (V p) -
        (W p * Ring.inverse (V p)) * V' h * Ring.inverse (V p)
  simp only [one_mul,mul_neg,mul_assoc]
  abel

local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- Apply the global actual-flow parameter differentiability theorem to the
center-regular second-order operator system. The coefficient derivative is
explicit data and must be an actual Frechet derivative, never an assumed slope. -/
theorem actual_slope_hasFDerivAt
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ]
      ((E →L[ℝ] E)×(E →L[ℝ] E))))
    (hA : ∀ p,Continuous (A p)) (hb : Continuous b)
    (hB' : ∀ p,Continuous (B' p))
    (hdB : ∀ p t,HasFDerivAt (fun q => block (leftAction (A q)) b t) (B' p t) p)
    {M : ℝ} (hM : 0 ≤ M)
    (hnB : ∀ p t,‖block (leftAction (A p)) b t‖ ≤ M)
    (hnB' : ∀ p t,‖(B' p t : H →L[ℝ] (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ]
      ((E →L[ℝ] E)×(E →L[ℝ] E))))‖ ≤ M)
    (l : ℝ) (p : H) (t : ℝ) (hV : IsUnit (operatorValue (A p) b l t)) :
    DifferentiableAt ℝ (fun q => slope (A q) b l t) p := by
  let B := fun q => block (leftAction (A q)) b
  have hf := flow_hasFDerivAt_parameter B B'
    (fun q => block_continuous (leftAction_continuous (hA q)) hb) hB' hdB
    hM hnB hnB' ((1 : E →L[ℝ] E),l • (1 : E →L[ℝ] E)) p t
  have hfst := (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp p hf
  have hsnd := (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp p hf
  exact (slope_parameter_deriv (V := fun q => operatorValue (A q) b l t)
    (W := fun q => operatorVelocity (A q) b l t) hV hfst hsnd).differentiableAt

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

lemma ring_inverse_deriv {Y : ℝ → R} {Y' : R} {t : ℝ}
    (hy : IsUnit (Y t)) (hd : HasDerivAt Y Y' t) :
    HasDerivAt (fun s => Ring.inverse (Y s))
      (-(Ring.inverse (Y t)*Y'*Ring.inverse (Y t))) t := by
  obtain ⟨u,hu⟩ := hy
  have hf : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ R (↑u⁻¹) (↑u⁻¹)) (Y t) :=
    hu ▸ hasFDerivAt_ringInverse (𝕜 := ℝ) u
  simpa only [Function.comp_def,neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    ← hu,Ring.inverse_unit] using hf.comp_hasDerivAt t hd

/-- Genuine time evolution of the logarithmic derivative of a variational
value solution. This is applied to the already constructed actual first jet. -/
theorem variation_slope_deriv (A P Y U V A₁ p : ℝ → R) {t : ℝ}
    (hY : HasDerivAt Y (P t*Y t) t)
    (hP : HasDerivAt P (A t-p t*P t-P t*P t) t)
    (hU : HasDerivAt U (V t) t)
    (hV : HasDerivAt V (A₁ t*Y t+A t*U t-p t*V t) t)
    (hy : IsUnit (Y t)) :
    HasDerivAt (fun s => (V s-P s*U s)*Ring.inverse (Y s))
      (A₁ t-p t*((V t-P t*U t)*Ring.inverse (Y t))-
        P t*((V t-P t*U t)*Ring.inverse (Y t))-
        ((V t-P t*U t)*Ring.inverse (Y t))*P t) t := by
  have hd := (hV.sub (hP.mul hU)).mul (ring_inverse_deriv hy hY)
  have hi : Y t*Ring.inverse (Y t)=1 := Ring.mul_inverse_cancel _ hy
  have he : ((A₁ t*Y t+A t*U t-p t*V t)-
      ((A t-p t*P t-P t*P t)*U t+P t*V t))*Ring.inverse (Y t)+
      (V t-P t*U t)*(-(Ring.inverse (Y t)*(P t*Y t)*Ring.inverse (Y t))) =
      A₁ t-p t*((V t-P t*U t)*Ring.inverse (Y t))-
        P t*((V t-P t*U t)*Ring.inverse (Y t))-
        ((V t-P t*U t)*Ring.inverse (Y t))*P t := by
    simp only [sub_mul,add_mul,mul_sub,mul_neg,mul_assoc,hi,mul_one]
    noncomm_ring
  exact he ▸ hd

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- The crucial regrouping of the parameter-error equation. Both sides damp
with the actual positive regular slope P; no bound on its derivative is used. -/
theorem riccati_parameter_regroup (A₁ p P Q P₁ Q₁ Q₁' : R) :
    (A₁-p*P₁-P*P₁-P₁*P)-Q₁' =
      (A₁-p*Q₁-Q₁*Q-Q*Q₁-Q₁')-
        (p+P)*(P₁-Q₁)-(P₁-Q₁)*P-Q₁*(P-Q)-(P-Q)*Q₁ := by
  noncomm_ring

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

abbrev OperatorPhase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E →L[ℝ] E)×(E →L[ℝ] E)

def phaseJet (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (l : ℝ) (p : H) (t : ℝ) : H →L[ℝ] OperatorPhase E :=
  flowD (fun q => block (leftAction (A q)) b) B' (1,l • 1) p t

def valueJet (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (l : ℝ) (p : H) (t : ℝ) : H →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ _ _).comp (phaseJet A b B' l p t)

def velocityJet (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (l : ℝ) (p : H) (t : ℝ) : H →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ _ _).comp (phaseJet A b B' l p t)

def slopeJet (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (l : ℝ) (p : H) (t : ℝ) : H →L[ℝ] E →L[ℝ] E :=
  ((ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) 1
    (Ring.inverse (operatorValue (A p) b l t))).comp (velocityJet A b B' l p t))-
  ((ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (slope (A p) b l t)
    (Ring.inverse (operatorValue (A p) b l t))).comp (valueJet A b B' l p t))

omit [CompleteSpace E] in
lemma slopeJet_apply (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (l : ℝ) (p h : H) (t : ℝ) :
    slopeJet A b B' l p t h =
      (velocityJet A b B' l p t h-slope (A p) b l t*valueJet A b B' l p t h)*
        Ring.inverse (operatorValue (A p) b l t) := by
  simp only [slopeJet,sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply,one_mul,sub_mul]

/-- Explicit actual parameter derivative of the actual global regular slope. -/
theorem slope_hasFDerivAt_jet
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (hA : ∀ p,Continuous (A p)) (hb : Continuous b) (hB' : ∀ p,Continuous (B' p))
    (hdB : ∀ p t,HasFDerivAt (fun q => block (leftAction (A q)) b t) (B' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hnB : ∀ p t,‖block (leftAction (A p)) b t‖ ≤ M)
    (hnB' : ∀ p t,‖B' p t‖ ≤ M)
    (l : ℝ) (p : H) (t : ℝ) (hV : IsUnit (operatorValue (A p) b l t)) :
    HasFDerivAt (fun q => slope (A q) b l t) (slopeJet A b B' l p t) p := by
  have hf := flow_hasFDerivAt_parameter (fun q => block (leftAction (A q)) b) B'
    (fun q => block_continuous (leftAction_continuous (hA q)) hb) hB' hdB
    hM hnB hnB' ((1 : E →L[ℝ] E),l • (1 : E →L[ℝ] E)) p t
  have hfst := (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp p hf
  have hsnd := (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp p hf
  exact slope_parameter_deriv (V := fun q => operatorValue (A q) b l t)
    (W := fun q => operatorVelocity (A q) b l t) hV hfst hsnd

/-- The actual center-regular parameter jet evolves by the damped Riccati
variational equation. There is no assumed bound on this jet. -/
theorem slopeJet_hasDerivAt
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hb : Continuous b) (hB' : ∀ p,Continuous (B' p))
    (hBeval : ∀ p t h v,B' p t h v=(0,A' p t h*v.1))
    {M MA Mb : ℝ} (hM : 0 ≤ M) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnB : ∀ p t,‖block (leftAction (A p)) b t‖ ≤ M) (hnB' : ∀ p t,‖B' p t‖ ≤ M)
    (hnA : ∀ p t,‖A p t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (l : ℝ) (p h : H) (t : ℝ) (hV : IsUnit (operatorValue (A p) b l t)) :
    HasDerivAt (fun s => slopeJet A b B' l p s h)
      (A' p t h-b t • slopeJet A b B' l p t h-
        slope (A p) b l t*slopeJet A b B' l p t h-
        slopeJet A b B' l p t h*slope (A p) b l t) t := by
  have hj := (flowD_hasDerivAt (fun q => block (leftAction (A q)) b) B'
    (fun q => block_continuous (leftAction_continuous (hA q)) hb) hB' hM hnB hnB'
    ((1:E →L[ℝ] E),l • (1:E →L[ℝ] E)) p t).clm_apply (hasDerivAt_const t h)
  have hu : HasDerivAt (fun s => valueJet A b B' l p s h) (velocityJet A b B' l p t h) t := by
    have hh := (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t hj
    simpa [Function.comp_def,valueJet,velocityJet,phaseJet,block_apply,hBeval] using hh
  have hv : HasDerivAt (fun s => velocityJet A b B' l p s h)
      (A' p t h*operatorValue (A p) b l t+A p t*valueJet A b B' l p t h-
        b t • velocityJet A b B' l p t h) t := by
    have hh := (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt t hj
    have he : A' p t h*operatorValue (A p) b l t+
        A p t*valueJet A b B' l p t h-b t • velocityJet A b B' l p t h =
        (A p t*valueJet A b B' l p t h-b t • velocityJet A b B' l p t h)+
          A' p t h*operatorValue (A p) b l t := by abel
    rw [he]
    simpa [Function.comp_def,valueJet,velocityJet,phaseJet,operatorValue,value,phase,block_apply,hBeval,leftAction,ContinuousLinearMap.mul_def,ContinuousLinearMap.one_def] using hh
  have hy := operatorValue_deriv (hA p) hb hMA hMb (hnA p) hnb l t
  have he : slope (A p) b l t*operatorValue (A p) b l t=operatorVelocity (A p) b l t := by
    simp only [slope,mul_assoc,Ring.inverse_mul_cancel _ hV,mul_one]
  rw [← he] at hy
  have hp := slope_deriv (hA p) hb hMA hMb (hnA p) hnb l t hV
  have hh := variation_slope_deriv (A p) (slope (A p) b l) (operatorValue (A p) b l)
    (fun s => valueJet A b B' l p s h) (fun s => velocityJet A b B' l p s h)
    (fun s => A' p s h) (fun s => b s • (1:E →L[ℝ] E)) hy
    (by simpa only [smul_mul_assoc,one_mul] using hp) hu
    (by simpa only [smul_mul_assoc,one_mul] using hv) hV
  simpa only [← slopeJet_apply,smul_mul_assoc,one_mul] using hh

omit [CompleteSpace E] in
lemma slopeJet_initial (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (l : ℝ) (p : H) : slopeJet A b B' l p 0=0 := by
  ext h
  simp only [slopeJet_apply,valueJet,velocityJet,phaseJet,flowD_initial,
    ContinuousLinearMap.comp_apply,zero_apply,map_zero,mul_zero,sub_self,zero_mul]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [CompleteSpace E] in
lemma termD_frozen (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (x : E) (p q : H) (n : ℕ) (t : ℝ) :
    termD (fun _ : H => A p) (fun _ : H => A' p) x q n t=termD A A' x p n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp only [termD,ih]

omit [CompleteSpace E] in
lemma flowD_frozen (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (x : E) (p q : H) (t : ℝ) :
    flowD (fun _ : H => A p) (fun _ : H => A' p) x q t=flowD A A' x p t := by
  simp only [flowD,termD_frozen]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

omit [CompleteSpace E] in
lemma slopeJet_frozen (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (l : ℝ) (p q : H) (t : ℝ) :
    slopeJet (fun _ : H => A p) b (fun _ : H => B' p) l q t=slopeJet A b B' l p t := by
  have he := flowD_frozen (fun q => block (leftAction (A q)) b) B' (1,l • 1) p q t
  simp only [slopeJet,valueJet,velocityJet,phaseJet]
  rw [he]

/-- Actual directional slope jets need bounds only at the current parameter.
This avoids imposing nonexistent global bounds on the full control parameter
space outside the admissible ball. -/
theorem slopeJet_hasDerivAt_pointwise
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (p h : H)
    (hA : Continuous (A p)) (hb : Continuous b) (hB' : Continuous (B' p))
    (hBeval : ∀ t z v,B' p t z v=(0,A' p t z*v.1))
    {M MA Mb : ℝ} (hM : 0 ≤ M) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnB : ∀ t,‖block (leftAction (A p)) b t‖ ≤ M) (hnB' : ∀ t,‖B' p t‖ ≤ M)
    (hnA : ∀ t,‖A p t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (l : ℝ) (t : ℝ) (hV : IsUnit (operatorValue (A p) b l t)) :
    HasDerivAt (fun s => slopeJet A b B' l p s h)
      (A' p t h-b t • slopeJet A b B' l p t h-
        slope (A p) b l t*slopeJet A b B' l p t h-
        slopeJet A b B' l p t h*slope (A p) b l t) t := by
  simpa only [slopeJet_frozen] using slopeJet_hasDerivAt
    (fun _ : H => A p) b (fun _ : H => B' p) (fun _ : H => A' p)
    (fun _ => hA) hb (fun _ => hB') (fun _ => hBeval) hM hMA hMb
    (fun _ => hnB) (fun _ => hnB') (fun _ => hnA) hnb l p h t hV

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Matrix Set
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- Uniform-history L1 value and first-jet error for the ACTUAL center-regular
Peano--Baker solution. Coercivity of the unknown Riccati solution is PRODUCED
from positivity and its Euclidean core; neither a solution nor an unknown-jet
bound is supplied as a hypothesis. The comparison residuals are explicit. -/
theorem actual_slow_pulse_integrated (basis : OrthonormalBasis ι ℝ E)
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (p h : H)
    (hA : Continuous (A p)) (hb : Continuous b) (hB' : Continuous (B' p))
    (hA' : Continuous (fun t => A' p t h))
    (hBeval : ∀ t z v,B' p t z v=(0,A' p t z*v.1))
    {M MA Mb : ℝ} (hM : 0 ≤ M) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnB : ∀ t,‖block (leftAction (A p)) b t‖ ≤ M) (hnB' : ∀ t,‖B' p t‖ ≤ M)
    (hnA : ∀ t,‖A p t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hAp : ∀ t x,0 ≤ inner ℝ x (A p t x))
    {l B : ℝ} (hl : 0 < l) (hAc : ∀ t ≤ 0,∀ x,A p t x=(l*(l+B)) • x)
    (hbc : ∀ t ≤ 0,b t=B)
    (Q Qdot Qh Qhdot : ℝ → Matrix ι ι ℝ)
    (hdQ : ∀ t,HasDerivAt Q (Qdot t) t) (hdQh : ∀ t,HasDerivAt Qh (Qhdot t) t)
    (hcQdot : Continuous Qdot) (hcQhdot : Continuous Qhdot)
    {a T γ C η : ℝ} (ha : 0 ≤ a) (hT : 1 ≤ T) (hγ : 0 < γ)
    (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hbl : ∀ t ∈ Icc a (a+T),γ ≤ b t)
    (hQpos : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      0 ≤ ∑ i,∑ j,v i*Q t i j*v j)
    (hρ : ∀ t ∈ Icc a (a+T),
      ‖orthogonalMatrix basis (A p t)-b t • Q t-Q t*Q t-Qdot t‖ ≤ C*η/T)
    (hρh : ∀ t ∈ Icc a (a+T),
      ‖orthogonalMatrix basis (A' p t h)-b t • Qh t-Qh t*Q t-Q t*Qh t-Qhdot t‖ ≤ C*η/T)
    (hQhn : ∀ t ∈ Icc a (a+T),‖Qh t‖ ≤ C/T)
    (hinit : ‖orthogonalMatrix basis (slope (A p) b l a)-Q a‖ ≤ C*η)
    (hjetinit : orthogonalMatrix basis (slopeJet A b B' l p a h)=Qh a) :
    (∫ t in a..a+T,‖orthogonalMatrix basis (slope (A p) b l t)-Q t‖) ≤ 2*C*η/γ ∧
    (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b B' l p t h)-Qh t‖) ≤
      C*η/γ+4*C^2*η/γ^2 := by
  let P := fun t => orthogonalMatrix basis (slope (A p) b l t)
  let Ph := fun t => orthogonalMatrix basis (slopeJet A b B' l p t h)
  let ρ := fun t => orthogonalMatrix basis (A p t)-b t • Q t-Q t*Q t-Qdot t
  let ρh := fun t => orthogonalMatrix basis (A' p t h)-b t • Qh t-Qh t*Q t-Q t*Qh t-Qhdot t
  have hu := actual_value_unit_all_time hA hb hMA hMb hnA hnb hAp hl hAc hbc
  have hdP (t : ℝ) : HasDerivAt P
      (orthogonalMatrix basis (A p t)-b t • P t-P t*P t) t :=
    orthogonalMatrix_riccati_deriv basis (slope_deriv hA hb hMA hMb hnA hnb l t (hu t))
  have hdPh (t : ℝ) : HasDerivAt Ph
      (orthogonalMatrix basis (A' p t h)-b t • Ph t-P t*Ph t-Ph t*P t) t :=
    orthogonalMatrix_jet_deriv basis (slopeJet_hasDerivAt_pointwise A b B' A' p h
      hA hb hB' hBeval hM hMA hMb hnB hnB' hnA hnb l t (hu t))
  have hcQ : Continuous Q := continuous_iff_continuousAt.2 fun t => (hdQ t).continuousAt
  have hcQh : Continuous Qh := continuous_iff_continuousAt.2 fun t => (hdQh t).continuousAt
  have hcρ : Continuous ρ :=
    ((((orthogonalMatrix basis).continuous.comp hA).sub (hb.smul hcQ)).sub
      (hcQ.mul hcQ)).sub hcQdot
  have hcρh : Continuous ρh :=
    (((((orthogonalMatrix basis).continuous.comp hA').sub (hb.smul hcQh)).sub
      (hcQh.mul hcQ)).sub (hcQ.mul hcQh)).sub hcQhdot
  have hPpos (t : ℝ) (ht : t ∈ Icc a (a+T)) (v : ι → ℝ) :
      0 ≤ ∑ i,∑ j,v i*P t i j*v j := by
    have he := orthogonalMatrix_coercive basis (slope (A p) b l t) (c := 0)
      (fun x => by simpa only [zero_mul] using
        slope_nonnegative hA hb hMA hMb hnA hnb hAp hl (ha.trans ht.1) (hu t) x) v
    simpa only [zero_mul] using he
  have hL (t : ℝ) (ht : t ∈ Icc a (a+T)) (v : ι → ℝ) :
      γ*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*(b t • (1:Matrix ι ι ℝ)+P t) i j*v j := by
    rw [quadratic_add,quadratic_scalar_one]
    have he := mul_le_mul_of_nonneg_right (hbl t ht)
      (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (v i))
    linarith [hPpos t ht v]
  have he := slow_pulse_error_estimate (c := γ) (d := 0) (c₁ := γ) (d₁ := 0)
    hT hγ hC hη (add_zero γ) (add_zero γ) hcρ hcρh hcQh
    (fun t => riccati_error_deriv (hdP t) (hdQ t))
    (fun t => riccati_error_jet_deriv (hdPh t) (hdQh t))
    hρ hρh hQhn hL
    (fun t ht v => by simpa only [zero_mul] using hQpos t ht v)
    hL (fun t ht v => by simpa only [zero_mul] using hPpos t ht v)
    hinit (sub_eq_zero.2 hjetinit)
  exact ⟨he.2.1,he.2.2.2⟩

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma termD_continuous_at_parameter (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) {p : H}
    (hA : Continuous (A p)) (hA' : Continuous (A' p))
    (x : E) (n : ℕ) : Continuous (termD A A' x p n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have hc : Continuous (fun s => (A p s).comp (termD A A' x p n s)+
        (A' p s).flip (term (A p) x n s)) :=
      (hA.clm_comp ih).add (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp hA').clm_apply
        (term_continuous hA x n))
    exact continuous_iff_continuousAt.2 fun t =>
      (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
        hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt

lemma param_integrand_bound_at_parameter (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    {p : H} (hA : Continuous (A p)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ s,‖A p s‖ ≤ M) (hb' : ∀ s,‖A' p s‖ ≤ M)
    (x : E) (n : ℕ) (s : ℝ)
    (hd : ‖termD A A' x p n s‖ ≤ ‖x‖*(2*M)^n*|s|^n/(n.factorial:ℝ)) :
    ‖(A p s).comp (termD A A' x p n s) + (A' p s).flip (term (A p) x n s)‖ ≤
      (‖x‖*(2*M)^(n+1)/(n.factorial:ℝ))*|s|^n := by
  have ht := term_bound hA (show 0 ≤ 2*M by positivity)
    (fun s => (hb s).trans (by linarith)) x n s
  have hn : ‖(A' p s).flip‖=‖A' p s‖ := ContinuousLinearMap.opNorm_flip _
  calc
    _ ≤ ‖(A p s).comp (termD A A' x p n s)‖ +
      ‖(A' p s).flip (term (A p) x n s)‖ := norm_add_le _ _
    _ ≤ ‖A p s‖*‖termD A A' x p n s‖ + ‖(A' p s).flip‖*‖term (A p) x n s‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ M*(‖x‖*(2*M)^n*|s|^n/(n.factorial:ℝ)) +
      M*(‖x‖*(2*M)^n*|s|^n/(n.factorial:ℝ)) := by
        rw [hn]
        exact add_le_add (mul_le_mul (hb s) hd (norm_nonneg _) hM)
          (mul_le_mul (hb' s) ht (norm_nonneg _) hM)
    _ = _ := by rw [pow_succ]; ring

lemma termD_bound_at_parameter (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    {p : H} (hA : Continuous (A p)) (hA' : Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s,‖A p s‖ ≤ M) (hb' : ∀ s,‖A' p s‖ ≤ M)
    (x : E) (n : ℕ) (t : ℝ) :
    ‖termD A A' x p n t‖ ≤ ‖x‖*(2*M)^n*|t|^n/(n.factorial:ℝ) := by
  induction n generalizing t with
  | zero => simp [termD]
  | succ n ih =>
    have hc : Continuous (fun s => (A p s).comp (termD A A' x p n s) +
        (A' p s).flip (term (A p) x n s)) :=
      (hA.clm_comp (termD_continuous_at_parameter A A' hA hA' x n)).add
        (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp hA').clm_apply (term_continuous hA x n))
    change ‖∫ s in (0:ℝ)..t,_‖ ≤ _
    calc
      _ ≤ ∫ s in Set.uIoc 0 t,
          ‖(A p s).comp (termD A A' x p n s) + (A' p s).flip (term (A p) x n s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s in Set.uIoc 0 t,(‖x‖*(2*M)^(n+1)/(n.factorial:ℝ))*|s|^n := by
        apply integral_mono_ae (hc.intervalIntegrable 0 t).def'.norm
          ((continuous_const.mul (continuous_abs.pow n)).intervalIntegrable 0 t).def'
        exact Filter.Eventually.of_forall (fun s => param_integrand_bound_at_parameter A A' hA hM hb hb' x n s (ih s))
      _ = _ := by
        rw [integral_const_mul]
        have hi := integral_pow_abs_sub_uIoc (a := (0:ℝ)) (b := t) (n := n)
        simp only [sub_zero] at hi
        rw [hi,Nat.factorial_succ]
        push_cast
        field_simp


/-- Local-parameter differentiation of actual Peano--Baker iterates. The
coefficient bounds are only required on the genuine admissible parameter set. -/
lemma term_hasFDerivAt_parameter_on (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) {S : Set H} (hS : IsOpen S)
    (hA : ∀ p ∈ S,Continuous (A p)) (hA' : ∀ p ∈ S,Continuous (A' p))
    (hdA : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => A q t) (A' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p ∈ S,∀ s,‖A p s‖ ≤ M)
    (hb' : ∀ p ∈ S,∀ s,‖A' p s‖ ≤ M)
    (x : E) (n : ℕ) {p : H} (hp : p ∈ S) (t : ℝ) :
    HasFDerivAt (fun q => term (A q) x n t) (termD A A' x p n t) p := by
  induction n generalizing p t with
  | zero => exact hasFDerivAt_const x p
  | succ n ih =>
    have hc (q : H) (hq : q ∈ S) : Continuous (fun s => A q s (term (A q) x n s)) :=
      (hA q hq).clm_apply (term_continuous (hA q hq) x n)
    have hd (q : H) (hq : q ∈ S) : Continuous (fun s =>
        (A q s).comp (termD A A' x q n s)+(A' q s).flip (term (A q) x n s)) :=
      ((hA q hq).clm_comp (termD_continuous_at_parameter A A' (hA q hq) (hA' q hq) x n)).add
        (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp (hA' q hq)).clm_apply
          (term_continuous (hA q hq) x n))
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le'' (s := S)
      (bound := fun s => (‖x‖*(2*M)^(n+1)/(n.factorial:ℝ))*|s|^n)
      (hS.mem_nhds hp) (Filter.Eventually.mono (hS.mem_nhds hp) fun q hq => (hc q hq).aestronglyMeasurable)
      ((hc p hp).intervalIntegrable 0 t) (hd p hp).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s q hq =>
        param_integrand_bound_at_parameter A A' (hA q hq) hM (hb q hq) (hb' q hq) x n s
          (termD_bound_at_parameter A A' (hA q hq) (hA' q hq) hM (hb q hq) (hb' q hq) x n s)))
      ((continuous_const.mul (continuous_abs.pow n)).intervalIntegrable 0 t)
      (Filter.Eventually.of_forall (fun s q hq => (hdA q hq s).clm_apply (ih hq s)))

/-- The actual flow is C1-differentiable on an admissible open connected ball;
no uniformity over inadmissible or arbitrarily large control parameters occurs. -/
theorem flow_hasFDerivAt_parameter_on (A : H → ℝ → E →L[ℝ] E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) {S : Set H}
    (hS : IsOpen S) (hSc : IsPreconnected S)
    (hA : ∀ p ∈ S,Continuous (A p)) (hA' : ∀ p ∈ S,Continuous (A' p))
    (hdA : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => A q t) (A' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p ∈ S,∀ s,‖A p s‖ ≤ M)
    (hb' : ∀ p ∈ S,∀ s,‖A' p s‖ ≤ M)
    (x : E) {p : H} (hp : p ∈ S) (t : ℝ) :
    HasFDerivAt (fun q => flow (A q) x t) (flowD A A' x p t) p := by
  unfold flow flowD
  refine hasFDerivAt_tsum_of_isPreconnected (f := fun n q => term (A q) x n t)
    (f' := fun n q => termD A A' x q n t) (x₀ := p)
    (u := fun n : ℕ => ‖x‖*(2*M)^n*|t|^n/(n.factorial:ℝ)) ?_ hS hSc ?_ ?_ hp ?_ hp
  · simpa only [mul_pow,mul_div_assoc,mul_assoc] using
      (Real.summable_pow_div_factorial (2*M*|t|)).mul_left ‖x‖
  · exact fun n q hq => term_hasFDerivAt_parameter_on A A' hS hA hA' hdA hM hb hb' x n hq t
  · exact fun n q hq => termD_bound_at_parameter A A' (hA q hq) (hA' q hq) hM
      (hb q hq) (hb' q hq) x n t
  · exact term_summable (hA p hp) hM (hb p hp) x t

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- The variational slope in the quantitative estimates is the GENUINE
Frechet derivative of the actual PB slope on the admissible parameter ball.
The hypotheses only require bounds on that ball, never outside it. -/
theorem slope_hasFDerivAt_jet_on
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    {S : Set H} (hS : IsOpen S) (hSc : IsPreconnected S)
    (hA : ∀ p ∈ S,Continuous (A p)) (hb : Continuous b) (hB' : ∀ p ∈ S,Continuous (B' p))
    (hdB : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => block (leftAction (A q)) b t) (B' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hnB : ∀ p ∈ S,∀ t,‖block (leftAction (A p)) b t‖ ≤ M)
    (hnB' : ∀ p ∈ S,∀ t,‖B' p t‖ ≤ M)
    (l : ℝ) {p : H} (hp : p ∈ S) (t : ℝ) (hV : IsUnit (operatorValue (A p) b l t)) :
    HasFDerivAt (fun q => slope (A q) b l t) (slopeJet A b B' l p t) p := by
  have hf := flow_hasFDerivAt_parameter_on (fun q => block (leftAction (A q)) b) B'
    hS hSc (fun q hq => block_continuous (leftAction_continuous (hA q hq)) hb) hB' hdB
    hM hnB hnB' ((1 : E →L[ℝ] E),l • (1 : E →L[ℝ] E)) hp t
  have hfst := (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp p hf
  have hsnd := (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) (E →L[ℝ] E)).hasFDerivAt.comp p hf
  exact slope_parameter_deriv (V := fun q => operatorValue (A q) b l t)
    (W := fun q => operatorVelocity (A q) b l t) hV hfst hsnd

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Local-in-time integrated damping. A constant exterior extension is applied
only to the scalar integrand, not to the differentiable unknown. Consequently
no artificial globally nonsingular comparison Riccati solution is required. -/
theorem dissipative_integral_on {f f' : ℝ → E} {r : ℝ → ℝ} {c a b : ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b,HasDerivAt f (f' t) t)
    (hr : ContinuousOn r (Icc a b))
    (he : ∀ t ∈ Icc a b,⟪f t,f' t⟫_ℝ ≤ -c*‖f t‖^2+r t*‖f t‖)
    (hz : ∀ t ∈ Icc a b,f t=0 → ‖f' t‖ ≤ r t) :
    c*(∫ t in a..b,‖f t‖) ≤ ‖f a‖-‖f b‖+∫ t in a..b,r t := by
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  let R := IccExtend hab (fun t : Icc a b => r t-c*‖f t‖)
  have hR : Continuous R := continuous_IccExtend_iff.2
    (continuousOn_iff_continuous_domRestrict.1 (hr.sub (continuousOn_const.mul hfc.norm)))
  have hReq (t : ℝ) (ht : t ∈ Icc a b) : R t=r t-c*‖f t‖ := IccExtend_of_mem hab _ ht
  let B := fun t => ‖f a‖+∫ s in a..t,R s
  have hB (t : ℝ) : HasDerivAt B (R t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hR.intervalIntegrable _ _)
      hR.stronglyMeasurable.stronglyMeasurableAtFilter hR.continuousAt).const_add _
  have hh : ‖f b‖ ≤ B b := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary hfc.norm
      (show ‖f a‖ ≤ B a by simp [B])
      (continuous_iff_continuousAt.2 (fun t => (hB t).continuousAt)).continuousOn
      (fun t _ => (hB t).hasDerivWithinAt) _ ⟨hab,le_rfl⟩
    intro t ht z htz
    have hct : t ∈ Icc a b := ⟨ht.1,ht.2.le⟩
    rw [hReq t hct] at htz
    simpa only [_root_.slope,smul_eq_mul,vsub_eq_sub] using
      dissipative_norm_slope (hf t hct) (he t hct) (hz t hct) z (by linarith)
  dsimp only [B] at hh
  have hI : (∫ t in a..b,R t)=∫ t in a..b,r t-c*‖f t‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hReq t (by simpa only [uIcc_of_le hab] using ht)
  have hcint : ContinuousOn (fun t => c*‖f t‖) (Icc a b) :=
    continuousOn_const.mul hfc.norm
  rw [hI,intervalIntegral.integral_sub
    (hr.intervalIntegrable_of_Icc hab)
    (hcint.intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_const_mul] at hh
  linarith

/-- The sharp exponential bound only uses derivatives ON the pulse interval. -/
theorem dissipative_gronwall_on {f f' : ℝ → E} {c M a b : ℝ}
    (hf : ∀ t ∈ Icc a b,HasDerivAt f (f' t) t)
    (he : ∀ t ∈ Icc a b,⟪f t,f' t⟫_ℝ ≤ -c*‖f t‖^2+M*‖f t‖)
    (hz : ∀ t ∈ Icc a b,f t=0 → ‖f' t‖ ≤ M) :
    ∀ t ∈ Icc a b,‖f t‖ ≤ gronwallBound ‖f a‖ (-c) M (t-a) := by
  have hfc : ContinuousOn f (Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  apply le_gronwallBound_of_liminf_deriv_right_le hfc.norm _ le_rfl (fun _ _ => le_rfl)
  intro t ht
  exact dissipative_norm_slope (r := fun _ => M) (hf t ⟨ht.1,ht.2.le⟩)
    (he t ⟨ht.1,ht.2.le⟩) (hz t ⟨ht.1,ht.2.le⟩)

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Matrix Set
open scoped Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sharp integrated Sylvester damping in the actual Frobenius matrix norm. -/
theorem sylvester_integrated_on {X F L R : ℝ → Matrix ι ι ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Set.Icc a b))
    (hX : ∀ t ∈ Set.Icc a b,HasDerivAt X (F t-(L t*X t+X t*R t)) t)
    (hL : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L t i j*v j)
    (hR : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      d*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R t i j*v j) :
    (c+d)*(∫ t in a..b,‖X t‖) ≤ ‖X a‖-‖X b‖+∫ t in a..b,‖F t‖ := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := frobeniusCLM.hasFDerivAt.comp_hasDerivAt t (hX t ht)
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ⟪frobenius (X t),frobenius (F t-(L t*X t+X t*R t))⟫_ℝ ≤
        -(c+d)*‖frobenius (X t)‖^2+‖F t‖*‖frobenius (X t)‖ := by
    change ⟪frobenius (X t),frobeniusCLM (F t-(L t*X t+X t*R t))⟫_ℝ ≤ _
    rw [map_sub,inner_sub_right]
    have hco := sylvester_coercive (hL t ht) (hR t ht) (X t)
    have hcs := real_inner_le_norm (frobenius (X t)) (frobenius (F t))
    rw [frobenius_norm (F t)] at hcs
    change ⟪frobenius (X t),frobenius (F t)⟫_ℝ-
      ⟪frobenius (X t),frobenius (L t*X t+X t*R t)⟫_ℝ ≤ _
    nlinarith
  have hz (t : ℝ) (_ht : t ∈ Set.Icc a b) (hx : frobenius (X t)=0) :
      ‖frobenius (F t-(L t*X t+X t*R t))‖ ≤ ‖F t‖ := by
    have hzero : X t=0 := frobenius_injective (hx.trans (frobeniusLinear.map_zero).symm)
    simp only [hzero,mul_zero,zero_mul,add_zero,sub_zero,frobenius_norm,le_refl]
  simpa only [Function.comp_def,frobeniusCLM_apply,frobenius_norm] using
    dissipative_integral_on hab hd hF.norm he hz

/-- Uniform forced damping, with the exact exponentially decaying initial term. -/
theorem sylvester_gronwall_on {X F L R : ℝ → Matrix ι ι ℝ} {a b c d M : ℝ}
    (hX : ∀ t ∈ Set.Icc a b,HasDerivAt X (F t-(L t*X t+X t*R t)) t)
    (hF : ∀ t ∈ Set.Icc a b,‖F t‖ ≤ M)
    (hL : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L t i j*v j)
    (hR : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      d*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R t i j*v j) :
    ∀ t ∈ Set.Icc a b,‖X t‖ ≤ gronwallBound ‖X a‖ (-(c+d)) M (t-a) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := frobeniusCLM.hasFDerivAt.comp_hasDerivAt t (hX t ht)
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) :
      ⟪frobenius (X t),frobenius (F t-(L t*X t+X t*R t))⟫_ℝ ≤
        -(c+d)*‖frobenius (X t)‖^2+M*‖frobenius (X t)‖ := by
    change ⟪frobenius (X t),frobeniusCLM (F t-(L t*X t+X t*R t))⟫_ℝ ≤ _
    rw [map_sub,inner_sub_right]
    have hco := sylvester_coercive (hL t ht) (hR t ht) (X t)
    have hcs := real_inner_le_norm (frobenius (X t)) (frobenius (F t))
    rw [frobenius_norm (F t)] at hcs
    have hmul := mul_le_mul_of_nonneg_right (hF t ht) (norm_nonneg (frobenius (X t)))
    change ⟪frobenius (X t),frobenius (F t)⟫_ℝ-
      ⟪frobenius (X t),frobenius (L t*X t+X t*R t)⟫_ℝ ≤ _
    nlinarith
  have hz (t : ℝ) (ht : t ∈ Set.Icc a b) (hx : frobenius (X t)=0) :
      ‖frobenius (F t-(L t*X t+X t*R t))‖ ≤ M := by
    have hzero : X t=0 := frobenius_injective (hx.trans (frobeniusLinear.map_zero).symm)
    simpa only [hzero,mul_zero,zero_mul,add_zero,sub_zero,frobenius_norm] using hF t ht
  simpa only [Function.comp_def,frobeniusCLM_apply,frobenius_norm] using
    dissipative_gronwall_on hd he hz

/-- Integrated first-parameter error, driven by integrated VALUE error rather
than pulse duration times its initial size. This is the source's C1 mechanism. -/
theorem sylvester_jet_integrated_on {Z X ρ Q L R : ℝ → Matrix ι ι ℝ} {a b c d q : ℝ}
    (hab : a ≤ b) (hρ : ContinuousOn ρ (Set.Icc a b)) (hQ : ContinuousOn Q (Set.Icc a b)) (hX : ContinuousOn X (Set.Icc a b))
    (hZ : ∀ t ∈ Set.Icc a b,HasDerivAt Z ((ρ t-Q t*X t-X t*Q t)-(L t*Z t+Z t*R t)) t)
    (hQn : ∀ t ∈ Set.Icc a b,‖Q t‖ ≤ q)
    (hL : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L t i j*v j)
    (hR : ∀ t ∈ Set.Icc a b,∀ v : ι → ℝ,
      d*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R t i j*v j) :
    (c+d)*(∫ t in a..b,‖Z t‖) ≤
      ‖Z a‖+(∫ t in a..b,‖ρ t‖)+2*q*(∫ t in a..b,‖X t‖) := by
  have hF : ContinuousOn (fun t => ρ t-Q t*X t-X t*Q t) (Set.Icc a b) :=
    (hρ.sub (hQ.mul hX)).sub (hX.mul hQ)
  have h := sylvester_integrated_on hab hF hZ hL hR
  have hbnd : (∫ t in a..b,‖ρ t-Q t*X t-X t*Q t‖) ≤
      (∫ t in a..b,‖ρ t‖)+2*q*(∫ t in a..b,‖X t‖) := by
    have hci : ContinuousOn (fun t => ‖ρ t‖+2*q*‖X t‖) (Set.Icc a b) :=
      hρ.norm.add (continuousOn_const.mul hX.norm)
    have hi := intervalIntegral.integral_mono_on (μ := volume) hab (hF.norm.intervalIntegrable_of_Icc hab)
      (hci.intervalIntegrable_of_Icc hab) (fun t ht => jet_forcing_norm (ρ t) (Q t) (X t) (hQn t ht))
    have he : (∫ t in a..b,‖ρ t‖+2*q*‖X t‖) =
        (∫ t in a..b,‖ρ t‖)+(∫ t in a..b,2*q*‖X t‖) := by
      exact intervalIntegral.integral_add (f := fun t => ‖ρ t‖)
        (g := fun t => 2*q*‖X t‖) (hρ.norm.intervalIntegrable_of_Icc hab)
        ((continuousOn_const.mul hX.norm).intervalIntegrable_of_Icc hab)
    rw [he,intervalIntegral.integral_const_mul] at hi
    exact hi
  linarith [norm_nonneg (Z b)]

/-- Quantitative source slow-pulse estimate, retaining both integrated errors
and the smaller pointwise parameter error. Its hypotheses are the two proved
error equations and coefficient residual bounds, NOT a bound on the unknown jet.
C is a single uniform constant and T is the genuine pulse duration. -/
theorem slow_pulse_error_estimate_on
    {X Z ρ ρ₁ Q₁ L R L₁ R₁ : ℝ → Matrix ι ι ℝ}
    {a T γ c d c₁ d₁ C η : ℝ}
    (hT : 1 ≤ T) (hγ : 0 < γ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hcd : c+d=γ) (hcd₁ : c₁+d₁=γ)
    (hρ : ContinuousOn ρ (Icc a (a+T))) (hρ₁ : ContinuousOn ρ₁ (Icc a (a+T))) (hQ₁ : ContinuousOn Q₁ (Icc a (a+T)))
    (hX : ∀ t ∈ Icc a (a+T),HasDerivAt X (ρ t-(L t*X t+X t*R t)) t)
    (hZ : ∀ t ∈ Icc a (a+T),HasDerivAt Z ((ρ₁ t-Q₁ t*X t-X t*Q₁ t)-(L₁ t*Z t+Z t*R₁ t)) t)
    (hbρ : ∀ t ∈ Icc a (a+T),‖ρ t‖ ≤ C*η/T)
    (hbρ₁ : ∀ t ∈ Icc a (a+T),‖ρ₁ t‖ ≤ C*η/T)
    (hbQ₁ : ∀ t ∈ Icc a (a+T),‖Q₁ t‖ ≤ C/T)
    (hL : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      c*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L t i j*v j)
    (hR : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      d*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R t i j*v j)
    (hL₁ : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      c₁*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*L₁ t i j*v j)
    (hR₁ : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      d₁*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*R₁ t i j*v j)
    (hinit : ‖X a‖ ≤ C*η) (hzinit : Z a=0) :
    (∀ t ∈ Icc a (a+T),‖X t‖ ≤ (C+C/γ)*η) ∧
    (∫ t in a..(a+T),‖X t‖) ≤ 2*C*η/γ ∧
    (∀ t ∈ Icc a (a+T),‖Z t‖ ≤ (C+2*C*(C+C/γ))*η/(γ*T)) ∧
    (∫ t in a..(a+T),‖Z t‖) ≤ C*η/γ+4*C^2*η/γ^2 := by
  have hTpos : 0 < T := by linarith
  have hab : a ≤ a+T := by linarith
  have hXc : ContinuousOn X (Icc a (a+T)) := fun t ht => (hX t ht).continuousAt.continuousWithinAt
  have hXpoint : ∀ t ∈ Icc a (a+T),‖X t‖ ≤ (C+C/γ)*η := by
    intro t ht
    have hg := sylvester_gronwall_on hX hbρ hL hR t ht
    rw [hcd] at hg
    have hg' := damped_gronwall_bound (norm_nonneg (X a))
      (by positivity : 0 ≤ C*η/T) hγ (by linarith [ht.1] : 0 ≤ t-a)
    have htdiv : C*η/T ≤ C*η := div_le_self (by positivity) hT
    have htdiv' : (C*η/T)/γ ≤ C*η/γ := div_le_div_of_nonneg_right htdiv hγ.le
    calc
      ‖X t‖ ≤ ‖X a‖+(C*η/T)/γ := hg.trans hg'
      _ ≤ C*η+C*η/γ := add_le_add hinit htdiv'
      _ = _ := by ring
  have hI (f : ℝ → Matrix ι ι ℝ) (hf : ContinuousOn f (Icc a (a+T)))
      (hb : ∀ t ∈ Icc a (a+T),‖f t‖ ≤ C*η/T) :
      (∫ t in a..(a+T),‖f t‖) ≤ C*η := by
    have hh := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
      (hf.norm.intervalIntegrable_of_Icc hab) (continuous_const.intervalIntegrable a (a+T)) hb
    simpa only [intervalIntegral.integral_const,add_sub_cancel_left,smul_eq_mul,
      mul_div_cancel₀ _ hTpos.ne'] using hh
  have hIX : (∫ t in a..(a+T),‖X t‖) ≤ 2*C*η/γ := by
    have hh := sylvester_integrated_on hab hρ hX hL hR
    rw [hcd] at hh
    apply (le_div_iff₀ hγ).2
    nlinarith [hI ρ hρ hbρ,norm_nonneg (X (a+T))]
  have hF : ∀ t ∈ Icc a (a+T),‖ρ₁ t-Q₁ t*X t-X t*Q₁ t‖ ≤
      (C+2*C*(C+C/γ))*η/T := by
    intro t ht
    calc
      _ ≤ ‖ρ₁ t‖+2*(C/T)*‖X t‖ := jet_forcing_norm _ _ _ (hbQ₁ t ht)
      _ ≤ C*η/T+2*(C/T)*((C+C/γ)*η) := by gcongr; exact hbρ₁ t ht; exact hXpoint t ht
      _ = _ := by ring
  have hZpoint : ∀ t ∈ Icc a (a+T),‖Z t‖ ≤ (C+2*C*(C+C/γ))*η/(γ*T) := by
    intro t ht
    have hh := sylvester_gronwall_on hZ hF hL₁ hR₁ t ht
    rw [hcd₁,hzinit,norm_zero] at hh
    have hb := damped_gronwall_bound (le_refl (0:ℝ))
      (by positivity : 0 ≤ (C+2*C*(C+C/γ))*η/T) hγ (by linarith [ht.1] : 0 ≤ t-a)
    calc
      _ ≤ 0+((C+2*C*(C+C/γ))*η/T)/γ := hh.trans hb
      _ = _ := by ring
  refine ⟨hXpoint,hIX,hZpoint,?_⟩
  have hh := sylvester_jet_integrated_on hab hρ₁ hQ₁ hXc hZ hbQ₁ hL₁ hR₁
  rw [hcd₁,hzinit,norm_zero,zero_add] at hh
  have hq : 0 ≤ C/T := by positivity
  have hstep : γ*(∫ t in a..(a+T),‖Z t‖) ≤ C*η+2*(C/T)*(2*C*η/γ) := by
    exact hh.trans (add_le_add (hI ρ₁ hρ₁ hbρ₁) (mul_le_mul_of_nonneg_left hIX (by positivity)))
  have hCT : C/T ≤ C := div_le_self hC hT
  have hmul := mul_le_mul_of_nonneg_right hCT (show 0 ≤ 4*C*η/γ by positivity)
  have hstep' : (∫ t in a..(a+T),‖Z t‖) ≤ (C*η+2*(C/T)*(2*C*η/γ))/γ :=
    (le_div_iff₀ hγ).2 (by simpa only [mul_comm] using hstep)
  calc
    _ ≤ (C*η+2*(C/T)*(2*C*η/γ))/γ  := hstep'
    _ ≤ (C*η+4*C^2*η/γ)/γ := by
      apply div_le_div_of_nonneg_right _ hγ.le
      have he₁ : 2*(C/T)*(2*C*η/γ)=(C/T)*(4*C*η/γ) := by ring
      have he₂ : 4*C^2*η/γ=C*(4*C*η/γ) := by ring
      rw [he₁,he₂]
      exact add_le_add_right hmul _
    _ = _ := by field_simp


end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set

namespace HarmonicCounterexample.LinearODE
open Matrix Set
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- Uniform-history L1 value and first-jet error for the ACTUAL center-regular
Peano--Baker solution. Coercivity of the unknown Riccati solution is PRODUCED
from positivity and its Euclidean core; neither a solution nor an unknown-jet
bound is supplied as a hypothesis. The comparison residuals are explicit. -/
theorem actual_slow_pulse_integrated_on (basis : OrthonormalBasis ι ℝ E)
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (p h : H)
    (hA : Continuous (A p)) (hb : Continuous b) (hB' : Continuous (B' p))
    (hA' : Continuous (fun t => A' p t h))
    (hBeval : ∀ t z v,B' p t z v=(0,A' p t z*v.1))
    {M MA Mb : ℝ} (hM : 0 ≤ M) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnB : ∀ t,‖block (leftAction (A p)) b t‖ ≤ M) (hnB' : ∀ t,‖B' p t‖ ≤ M)
    (hnA : ∀ t,‖A p t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hAp : ∀ t x,0 ≤ inner ℝ x (A p t x))
    {l B : ℝ} (hl : 0 < l) (hAc : ∀ t ≤ 0,∀ x,A p t x=(l*(l+B)) • x)
    (hbc : ∀ t ≤ 0,b t=B)
    (Q Qdot Qh Qhdot : ℝ → Matrix ι ι ℝ)
    {a T γ C η : ℝ}
    (hdQ : ∀ t ∈ Icc a (a+T),HasDerivAt Q (Qdot t) t)
    (hdQh : ∀ t ∈ Icc a (a+T),HasDerivAt Qh (Qhdot t) t)
    (hcQdot : ContinuousOn Qdot (Icc a (a+T)))
    (hcQhdot : ContinuousOn Qhdot (Icc a (a+T)))
    (ha : 0 ≤ a) (hT : 1 ≤ T) (hγ : 0 < γ)
    (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hbl : ∀ t ∈ Icc a (a+T),γ ≤ b t)
    (hQpos : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      0 ≤ ∑ i,∑ j,v i*Q t i j*v j)
    (hρ : ∀ t ∈ Icc a (a+T),
      ‖orthogonalMatrix basis (A p t)-b t • Q t-Q t*Q t-Qdot t‖ ≤ C*η/T)
    (hρh : ∀ t ∈ Icc a (a+T),
      ‖orthogonalMatrix basis (A' p t h)-b t • Qh t-Qh t*Q t-Q t*Qh t-Qhdot t‖ ≤ C*η/T)
    (hQhn : ∀ t ∈ Icc a (a+T),‖Qh t‖ ≤ C/T)
    (hinit : ‖orthogonalMatrix basis (slope (A p) b l a)-Q a‖ ≤ C*η)
    (hjetinit : orthogonalMatrix basis (slopeJet A b B' l p a h)=Qh a) :
    (∫ t in a..a+T,‖orthogonalMatrix basis (slope (A p) b l t)-Q t‖) ≤ 2*C*η/γ ∧
    (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b B' l p t h)-Qh t‖) ≤
      C*η/γ+4*C^2*η/γ^2 := by
  let P := fun t => orthogonalMatrix basis (slope (A p) b l t)
  let Ph := fun t => orthogonalMatrix basis (slopeJet A b B' l p t h)
  let ρ := fun t => orthogonalMatrix basis (A p t)-b t • Q t-Q t*Q t-Qdot t
  let ρh := fun t => orthogonalMatrix basis (A' p t h)-b t • Qh t-Qh t*Q t-Q t*Qh t-Qhdot t
  have hu := actual_value_unit_all_time hA hb hMA hMb hnA hnb hAp hl hAc hbc
  have hdP (t : ℝ) : HasDerivAt P
      (orthogonalMatrix basis (A p t)-b t • P t-P t*P t) t :=
    orthogonalMatrix_riccati_deriv basis (slope_deriv hA hb hMA hMb hnA hnb l t (hu t))
  have hdPh (t : ℝ) : HasDerivAt Ph
      (orthogonalMatrix basis (A' p t h)-b t • Ph t-P t*Ph t-Ph t*P t) t :=
    orthogonalMatrix_jet_deriv basis (slopeJet_hasDerivAt_pointwise A b B' A' p h
      hA hb hB' hBeval hM hMA hMb hnB hnB' hnA hnb l t (hu t))
  have hcQ : ContinuousOn Q (Icc a (a+T)) := fun t ht => (hdQ t ht).continuousAt.continuousWithinAt
  have hcQh : ContinuousOn Qh (Icc a (a+T)) := fun t ht => (hdQh t ht).continuousAt.continuousWithinAt
  have hcρ : ContinuousOn ρ (Icc a (a+T)) :=
    ((((orthogonalMatrix basis).continuous.comp hA).continuousOn.sub (hb.continuousOn.smul hcQ)).sub
      (hcQ.mul hcQ)).sub hcQdot
  have hcρh : ContinuousOn ρh (Icc a (a+T)) :=
    (((((orthogonalMatrix basis).continuous.comp hA').continuousOn.sub (hb.continuousOn.smul hcQh)).sub
      (hcQh.mul hcQ)).sub (hcQ.mul hcQh)).sub hcQhdot
  have hPpos (t : ℝ) (ht : t ∈ Icc a (a+T)) (v : ι → ℝ) :
      0 ≤ ∑ i,∑ j,v i*P t i j*v j := by
    have he := orthogonalMatrix_coercive basis (slope (A p) b l t) (c := 0)
      (fun x => by simpa only [zero_mul] using
        slope_nonnegative hA hb hMA hMb hnA hnb hAp hl (ha.trans ht.1) (hu t) x) v
    simpa only [zero_mul] using he
  have hL (t : ℝ) (ht : t ∈ Icc a (a+T)) (v : ι → ℝ) :
      γ*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*(b t • (1:Matrix ι ι ℝ)+P t) i j*v j := by
    rw [quadratic_add,quadratic_scalar_one]
    have he := mul_le_mul_of_nonneg_right (hbl t ht)
      (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (v i))
    linarith [hPpos t ht v]
  have he := slow_pulse_error_estimate_on (c := γ) (d := 0) (c₁ := γ) (d₁ := 0)
    hT hγ hC hη (add_zero γ) (add_zero γ) hcρ hcρh hcQh
    (fun t ht => riccati_error_deriv (hdP t) (hdQ t ht))
    (fun t ht => riccati_error_jet_deriv (hdPh t) (hdQh t ht))
    hρ hρh hQhn hL
    (fun t ht v => by simpa only [zero_mul] using hQpos t ht v)
    hL (fun t ht v => by simpa only [zero_mul] using hPpos t ht v)
    hinit (sub_eq_zero.2 hjetinit)
  exact ⟨he.2.1,he.2.2.2⟩


theorem actual_slow_pulse_estimates_on (basis : OrthonormalBasis ι ℝ E)
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (p h : H)
    (hA : Continuous (A p)) (hb : Continuous b) (hB' : Continuous (B' p))
    (hA' : Continuous (fun t => A' p t h))
    (hBeval : ∀ t z v,B' p t z v=(0,A' p t z*v.1))
    {M MA Mb : ℝ} (hM : 0 ≤ M) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnB : ∀ t,‖block (leftAction (A p)) b t‖ ≤ M) (hnB' : ∀ t,‖B' p t‖ ≤ M)
    (hnA : ∀ t,‖A p t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hAp : ∀ t x,0 ≤ inner ℝ x (A p t x))
    {l B : ℝ} (hl : 0 < l) (hAc : ∀ t ≤ 0,∀ x,A p t x=(l*(l+B)) • x)
    (hbc : ∀ t ≤ 0,b t=B)
    (Q Qdot Qh Qhdot : ℝ → Matrix ι ι ℝ)
    {a T γ C η : ℝ}
    (hdQ : ∀ t ∈ Icc a (a+T),HasDerivAt Q (Qdot t) t)
    (hdQh : ∀ t ∈ Icc a (a+T),HasDerivAt Qh (Qhdot t) t)
    (hcQdot : ContinuousOn Qdot (Icc a (a+T)))
    (hcQhdot : ContinuousOn Qhdot (Icc a (a+T)))
    (ha : 0 ≤ a) (hT : 1 ≤ T) (hγ : 0 < γ)
    (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hbl : ∀ t ∈ Icc a (a+T),γ ≤ b t)
    (hQpos : ∀ t ∈ Icc a (a+T),∀ v : ι → ℝ,
      0 ≤ ∑ i,∑ j,v i*Q t i j*v j)
    (hρ : ∀ t ∈ Icc a (a+T),
      ‖orthogonalMatrix basis (A p t)-b t • Q t-Q t*Q t-Qdot t‖ ≤ C*η/T)
    (hρh : ∀ t ∈ Icc a (a+T),
      ‖orthogonalMatrix basis (A' p t h)-b t • Qh t-Qh t*Q t-Q t*Qh t-Qhdot t‖ ≤ C*η/T)
    (hQhn : ∀ t ∈ Icc a (a+T),‖Qh t‖ ≤ C/T)
    (hinit : ‖orthogonalMatrix basis (slope (A p) b l a)-Q a‖ ≤ C*η)
    (hjetinit : orthogonalMatrix basis (slopeJet A b B' l p a h)=Qh a) :
    (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slope (A p) b l t)-Q t‖ ≤ (C+C/γ)*η) ∧
    (∫ t in a..a+T,‖orthogonalMatrix basis (slope (A p) b l t)-Q t‖) ≤ 2*C*η/γ ∧
    (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slopeJet A b B' l p t h)-Qh t‖ ≤
      (C+2*C*(C+C/γ))*η/(γ*T)) ∧
    (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b B' l p t h)-Qh t‖) ≤
      C*η/γ+4*C^2*η/γ^2 := by
  let P := fun t => orthogonalMatrix basis (slope (A p) b l t)
  let Ph := fun t => orthogonalMatrix basis (slopeJet A b B' l p t h)
  let ρ := fun t => orthogonalMatrix basis (A p t)-b t • Q t-Q t*Q t-Qdot t
  let ρh := fun t => orthogonalMatrix basis (A' p t h)-b t • Qh t-Qh t*Q t-Q t*Qh t-Qhdot t
  have hu := actual_value_unit_all_time hA hb hMA hMb hnA hnb hAp hl hAc hbc
  have hdP (t : ℝ) : HasDerivAt P
      (orthogonalMatrix basis (A p t)-b t • P t-P t*P t) t :=
    orthogonalMatrix_riccati_deriv basis (slope_deriv hA hb hMA hMb hnA hnb l t (hu t))
  have hdPh (t : ℝ) : HasDerivAt Ph
      (orthogonalMatrix basis (A' p t h)-b t • Ph t-P t*Ph t-Ph t*P t) t :=
    orthogonalMatrix_jet_deriv basis (slopeJet_hasDerivAt_pointwise A b B' A' p h
      hA hb hB' hBeval hM hMA hMb hnB hnB' hnA hnb l t (hu t))
  have hcQ : ContinuousOn Q (Icc a (a+T)) := fun t ht => (hdQ t ht).continuousAt.continuousWithinAt
  have hcQh : ContinuousOn Qh (Icc a (a+T)) := fun t ht => (hdQh t ht).continuousAt.continuousWithinAt
  have hcρ : ContinuousOn ρ (Icc a (a+T)) :=
    ((((orthogonalMatrix basis).continuous.comp hA).continuousOn.sub (hb.continuousOn.smul hcQ)).sub
      (hcQ.mul hcQ)).sub hcQdot
  have hcρh : ContinuousOn ρh (Icc a (a+T)) :=
    (((((orthogonalMatrix basis).continuous.comp hA').continuousOn.sub (hb.continuousOn.smul hcQh)).sub
      (hcQh.mul hcQ)).sub (hcQ.mul hcQh)).sub hcQhdot
  have hPpos (t : ℝ) (ht : t ∈ Icc a (a+T)) (v : ι → ℝ) :
      0 ≤ ∑ i,∑ j,v i*P t i j*v j := by
    have he := orthogonalMatrix_coercive basis (slope (A p) b l t) (c := 0)
      (fun x => by simpa only [zero_mul] using
        slope_nonnegative hA hb hMA hMb hnA hnb hAp hl (ha.trans ht.1) (hu t) x) v
    simpa only [zero_mul] using he
  have hL (t : ℝ) (ht : t ∈ Icc a (a+T)) (v : ι → ℝ) :
      γ*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*(b t • (1:Matrix ι ι ℝ)+P t) i j*v j := by
    rw [quadratic_add,quadratic_scalar_one]
    have he := mul_le_mul_of_nonneg_right (hbl t ht)
      (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (v i))
    linarith [hPpos t ht v]
  have he := slow_pulse_error_estimate_on (c := γ) (d := 0) (c₁ := γ) (d₁ := 0)
    hT hγ hC hη (add_zero γ) (add_zero γ) hcρ hcρh hcQh
    (fun t ht => riccati_error_deriv (hdP t) (hdQ t ht))
    (fun t ht => riccati_error_jet_deriv (hdPh t) (hdQh t ht))
    hρ hρh hQhn hL
    (fun t ht v => by simpa only [zero_mul] using hQpos t ht v)
    hL (fun t ht v => by simpa only [zero_mul] using hPpos t ht v)
    hinit (sub_eq_zero.2 hjetinit)
  exact he

end HarmonicCounterexample.LinearODE

end

end OAI
