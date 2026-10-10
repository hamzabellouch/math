import OAI.Analysis.Littlewood.Cutoff

namespace OAI

universe uI uZ

namespace AsymptoticallyMinimalLittlewood
namespace QuadraticTail
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

def phase (t u x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2*Real.pi*(t*x^2/2-u*x) : ℝ))

def amp (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  g x / ((t*x-u : ℝ) : ℂ)^k

def osc (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) : ℂ :=
  ∫ x : ℝ, amp g t u k x * phase t u x

lemma phase_norm (t u x : ℝ) : ‖phase t u x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]

lemma phase_smooth (t u : ℝ) : ContDiff ℝ ∞ (phase t u) := by
  have hc : ContDiff ℝ ∞ (fun x : ℝ ↦ 2*Real.pi*(t*x^2/2-u*x)) := by fun_prop
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ Complex.I)).mul
    (Complex.ofRealCLM.contDiff.comp hc)).cexp

lemma phase_deriv (t u x : ℝ) : HasDerivAt (phase t u)
    (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x) x := by
  have hr : HasDerivAt (fun y : ℝ ↦ 2*Real.pi*(t*y^2/2-u*y))
      (2*Real.pi*(t*x-u)) x := by
    convert (((((hasDerivAt_id x).pow 2).const_mul t).div_const 2).sub
      ((hasDerivAt_id x).const_mul u)).const_mul (2*Real.pi) using 1 <;> first | rfl | (dsimp; ring)
  have hh := (hr.ofReal_comp.const_mul Complex.I).cexp
  change HasDerivAt (phase t u) _ x at hh
  convert hh using 1
  dsimp only [phase]
  push_cast
  ring

lemma amp_smooth {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (t u : ℝ) (k : ℕ)
    (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) : ContDiff ℝ ∞ (amp g t u k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases h : t*x-u = 0
  · have hx : x ∉ tsupport g := fun hx ↦ havoid x hx h
    rw [notMem_tsupport_iff_eventuallyEq] at hx
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (0:ℂ)) x).congr_of_eventuallyEq
    filter_upwards [hx] with y hy
    simp [amp, hy]
  · have hr : ContDiff ℝ ∞ (fun y : ℝ ↦ t*y-u) := by fun_prop
    have hd : ContDiff ℝ ∞ (fun y : ℝ ↦ ((t*y-u : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hr
    simpa only [amp, div_eq_mul_inv, Pi.inv_apply] using! hg.contDiffAt.mul
      ((hd.contDiffAt.pow k).inv (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h)))

lemma amp_support (g : ℝ → ℂ) (t u : ℝ) (k : ℕ) :
    tsupport (amp g t u k) ⊆ tsupport g := by
  apply closure_mono
  intro x hx
  change amp g t u k x ≠ 0 at hx
  change g x ≠ 0
  intro h
  exact hx (by simp [amp, h])

lemma amp_compact {g : ℝ → ℂ} (hg : HasCompactSupport g) (t u : ℝ) (k : ℕ) :
    HasCompactSupport (amp g t u k) :=
  hg.mono' ((subset_tsupport _).trans (amp_support g t u k))

lemma amp_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (t u : ℝ) (k : ℕ)
    (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) (x : ℝ) :
    HasDerivAt (amp g t u (k+1))
      (amp (deriv g) t u (k+1) x - ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x) x := by
  by_cases h : t*x-u = 0
  · have hx : x ∉ tsupport g := fun hx ↦ havoid x hx h
    have hz : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hd : deriv g x = 0 := by
      exact (hz.hasDerivAt_iff.mpr (hasDerivAt_const x (0 : ℂ))).deriv
    simp only [amp, hd, h, Complex.ofReal_zero, zero_pow (by omega : k+1 ≠ 0),
      zero_pow (by omega : k+2 ≠ 0), div_zero, mul_zero, sub_zero]
    apply (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [amp, hy]
  · have hd : HasDerivAt (fun y : ℝ ↦ ((t*y-u : ℝ) : ℂ)) (t : ℂ) x := by
      simpa using (((hasDerivAt_id x).const_mul t).sub_const u).ofReal_comp
    have hh := (hg.differentiable (by norm_num) x).hasDerivAt.div (hd.pow (k+1))
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h))
    change HasDerivAt (amp g t u (k+1)) _ x at hh
    convert hh using 1
    simp only [amp, Pi.pow_apply, Nat.add_sub_cancel]
    have hc : ((t*x-u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
    rw [show k+2=(k+1)+1 by omega, pow_succ, pow_succ]
    field_simp [hc]
    ring

lemma osc_integrable {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (t u : ℝ) (k : ℕ) (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) :
    Integrable (fun x ↦ amp g t u k x * phase t u x) :=
  ((amp_smooth hgs t u k havoid).continuous.mul (phase_smooth t u).continuous).integrable_of_hasCompactSupport
    ((amp_compact hg t u k).mul_right)

lemma osc_parts {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (t u : ℝ) (k : ℕ) (havoid : ∀ x ∈ tsupport g, t*x-u ≠ 0) :
    (2*Real.pi*Complex.I)*osc g t u k =
      -(osc (deriv g) t u (k+1) - ((k+1 : ℕ) : ℂ)*(t : ℂ)*osc g t u (k+2)) := by
  have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hgs).2
  have havd : ∀ x ∈ tsupport (deriv g), t*x-u ≠ 0 :=
    fun x hx ↦ havoid x (tsupport_deriv_subset hx)
  have hi1 := osc_integrable hg hgs t u k havoid
  have hi2 := osc_integrable hg.deriv hgd t u (k+1) havd
  have hi3 := osc_integrable hg hgs t u (k+2) havoid
  have hprod (x : ℝ) : amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x) =
      (2*Real.pi*Complex.I)*(amp g t u k x*phase t u x) := by
    by_cases h : t*x-u=0
    · have hx : g x=0 := Function.notMem_support.mp (fun hx ↦ havoid x (subset_tsupport _ hx) h)
      simp [amp, hx]
    · dsimp [amp]
      have hc : ((t*x-u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h
      rw [pow_succ]
      field_simp [hc]
  have hprod2 (x : ℝ) : (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x =
      amp (deriv g) t u (k+1) x*phase t u x -
      (((k+1 : ℕ) : ℂ)*(t : ℂ))*(amp g t u (k+2) x*phase t u x) := by ring
  have hh := MeasureTheory.integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.mul ℝ ℂ)
    (fun x _ ↦ amp_deriv hgs t u k havoid x)
    (fun x _ ↦ phase_deriv t u x)
    (show Integrable (fun x ↦ amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x)) volume by
      simp_rw [hprod]; exact hi1.const_mul _)
    (show Integrable (fun x ↦ (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x) volume by
      simp_rw [hprod2]; exact hi2.sub (hi3.const_mul _))
    (osc_integrable hg hgs t u (k+1) havoid)
  change (∫ x : ℝ, amp g t u (k+1) x *
      (2*Real.pi*Complex.I*((t*x-u : ℝ) : ℂ)*phase t u x)) =
    -(∫ x : ℝ, (amp (deriv g) t u (k+1) x -
      ((k+1 : ℕ) : ℂ)*(t : ℂ)*amp g t u (k+2) x)*phase t u x) at hh
  simp_rw [hprod, hprod2] at hh
  rw [integral_const_mul, integral_sub hi2 (hi3.const_mul _), integral_const_mul] at hh
  exact hh

lemma osc_bound_zero {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {c M : ℝ} (hc : 0 < c) (hM : 0 < M) (t u : ℝ) (k : ℕ)
    (hsep : ∀ x ∈ tsupport g, c*M ≤ |t*x-u|) :
    M^k * ‖osc g t u k‖ ≤ (∫ x : ℝ, ‖g x‖) / c^k := by
  have hav : ∀ x ∈ tsupport g, t*x-u ≠ 0 := by
    intro x hx hz
    have := hsep x hx
    rw [hz, abs_zero] at this
    nlinarith [mul_pos hc hM]
  have hi := osc_integrable hg hgs t u k hav
  have hpoint (x : ℝ) : M^k * ‖amp g t u k x*phase t u x‖ ≤ ‖g x‖ / c^k := by
    by_cases hx : g x=0
    · simp [amp, hx]
    · have hx' := subset_tsupport g hx
      have hz : 0 < |t*x-u| := lt_of_lt_of_le (mul_pos hc hM) (hsep x hx')
      rw [norm_mul, phase_norm, mul_one, amp, norm_div, norm_pow, Complex.norm_real]
      rw [Real.norm_eq_abs, ← mul_div_assoc, div_le_div_iff₀ (pow_pos hz _) (pow_pos hc _)]
      have hp := pow_le_pow_left₀ (le_of_lt (mul_pos hc hM)) (hsep x hx') k
      rw [mul_pow] at hp
      nlinarith [mul_le_mul_of_nonneg_left hp (norm_nonneg (g x))]
  calc
    M^k * ‖osc g t u k‖ ≤ M^k * ∫ x : ℝ, ‖amp g t u k x*phase t u x‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (pow_nonneg hM.le _)
    _ = ∫ x : ℝ, M^k * ‖amp g t u k x*phase t u x‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ x : ℝ, ‖g x‖ / c^k := integral_mono (hi.norm.const_mul _)      ((hgs.continuous.norm.integrable_of_hasCompactSupport hg.norm).div_const _) hpoint
    _ = (∫ x : ℝ, ‖g x‖) / c^k := integral_div _ _

/-- Uniform repeated nonstationary integration by parts, with the support condition
on the actual amplitude. The parameters may vary, but c and B stay fixed. -/
theorem polynomial_decay (l : ℕ) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B) :
    ∀ (g : ℝ → ℂ), HasCompactSupport g → ContDiff ℝ ∞ g → ∀ k : ℕ,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t u M : ℝ), 0 < M → |t| ≤ B*M →
      (∀ x ∈ tsupport g, c*M ≤ |t*x-u|) → M^(k+l)*‖osc g t u k‖ ≤ C := by
  induction l with
  | zero =>
      intro g hg hgs k
      refine ⟨(∫ x : ℝ, ‖g x‖)/c^k, div_nonneg (integral_nonneg (fun x ↦ norm_nonneg _))
        (pow_nonneg hc.le _), ?_⟩
      intro t u M hM ht hs
      simpa using osc_bound_zero hg hgs hc hM t u k hs
  | succ l ih =>
      intro g hg hgs k
      have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hgs).2
      obtain ⟨C1, hC1, h1⟩ := ih (deriv g) hg.deriv hgd (k+1)
      obtain ⟨C2, hC2, h2⟩ := ih g hg hgs (k+2)
      refine ⟨(C1+(k+1)*B*C2)/(2*Real.pi), by positivity, ?_⟩
      intro t u M hM ht hs
      have hav : ∀ x ∈ tsupport g, t*x-u ≠ 0 := by
        intro x hx hz
        have := hs x hx
        rw [hz, abs_zero] at this
        nlinarith [mul_pos hc hM]
      have hs' : ∀ x ∈ tsupport (deriv g), c*M ≤ |t*x-u| :=
        fun x hx ↦ hs x (tsupport_deriv_subset hx)
      have hh1 := h1 t u M hM ht hs'
      have hh2 := h2 t u M hM ht hs
      have hnorm : (2*Real.pi)*‖osc g t u k‖ ≤
          ‖osc (deriv g) t u (k+1)‖+(k+1)*|t| * ‖osc g t u (k+2)‖ := by
        have he := congrArg norm (osc_parts hg hgs t u k hav)
        have htriangle := norm_sub_le (osc (deriv g) t u (k+1))
          (((k+1 : ℕ) : ℂ)*(t : ℂ)*osc g t u (k+2))
        simp only [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_natCast] at he htriangle
        push_cast at he htriangle
        linarith
      have hterm : M^(k+l+1)*|t| * ‖osc g t u (k+2)‖ ≤ B*C2 := by
        calc
          _ ≤ M^(k+l+1)*(B*M)*‖osc g t u (k+2)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (pow_nonneg hM.le _)) (norm_nonneg _)
          _ = B*(M^(k+2+l)*‖osc g t u (k+2)‖) := by
            rw [show k+2+l=(k+l+1)+1 by omega, pow_succ]; ring
          _ ≤ B*C2 := mul_le_mul_of_nonneg_left hh2 hB
      rw [le_div_iff₀ (by positivity : 0 < 2*Real.pi)]
      have hp := mul_le_mul_of_nonneg_left hnorm (pow_nonneg hM.le (k+l+1))
      have hk : (0:ℝ) ≤ k+1 := by positivity
      have hterm' := mul_le_mul_of_nonneg_left hterm hk
      have e1 : k+1+l=k+l+1 := by omega
      rw [e1] at hh1
      have e2 : k+(l+1)=k+l+1 := by omega
      rw [e2]
      nlinarith only [hp, hh1, hterm']

/-- Off-box decay in precisely the regime used to truncate the spread spectrum. -/
theorem offbox_decay {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {α β : ℝ} (hα : 0 ≤ α) (hα' : α < 1/2) (hβ : β ≠ 0)
    (hsupp : tsupport g ⊆ Set.Icc (-α) α) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T w : ℝ, 0 < T → T*|β|/2 < |w| →
      (T+|w|)^l * ‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C := by
  let c : ℝ := (1-2*α)/(1+2/|β|)
  have hb : 0 < |β| := abs_pos.mpr hβ
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith) (by positivity)
  obtain ⟨C,hC,htail⟩ := polynomial_decay l c |β| hc (abs_nonneg _) g hg hgs 0
  refine ⟨C,hC,?_⟩
  intro T w hT hw
  have hM : 0 < T+|w| := by positivity
  have ht : |T*β| ≤ |β| *(T+|w|) := by
    rw [abs_mul, abs_of_pos hT]; nlinarith [mul_nonneg (abs_nonneg β) (abs_nonneg w)]
  have hs : ∀ x ∈ tsupport g, c*(T+|w|) ≤ |T*β*x-w| := by
    intro x hx
    have hx' : |x| ≤ α := abs_le.mpr (hsupp hx)
    have h1 : c*(T+|w|) ≤ (1-2*α)*|w| := by
      dsimp [c]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1+2/|β|)]
      have hw' : T ≤ 2*|w|/|β| := by rw [le_div_iff₀ hb]; linarith
      have hh := mul_le_mul_of_nonneg_left hw' (by linarith : 0 ≤ 1-2*α)
      convert add_le_add_right hh ((1-2*α)*|w|) using 1 <;> ring
    have hab : |T*β*x| ≤ T*|β| *α := by
      rw [abs_mul, abs_mul, abs_of_pos hT]
      exact mul_le_mul_of_nonneg_left hx' (by positivity)
    have htri : |w| ≤ |T*β*x-w| + |T*β*x| := by
      have hh := abs_add_le (w-T*β*x) (T*β*x)
      rw [sub_add_cancel, abs_sub_comm] at hh
      exact hh
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hw) hα
    linarith
  have hh := htail (T*β) w (T+|w|) hM ht hs
  simpa [osc, amp] using hh

lemma phase_fourier (t x : ℝ) (w : ℤ) :
    fourier (-w) (x : UnitAddCircle) * phase t 0 x = phase t w x := by
  rw [fourier_coe_apply, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma cutoff_zero {g : ℝ → ℂ} {α x : ℝ}
    (hs : tsupport g ⊆ Set.Icc (-α) α) (hx : x ∉ Set.Icc (-α) α) : g x=0 :=
  image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))

def circleChirp (g : ℝ → ℂ) (t : ℝ) : UnitAddCircle → ℂ :=
  AddCircle.liftIoc 1 (-1/2) (fun x ↦ g x*phase t 0 x)

lemma circleChirp_continuous {g : ℝ → ℂ} (hg : Continuous g) {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    Continuous (circleChirp g t) := by
  apply AddCircle.liftIoc_continuous
  · have hleft : g (-1/2)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    have hright : g (-1/2+1)=0 := cutoff_zero hs (by intro h; rcases h with ⟨h1,h2⟩; linarith)
    simp only [hleft,hright,zero_mul]
  · exact (hg.mul (phase_smooth t 0).continuous).continuousOn

lemma circleChirp_coefficient {g : ℝ → ℂ} {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) (w : ℤ) :
    fourierCoeff (circleChirp g t) w = ∫ x : ℝ, g x*phase t w x := by
  rw [fourierCoeff_eq_intervalIntegral _ w (-1/2)]
  simp only [div_self (one_ne_zero : (1:ℝ) ≠ 0), one_smul]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤ -1/2+1)]
  calc
    _ = ∫ x in Set.Ioc (-1/2:ℝ) (-1/2+1), g x*phase t w x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only [circleChirp]
      rw [AddCircle.liftIoc_coe_apply hx, smul_eq_mul]
      calc
        _ = g x*(fourier (-w) (x : UnitAddCircle)*phase t 0 x) := by ring
        _ = _ := by rw [phase_fourier]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : g x=0 := cutoff_zero hs (by
        intro ⟨hx1,hx2⟩
        apply hx
        constructor <;> linarith)
      rw [hz,zero_mul]

def latticeWeight (w : ℤ) : ℝ := 1/(1+|(w:ℝ)|)^2

lemma latticeWeight_pos (w : ℤ) : 0 < latticeWeight w := by
  dsimp [latticeWeight]
  positivity

lemma latticeWeight_summable : Summable latticeWeight := by
  have hn : Summable (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using h
  have hpos : (fun n : ℕ ↦ latticeWeight (n : ℤ)) = (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    funext n
    simp [latticeWeight]
  have hneg : (fun n : ℕ ↦ latticeWeight (-(n : ℤ))) = (fun n : ℕ ↦ 1/(1+(n:ℝ))^2) := by
    funext n
    simp [latticeWeight]
  exact Summable.of_nat_of_neg (hpos ▸ hn) (hneg ▸ hn)

noncomputable def box (T β : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋

lemma mem_box (T β : ℝ) (w : ℤ) :
    w ∈ box T β ↔ |(w:ℝ)| ≤ T*|β|/2 := by
  rw [box, Finset.mem_Icc, ← abs_le, ← Int.cast_abs, ← Int.le_floor]

lemma box_card_le {T : ℝ} (hT : 0≤T) (β : ℝ) :
    ((box T β).card : ℝ) ≤ T*|β|+1 := by
  have hfloor : 0 ≤ ⌊T*|β|/2⌋ := Int.floor_nonneg.mpr (by positivity)
  have hc := Int.card_Icc_of_le (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋ (show -⌊T*|β|/2⌋ ≤ ⌊T*|β|/2⌋+1 by omega)
  have hcR : ((box T β).card : ℝ) = 2*(⌊T*|β|/2⌋ : ℝ)+1 := by
    simp only [box]
    exact_mod_cast (by omega : (Finset.Icc (-⌊T*|β|/2⌋) ⌊T*|β|/2⌋).card =
      (2*⌊T*|β|/2⌋+1 : ℤ))
  rw [hcR]
  linarith [Int.floor_le (T*|β|/2)]

/-- A summable majorant for the discarded one-dimensional Fourier tail.
This uses three integrations by parts (or n+2 for the stronger form), and
avoids an unjustified summation of stationary-phase errors. -/
theorem offbox_weighted {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) {β : ℝ} (hβ : β ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ w : ℤ, w ∉ box T β →
      ‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C / T^n * latticeWeight w := by
  obtain ⟨C,hC,hbound⟩ := offbox_decay hg hgs hα0 hα hβ hs (n+2)
  refine ⟨C,hC,?_⟩
  intro T hT w hw
  have hTpos : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hw' : T*|β|/2 < |(w:ℝ)| := lt_of_not_ge (by simpa only [← mem_box] using hw)
  have hb := hbound T w hTpos hw'
  have hp : T^n*(1+|(w:ℝ)|)^2 ≤ (T+|(w:ℝ)|)^(n+2) := by
    rw [pow_add]
    apply mul_le_mul
    · exact pow_le_pow_left₀ hTpos.le (le_add_of_nonneg_right (abs_nonneg _)) n
    · exact pow_le_pow_left₀ (by positivity) (by linarith : 1+|(w:ℝ)|≤T+|(w:ℝ)|) 2
    · positivity
    · positivity
  have hh : T^n*(1+|(w:ℝ)|)^2*‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hb
  dsimp only [latticeWeight]
  calc
    _ ≤ C/(T^n*(1+|(w:ℝ)|)^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hh])
    _ = _ := by rw [div_mul_eq_div_div]; ring

lemma circle_fourier_norm (w : ℤ) (z : UnitAddCircle) : ‖fourier w z‖=1 :=
  Circle.norm_coe _

/-- Uniform truncation from a summable majorant outside one finite box. -/
lemma fourier_truncation_error (f : C(UnitAddCircle,ℂ)) (S : Finset ℤ)
    (b : ℤ → ℝ) (hb : Summable b) (hb0 : ∀ w, 0≤b w)
    (hbound : ∀ w, w ∉ S → ‖fourierCoeff f w‖ ≤ b w) (z : UnitAddCircle) :
    ‖(∑ w ∈ S, fourierCoeff f w*fourier w z)-f z‖ ≤ ∑' w, b w := by
  classical
  have hcomp : Summable (fun w : {w : ℤ // w ∉ S} ↦ fourierCoeff f w.val) := by
    exact (hb.subtype _).of_norm_bounded (fun w ↦ hbound w.val w.property)
  have hh : Summable (fourierCoeff f) := (S.summable_compl_iff).mp hcomp
  have hs := has_pointwise_sum_fourier_series_of_summable hh z
  simp only [smul_eq_mul] at hs
  have hterm := hs.summable
  have he := hterm.sum_add_tsum_compl (s := S)
  rw [hs.tsum_eq] at he
  change (∑ w ∈ S, fourierCoeff f w*fourier w z) +
    (∑' w : {w : ℤ // w ∉ S}, fourierCoeff f w.val*fourier w.val z) = f z at he
  have heq : (∑ w ∈ S, fourierCoeff f w*fourier w z)-f z =
      -(∑' w : {w : ℤ // w ∉ S}, fourierCoeff f w.val*fourier w.val z) := by
    linear_combination he
  rw [heq, norm_neg]
  have hbc : Summable (fun w : {w : ℤ // w ∉ S} ↦ b w.val) := hb.subtype _
  calc
    _ ≤ ∑' w : {w : ℤ // w ∉ S}, b w.val := by
      apply ((hterm.subtype _).hasSum).norm_le_of_bounded hbc.hasSum
      intro w
      change ‖fourierCoeff f w.val * fourier w.val z‖ ≤ b w.val
      rw [norm_mul, circle_fourier_norm, mul_one]
      exact hbound w.val w.property
    _ ≤ ∑' w, b w := by
      exact hbc.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun w _ ↦ hb0 w) (fun _ ↦ le_rfl) hb

def rowTrunc (g : ℝ → ℂ) (T β : ℝ) (z : UnitAddCircle) : ℂ :=
  ∑ w ∈ box T β, (∫ x : ℝ, g x*phase (T*β) w x)*fourier w z

theorem rowTrunc_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ z : UnitAddCircle,
      ‖rowTrunc g T β z-circleChirp g (T*β) z‖ ≤ C/T := by
  obtain ⟨C,hC,hbound⟩ := offbox_weighted hg hgs hα0 hα hs hβ 1
  refine ⟨C*(∑' w, latticeWeight w),mul_nonneg hC (tsum_nonneg (fun w ↦ (latticeWeight_pos w).le)),?_⟩
  intro T hT z
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs.continuous hα hs _⟩
  have hf (w : ℤ) : fourierCoeff f w = ∫ x : ℝ, g x*phase (T*β) w x :=
    circleChirp_coefficient hα hs _ _
  have hh := fourier_truncation_error f (box T β) (fun w ↦ C/T*latticeWeight w)
    (latticeWeight_summable.mul_left (C/T))
    (fun w ↦ mul_nonneg (div_nonneg hC (by linarith)) (latticeWeight_pos w).le)
    (fun w hw ↦ by rw [hf]; simpa only [pow_one] using hbound T hT w hw) z
  change ‖(∑ w ∈ box T β, fourierCoeff f w*fourier w z)-f z‖ ≤ _ at hh
  simp only [hf, tsum_mul_left] at hh
  convert hh using 1 <;> (try dsimp [rowTrunc, f])
  ring

lemma circleChirp_norm {g : ℝ → ℂ} (hg : ∀ x, ‖g x‖ ≤ 1)
    (t : ℝ) (z : UnitAddCircle) : ‖circleChirp g t z‖ ≤ 1 := by
  dsimp [circleChirp, AddCircle.liftIoc, Function.comp_def, Set.domRestrict]
  rw [norm_mul, phase_norm, mul_one]
  exact hg _

lemma circleChirp_mass {g : ℝ → ℂ} {α : ℝ} (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) :
    (∫ z : UnitAddCircle, ‖circleChirp g t z‖^2 ∂AddCircle.haarAddCircle) =
      ∫ x : ℝ, ‖g x‖^2 := by
  rw [AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.integral_preimage 1 (-1/2)]
  calc
    _ = ∫ x in Set.Ioc (-1/2:ℝ) (-1/2+1), ‖g x‖^2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change ‖circleChirp g t (x : UnitAddCircle)‖^2 = ‖g x‖^2
      rw [circleChirp, AddCircle.liftIoc_coe_apply hx, norm_mul, phase_norm, mul_one]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : g x=0 := cutoff_zero hs (by
        intro ⟨hx1,hx2⟩
        apply hx
        constructor <;> linarith)
      simp [hz]

lemma circle_parseval (f : C(UnitAddCircle,ℂ)) :
    HasSum (fun w : ℤ ↦ ‖fourierCoeff f w‖^2)
      (∫ z : UnitAddCircle, ‖f z‖^2 ∂AddCircle.haarAddCircle) := by
  have hh := hasSum_sq_fourierCoeff (f.toLp 2 AddCircle.haarAddCircle ℂ)
  simp only [fourierCoeff_toLp] at hh
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle] with x hx
  rw [hx]

lemma coefficient_norm_le_one (f : C(UnitAddCircle,ℂ)) (hf : ∀ z, ‖f z‖≤1)
    (w : ℤ) : ‖fourierCoeff f w‖ ≤ 1 := by
  unfold fourierCoeff
  calc
    _ ≤ ∫ z : UnitAddCircle, ‖fourier (-w) z • f z‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _z : UnitAddCircle, (1:ℝ) ∂AddCircle.haarAddCircle := by
      apply integral_mono
      · exact (show Continuous (fun z ↦ ‖fourier (-w) z • f z‖) by fun_prop).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
      · intro z
        simpa only [norm_smul, circle_fourier_norm, one_mul] using hf z
    _ = 1 := by simp

/-- Retained squared Fourier mass loses only O(1/T), uniformly in the
quadratic modulation. This is the scalar Parseval ingredient for spreading. -/
theorem row_mass_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) (hg1 : ∀ x, ‖g x‖≤1) {α : ℝ}
    (hα0 : 0≤α) (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α)
    {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T →
      (∫ x : ℝ, ‖g x‖^2) - C/T ≤
        ∑ w ∈ box T β, ‖∫ x : ℝ, g x*phase (T*β) w x‖^2 := by
  obtain ⟨C,hC,hbound⟩ := offbox_weighted hg hgs hα0 hα hs hβ 1
  refine ⟨C*(∑' w, latticeWeight w),mul_nonneg hC (tsum_nonneg (fun w ↦ (latticeWeight_pos w).le)),?_⟩
  intro T hT
  let f : C(UnitAddCircle,ℂ) := ⟨circleChirp g (T*β),circleChirp_continuous hgs.continuous hα hs _⟩
  have hf (w : ℤ) : fourierCoeff f w = ∫ x : ℝ, g x*phase (T*β) w x :=
    circleChirp_coefficient hα hs _ _
  have hp := circle_parseval f
  change HasSum _ (∫ z : UnitAddCircle, ‖circleChirp g (T*β) z‖^2 ∂AddCircle.haarAddCircle) at hp
  rw [circleChirp_mass hα hs] at hp
  have he := hp.summable.sum_add_tsum_compl (s := box T β)
  rw [hp.tsum_eq] at he
  change (∑ w ∈ box T β, ‖fourierCoeff f w‖^2) +
    (∑' w : {w : ℤ // w ∉ box T β}, ‖fourierCoeff f w.val‖^2) = _ at he
  have ht : (∑' w : {w : ℤ // w ∉ box T β}, ‖fourierCoeff f w.val‖^2) ≤
      C/T*(∑' w, latticeWeight w) := by
    calc
      _ ≤ ∑' w : {w : ℤ // w ∉ box T β}, C/T*latticeWeight w.val := by
        apply (hp.summable.subtype _).tsum_le_tsum
        · intro w
          have hn := coefficient_norm_le_one f (circleChirp_norm hg1 _) w.val
          have hb := hbound T hT w.val w.property
          change ‖fourierCoeff f w.val‖^2 ≤ _
          rw [hf]
          have hn' := norm_nonneg (fourierCoeff f w.val)
          rw [hf] at hn hn'
          simpa only [pow_one] using (show ‖∫ x : ℝ, g x*phase (T*β) w.val x‖^2 ≤
            C/T^1*latticeWeight w.val by nlinarith only [hn,hn',hb])
        · exact (latticeWeight_summable.mul_left (C/T)).subtype _
      _ ≤ ∑' w : ℤ, C/T*latticeWeight w := by
        exact ((latticeWeight_summable.mul_left (C/T)).subtype _).tsum_le_tsum_of_inj
          Subtype.val Subtype.val_injective
          (fun w _ ↦ mul_nonneg (div_nonneg hC (by linarith)) (latticeWeight_pos w).le)
          (fun _ ↦ le_rfl) (latticeWeight_summable.mul_left (C/T))
      _ = _ := tsum_mul_left
  simp_rw [hf] at he ht
  have heq : C/T*(∑' w, latticeWeight w) = (C*(∑' w, latticeWeight w))/T := by ring
  rw [heq] at ht
  linarith

/-- Tensoring finitely many uniformly bounded approximations preserves a
uniform O(1/T) error; both target functions may depend on T. -/
lemma finite_product_error {I : Type uI} {Z : Type uZ} (S : Finset I)
    (f h : I → ℝ → Z → ℂ)
    (hh : ∀ i ∈ S, ∀ T z, ‖h i T z‖≤1)
    (hf : ∀ i ∈ S, ∃ C : ℝ, 0≤C ∧ ∀ T, 1≤T → ∀ z, ‖f i T z-h i T z‖≤C/T) :
    ∃ C : ℝ, 0≤C ∧ ∀ T, 1≤T → ∀ z,
      ‖(∏ i ∈ S, f i T z)-(∏ i ∈ S, h i T z)‖ ≤ C/T := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0,le_rfl,by simp⟩
  | @insert i S hi ih =>
      obtain ⟨C,hC,hc⟩ := hf i (Finset.mem_insert_self _ _)
      obtain ⟨D,hD,hd⟩ := ih
        (fun j hj ↦ hh j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      refine ⟨(1+C)*D+C,by positivity,?_⟩
      intro T hT z
      have hT0 : 0<T := by linarith
      have hn : ‖f i T z‖ ≤ 1+C := by
        have hb := norm_sub_norm_le (f i T z) (h i T z)
        have hc' := hc T hT z
        have hh' := hh i (Finset.mem_insert_self _ _) T z
        have hcT : C/T≤C := (div_le_self hC hT)
        linarith
      have hp : ‖∏ j ∈ S, h j T z‖≤1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun j _ ↦ norm_nonneg (h j T z)) (fun j hj ↦ hh j (Finset.mem_insert_of_mem hj) T z)
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc
        _ = ‖f i T z*((∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)) +
          (f i T z-h i T z)*(∏ j ∈ S, h j T z)‖ := by congr 1; ring
        _ ≤ ‖f i T z‖*‖(∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)‖ +
          ‖f i T z-h i T z‖*‖∏ j ∈ S, h j T z‖ := by
            simpa only [norm_mul] using norm_add_le
              (f i T z*((∏ j ∈ S, f j T z)-(∏ j ∈ S, h j T z)))
              ((f i T z-h i T z)*(∏ j ∈ S, h j T z))
        _ ≤ (1+C)*(D/T)+(C/T)*1 := by
          apply add_le_add
          · exact mul_le_mul hn (hd T hT z) (norm_nonneg _) (by positivity)
          · exact mul_le_mul (hc T hT z) hp (norm_nonneg _) (by positivity)
        _ = _ := by ring

end
end QuadraticTail
end AsymptoticallyMinimalLittlewood

end OAI
