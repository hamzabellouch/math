import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform
import OAI.NumberTheory.DirichletL.CompactProfileFamily
import OAI.NumberTheory.DirichletL.Descent.ActualProfiles
import OAI.NumberTheory.DirichletL.Descent.DescentHeight

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
namespace SevenEighths.InverseClippingProfiles

def logWindow (v : ℝ → ℂ) (L ρ : ℝ) (y : ℝ) : ℂ := v ((y + ρ) / L)

def rootedWindow (v : ℝ → ℂ) (L ρ a H : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (a * y - H * L) : ℂ) * logWindow v L ρ y

lemma logWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ : ℝ) :
    ContDiff ℝ ∞ (logWindow v L ρ) := by
  exact hv.comp ((contDiff_id.add contDiff_const).div_const L)

lemma rootedWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ a H : ℝ) :
    ContDiff ℝ ∞ (rootedWindow v L ρ a H) := by
  apply ContDiff.mul _ (logWindow_contDiff v hv L ρ)
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma logWindow_iteratedDeriv (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v)
    (L ρ : ℝ) (n : ℕ) :
    iteratedDeriv n (logWindow v L ρ) =
      fun y => (L⁻¹)^n • iteratedDeriv n v ((y + ρ) / L) := by
  have h : (logWindow v L ρ) =
      fun y => (fun z => v (L⁻¹ * z)) (y + ρ) := by
    funext y
    simp only [logWindow, div_eq_mul_inv, mul_comm]
  rw [h, iteratedDeriv_comp_add_const n (fun z => v (L⁻¹ * z)) ρ,
    iteratedDeriv_comp_const_smul (hv.of_le (by simp))]
  simp only [div_eq_mul_inv, mul_comm]

lemma expAffine_iteratedDeriv (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => (Real.exp (a * y + b) : ℂ)) =
      fun y => (a : ℂ)^n * (Real.exp (a * y + b) : ℂ) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h := (((hasDerivAt_id y).const_mul a).add_const b).exp
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y h).const_mul ((a : ℂ)^n)
    simp only [Function.comp_def, id_eq, Complex.ofRealCLM_apply] at hc
    rw [hc.deriv]
    simp only [mul_one, Complex.ofReal_mul, pow_succ]
    ring

lemma logWindow_support (v : ℝ → ℂ) (M B L ρ : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    Function.support (logWindow v L ρ) ⊆ Set.Icc (-(M+B)*L) ((M+B)*L) := by
  intro y hy
  have hy' := hv hy
  change -M ≤ (y+ρ)/L ∧ (y+ρ)/L ≤ M at hy'
  have hl := (le_div_iff₀ hL).mp hy'.1
  have hu := (div_le_iff₀ hL).mp hy'.2
  have hr := abs_le.mp hρ
  constructor <;> nlinarith

lemma rootedWindow_compact (v : ℝ → ℂ) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    HasCompactSupport (rootedWindow v L ρ a H) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro y hy
  apply logWindow_support v M B L ρ hL hρ hv
  exact (mul_ne_zero_iff.mp hy).2

def rootSchwartz (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  (rootedWindow_compact v M B L ρ a H hL hρ hv).toSchwartzMap
    (rootedWindow_contDiff v (v.smooth ⊤) L ρ a H)

@[simp] lemma rootSchwartz_apply (v : 𝓢(ℝ, ℂ)) (M B L ρ a H y : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    rootSchwartz v M B L ρ a H hL hρ hv y = rootedWindow v L ρ a H y := rfl

lemma derivative_support (v : 𝓢(ℝ, ℂ)) (M : ℝ)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (n : ℕ) :
    Function.support (iteratedDeriv n v) ⊆ Set.Icc (-M) M :=
  (subset_tsupport _).trans
    ((CompactProfileFamily.tsupport_iteratedDeriv_subset v n).trans
      (closure_minimal hv isClosed_Icc))

lemma root_exp_le_one (a H M B L ρ y : ℝ)
    (hL : 0 ≤ L) (hρ : |ρ| ≤ B*L) (hy : |(y+ρ)/L| ≤ M)
    (hL0 : L ≠ 0) (hH : |a| *(M+B) ≤ H) :
    Real.exp (a*y-H*L) ≤ 1 := by
  have hs : |y| ≤ (M+B)*L := by
    have h := (abs_le.mp hy)
    have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have h1 := (le_div_iff₀ hLp).mp h.1
    have h2 := (div_le_iff₀ hLp).mp h.2
    have hr := abs_le.mp hρ
    apply abs_le.mpr
    constructor <;> nlinarith
  have ha := le_abs_self (a*y)
  rw [abs_mul] at ha
  have hh := mul_le_mul_of_nonneg_left hs (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_right hH hL
  apply Real.exp_le_one_iff.mpr
  nlinarith

lemma expAffine_iteratedFDeriv_norm (a b y : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ => (Real.exp (a*x+b) : ℂ)) y‖ =
      |a|^n * Real.exp (a*y+b) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, expAffine_iteratedDeriv]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem rootSchwartz_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
        (rootSchwartz v M B L ρ a H (by linarith) hρ hv) ≤
      ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n * derivativeSeminormSum v 0 n := by
  have hLp : 0 < L := by linarith
  have hC : 0 ≤ ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n *
      derivativeSeminormSum v 0 n := by
    apply mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hC
  intro y
  have hbase (j : ℕ) (hj : j ≤ n) :
      ‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ j (logWindow v L ρ) y‖ ≤
        ((M+B)*L)^k * derivativeSeminormSum v 0 n := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logWindow_iteratedDeriv v (v.smooth ⊤)]
    by_cases hz : iteratedDeriv j v ((y+ρ)/L) = 0
    · simp only [hz, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
    have harg := derivative_support v M hv j hz
    have hy : |(y+ρ)/L| ≤ M := abs_le.mpr harg
    have he := root_exp_le_one a H M B L ρ y hLp.le hρ hy (ne_of_gt hLp) hH
    have hx : ‖y‖ ≤ (M+B)*L := by
      have ht := logWindow_support (iteratedDeriv j v) M B L ρ hLp hρ
        (derivative_support v M hv j) hz
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2]
    have hd : ‖iteratedDeriv j v ((y+ρ)/L)‖ ≤ derivativeSeminormSum v 0 n := by
      have hh := (SchwartzMap.le_seminorm ℝ 0 j v ((y+ρ)/L)).trans
        (seminorm_le_derivativeSeminormSum v 0 n j hj)
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hh
    have hi : ‖L⁻¹‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
      exact inv_le_one_of_one_le₀ hL
    have hs : ‖(L⁻¹)^j • iteratedDeriv j v ((y+ρ)/L)‖ ≤
        derivativeSeminormSum v 0 n := by
      rw [norm_smul, norm_pow]
      calc
        _ ≤ 1 * ‖iteratedDeriv j v ((y+ρ)/L)‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hi
        _ ≤ _ := by simpa using hd
    calc
      _ ≤ ((M+B)*L)^k * 1 * derivativeSeminormSum v 0 n := by gcongr
      _ = _ := by ring
  have he : ContDiff ℝ ∞ (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  have hh := norm_iteratedFDeriv_mul_le he (logWindow_contDiff v (v.smooth ⊤) L ρ)
    y (n := n) (by exact_mod_cast le_top)
  change ‖y‖^k * ‖iteratedFDeriv ℝ n (rootedWindow v L ρ a H) y‖ ≤ _
  unfold rootedWindow
  calc
    _ ≤ ‖y‖^k * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) y‖ *
        ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * |a|^i *
        (‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) =
        (fun x : ℝ => (Real.exp (a*x+(-H*L)) : ℂ)) by ext x; congr 2; ring]
      rw [expAffine_iteratedFDeriv_norm]
      rw [show a*y+(-H*L) = a*y-H*L by ring]
      ring
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (1+|a|)^n *
        (((M+B)*L)^k * derivativeSeminormSum v 0 n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : |a|^i ≤ (1+|a|)^n := by
        calc
          _ ≤ (1+|a|)^i := by gcongr; linarith [abs_nonneg a]
          _ ≤ _ := pow_le_pow_right₀ (by linarith [abs_nonneg a])
            (Finset.mem_range_succ_iff.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity))
        (hbase (n-i) (Nat.sub_le _ _)) (by positivity) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

def rootDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (2:ℝ)^i * (1+|a|)^i * derivativeSeminormSum v 0 i

def twistedDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  (2:ℝ)^n * (1+2*Real.pi)^n * rootDerivativeBound v a n

lemma rootDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ rootDerivativeBound v a n := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)

lemma twistedDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ twistedDerivativeBound v a n :=
  mul_nonneg (by positivity) (rootDerivativeBound_nonneg _ _ _)

lemma rootSchwartz_derivativeSum (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n ≤
      ((M+B)*L)^k * rootDerivativeBound v a n := by
  unfold derivativeSeminormSum rootDerivativeBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  convert rootSchwartz_seminorm v M B L ρ a H hM hB hL hρ hv hH k i using 1
  ring

theorem rooted_twist_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
      (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      (M+B)^k * twistedDerivativeBound v a n * L^k * (1+‖θ‖)^n := by
  have hb := frequencyTwist_seminorm_polynomial
    (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ k n
  have hd := rootSchwartz_derivativeSum v M B L ρ a H hM hB hL hρ hv hH k n
  calc
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n) *
        (1+‖θ‖)^n := hb
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        (((M+B)*L)^k * rootDerivativeBound v a n)) * (1+‖θ‖)^n := by gcongr
    _ = _ := by unfold twistedDerivativeBound; rw [mul_pow]; ring

def momentOrder (J : ℕ) : ℕ := J + (volume : Measure ℝ).integrablePower

def windowSourceBound (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (1+(M+B)^(volume : Measure ℝ).integrablePower) *
    ∑ i ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a i

lemma windowSourceBound_nonneg (v : 𝓢(ℝ, ℂ)) (M B a : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (J : ℕ) : 0 ≤ windowSourceBound v M B a J := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)

theorem rooted_twist_moment_sources (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (J i : ℕ) (hi : i ≤ momentOrder J) :
    (SchwartzMap.seminorm ℝ 0 i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  let p := (volume : Measure ℝ).integrablePower
  have h0 := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH 0 i
  have hp := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH p i
  simp only [pow_zero, one_mul, mul_one] at h0
  have hs : twistedDerivativeBound v a i ≤
      ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j := by
    apply Finset.single_le_sum (fun j _ => twistedDerivativeBound_nonneg v a j)
    exact Finset.mem_range_succ_iff.mpr hi
  have hl : 1 ≤ L^p := one_le_pow₀ hL
  have ht : (1+‖θ‖)^i ≤ (1+‖θ‖)^(momentOrder J) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg θ]) hi
  have hc := twistedDerivativeBound_nonneg v a i
  have hsum : 0 ≤ ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j :=
    Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)
  calc
    _ ≤ twistedDerivativeBound v a i * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := add_le_add h0 hp
    _ ≤ twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by gcongr; nlinarith
    _ = (1+(M+B)^p) * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by ring
    _ ≤ _ := by unfold windowSourceBound; gcongr

lemma coefficientMomentBound_mul (J : ℕ) (C D : ℝ) :
    coefficientMomentBound J (C*D) = coefficientMomentBound J C * D := by
  unfold coefficientMomentBound
  ring

theorem rooted_twist_fourier_moment (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H) (J : ℕ) :
    (∫ t : ℝ, (1+‖t‖)^J *
      ‖(𝓕 (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ)) t‖) ≤
      ((2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
        coefficientMomentBound J (windowSourceBound v M B a J))) *
      L^(volume : Measure ℝ).integrablePower * (1+‖θ‖)^(momentOrder J) := by
  have hc := windowSourceBound_nonneg v M B a hM hB J
  have h := uniform_fourier_one_plus_moment
    (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) J 1
    (windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
      (1+‖θ‖)^(momentOrder J)) (by norm_num) (by positivity)
    (by
      intro i hi
      simpa using (rooted_twist_moment_sources v M B L ρ a H θ
        hM hB hL hρ hv hH J i hi))
  simp only [one_mul, coefficientMomentBound_mul] at h
  convert h using 1
  ring

theorem child_log_window_parameters (η Z δ : ℝ) (_hη : 0 ≤ η)
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    0 ≤ δ*Real.log Z ∧ |δ*Real.log Z| ≤ 6*(η*Real.log Z) := by
  have hz : 0 ≤ Real.log Z := Real.log_nonneg hZ
  constructor
  · positivity
  · rw [abs_of_nonneg (by positivity : 0 ≤ δ*Real.log Z)]
    nlinarith [mul_le_mul_of_nonneg_right hδu hz]

theorem clipping_ratio_of_column_witness (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q / Z^N) ≠ 0) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  have hz : 0 < Z := by linarith
  have hn : 0 ≤ max 0 N-N := sub_nonneg.mpr (le_max_right _ _)
  refine ⟨Real.one_le_rpow hZ.le hn, ?_⟩
  by_cases hN : 0 ≤ N
  · simpa [max_eq_right hN] using hb
  · have hN' : N ≤ 0 := le_of_lt (lt_of_not_ge hN)
    rw [max_eq_left hN', zero_sub, Real.rpow_neg hz.le]
    have hsupport := (hw hwitness).2
    calc
      _ = 1 / Z^N := (one_div _).symm
      _ ≤ q / Z^N := div_le_div_of_nonneg_right hq (Real.rpow_nonneg hz.le _)
      _ ≤ b := hsupport

theorem clipped_positive_support (w : ℝ → ℂ) (a b c : ℝ)
    (ha : 0 < a) (hc : 1 ≤ c) (hcb : c ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) :
    Function.support (fun y => w (c*y)) ⊆ Set.Icc (a/b) b := by
  intro y hy
  have hs := hw hy
  have hcp : 0 < c := by linarith
  have hbp : 0 < b := lt_of_lt_of_le hcp hcb
  have hyp : 0 < y := by nlinarith [hs.1]
  constructor
  · apply (div_le_iff₀ hbp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcb hyp.le, hs.1]
  · nlinarith [hs.2]

theorem clipped_log_source (w : ℝ → ℂ) (c y : ℝ) (hc : 0 < c) :
    w (c*Real.exp y) = (fun s => w (Real.exp s)) (y+Real.log c) := by
  change w (c*Real.exp y) = w (Real.exp (y+Real.log c))
  rw [Real.exp_add, Real.exp_log hc]
  congr 1
  ring

open InverseMoment

def firstRootExponent (y : Fin 9 → ℝ) : ℝ :=
  -y 3-y 4/2-y 5-(y 7+y 8)/2

def secondRootExponent (y : Fin 6 → ℝ) : ℝ :=
  -y 1-y 2-(y 4+y 5)/2

theorem first_root_coupled_identity (y : Fin 9 → ℝ) :
    firstRootExponent y = -y 3-y 4/2+(y 0+y 1)/2+y 2 -
      ((∑ i, firstLeftSlope i*y i)+(∑ i, firstRightSlope i*y i))/2 := by
  simp [firstRootExponent, firstLeftSlope, firstRightSlope, Fin.sum_univ_succ]
  ring

theorem second_root_coupled_identity (y : Fin 6 → ℝ) :
    secondRootExponent y = -y 1+y 0 -
      ((∑ i, secondLeftSlope i*y i)+(∑ i, secondRightSlope i*y i))/2 := by
  simp [secondRootExponent, secondLeftSlope, secondRightSlope, Fin.sum_univ_succ]
  ring

theorem first_root_budget (y : Fin 9 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L) (h2 : |y 2| ≤ L)
    (h3 : |y 3| ≤ L) (h4 : |y 4| ≤ L)
    (hl : |∑ i, firstLeftSlope i*y i| ≤ L)
    (hr : |∑ i, firstRightSlope i*y i| ≤ L) :
    firstRootExponent y ≤ (9/2:ℝ)*L := by
  rw [first_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨_, h1⟩
  rcases abs_le.mp h2 with ⟨_, h2⟩
  rcases abs_le.mp h3 with ⟨h3, _⟩
  rcases abs_le.mp h4 with ⟨h4, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

theorem second_root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L)
    (hl : |∑ i, secondLeftSlope i*y i| ≤ 4*L)
    (hr : |∑ i, secondRightSlope i*y i| ≤ 4*L) :
    secondRootExponent y ≤ 6*L := by
  rw [second_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨h1, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

def firstRootSlope : Fin 9 → ℝ := ![0,0,0,-1,-(1/2),-1,0,-(1/2),-(1/2)]
def secondRootSlope : Fin 6 → ℝ := ![0,-1,-1,0,-(1/2),-(1/2)]

lemma inverseNormWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseNormWindow V y = (Real.exp (-y) : ℂ)*V y := by
  simp only [inverseNormWindow, Real.exp_neg, Complex.ofReal_inv, div_eq_mul_inv]
  ring

lemma inverseRootWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseRootWindow V y = (Real.exp (-(y/2)) : ℂ)*V y := by
  rw [inverseRootWindow, ← Real.exp_half, Real.exp_neg, Complex.ofReal_inv]
  ring

theorem firstRootWindows_exp (V : Fin 9 → ℝ → ℂ) (i : Fin 9) (y : ℝ) :
    firstRootWindows V i y = (Real.exp (firstRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [firstRootWindows, firstRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem secondRootWindows_exp (V : Fin 6 → ℝ → ℂ) (i : Fin 6) (y : ℝ) :
    secondRootWindows V i y = (Real.exp (secondRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [secondRootWindows, secondRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem firstRootWindows_prod (V : Fin 9 → ℝ → ℂ) (y : Fin 9 → ℝ) :
    (∏ i, firstRootWindows V i (y i)) =
      (Real.exp (firstRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [firstRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [firstRootSlope, firstRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem secondRootWindows_prod (V : Fin 6 → ℝ → ℂ) (y : Fin 6 → ℝ) :
    (∏ i, secondRootWindows V i (y i)) =
      (Real.exp (secondRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [secondRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [secondRootSlope, secondRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem first_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R L : ℝ) (y : Fin 9 → ℝ) :
    (Real.exp (-(9/2:ℝ)*L) : ℂ)*firstPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (firstRootExponent y-(9/2:ℝ)*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, firstLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, firstRightSlope i*y i)) *
      EisensteinSchwartzPoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, firstKernelSlope i*y i)) := by
  rw [firstPoissonProfile, firstRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem second_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    (Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (secondRootExponent y-6*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, secondLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, secondRightSlope i*y i)) *
      EisensteinSchwartzPoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, secondKernelSlope i*y i)) := by
  rw [secondPoissonProfile, secondRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem fourier_phase_shift (f : ℝ → ℂ) (θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f y)) t = (𝓕 f) (t-θ) := by
  simp only [Real.fourier_eq', logPhase, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translate (f : ℝ → ℂ) (ρ t : ℝ) :
    (𝓕 (fun y => f (y+ρ))) t = logPhase t ρ * (𝓕 f) t := by
  have h := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) f ρ) t
  change _ = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t at h
  have h' : (𝓕 (fun y => f (y+ρ))) t = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t := by
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, Function.comp_def, innerₗ_apply_apply] using h
  rw [h']
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, logPhase]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f (y+ρ))) t =
      logPhase (t-θ) ρ * (𝓕 f) (t-θ) := by
  rw [fourier_phase_shift, fourier_translate]

theorem norm_fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    ‖(𝓕 (fun y => logPhase θ y * f (y+ρ))) t‖ = ‖(𝓕 f) (t-θ)‖ := by
  rw [fourier_translated_twist, norm_mul, logPhase_norm, one_mul]

theorem rooted_family_fourier_joint_measurable (v : 𝓢(ℝ, ℂ)) (a H : ℝ) :
    StronglyMeasurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
      (𝓕 (fun y => logPhase p.1.2.2 y * rootedWindow v p.1.1 p.1.2.1 a H y)) p.2) := by
  apply InverseKernelSourceUniform.fourier_joint_stronglyMeasurable
    (fun q : ℝ × ℝ × ℝ => fun y => logPhase q.2.2 y * rootedWindow v q.1 q.2.1 a H y)
  apply Measurable.stronglyMeasurable
  change Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
    logPhase p.1.2.2 p.2 * ((Real.exp (a*p.2-H*p.1.1) : ℂ) *
      v ((p.2+p.1.2.1)/p.1.1)))
  have hp : Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ => logPhase p.1.2.2 p.2) := by
    unfold logPhase
    fun_prop
  exact hp.mul ((show Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
    (Real.exp (a*p.2-H*p.1.1) : ℂ)) by fun_prop).mul
      (v.continuous.measurable.comp (by fun_prop)))

def childWindowDensity (v : 𝓢(ℝ, ℂ)) (η Z δ θ t : ℝ) : ℂ :=
  (𝓕 (fun y => logPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)))) t

def windowMomentConstant (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
    coefficientMomentBound J (windowSourceBound v M B a J))

theorem childWindowDensity_moment (v : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (J : ℕ)
    (η Z δ θ : ℝ) (hη : 0 ≤ η) (hZ : 1 ≤ Z)
    (hL : 1 ≤ η*Real.log Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    Integrable (fun t : ℝ => (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ∧
    (∫ t : ℝ, (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ≤
      windowMomentConstant v M 6 0 J * (η*Real.log Z)^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  have hρ := (child_log_window_parameters η Z δ hη hZ hδ hδu).2
  let g := frequencyTwist (rootSchwartz v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0
    (by linarith) hρ hv) θ
  have he (t : ℝ) : childWindowDensity v η Z δ θ t = (𝓕 g) t := by
    rw [congrFun (SchwartzMap.fourier_coe g) t]
    unfold childWindowDensity
    have hg : (g : ℝ → ℂ) = fun y =>
        logPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)) := by
      funext y
      simp [g, frequencyTwist_apply, rootSchwartz_apply, rootedWindow, logWindow]
    rw [hg]
  simp_rw [he]
  refine ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable g J, ?_⟩
  exact rooted_twist_fourier_moment v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0 θ
    hM (by norm_num) hL hρ hv (by simp) J

theorem retained_clipped_column (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧
    Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
    ∀ θ t : ℝ,
      (𝓕 (fun y => logPhase θ y * w (c*Real.exp y))) t =
        logPhase (t-θ) (Real.log c) * (𝓕 (fun y => w (Real.exp y))) (t-θ) := by
  dsimp only
  have hc := clipping_ratio_of_column_witness w Z N q a b hZ hq hb hw hwitness
  refine ⟨hc.1, hc.2, clipped_positive_support w a b _ ha hc.1 hc.2 hw, ?_⟩
  intro θ t
  have he : (fun y => logPhase θ y * w (Z^(max 0 N-N)*Real.exp y)) =
      (fun y => logPhase θ y * (fun s => w (Real.exp s)) (y+Real.log (Z^(max 0 N-N)))) := by
    ext y
    rw [clipped_log_source w _ y (by linarith)]
  rw [he]
  exact fourier_translated_twist (fun s => w (Real.exp s)) (Real.log (Z^(max 0 N-N))) θ t

theorem translated_twist_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J *
        ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ≤
        C*(1+‖θ‖)^(momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseMoment.frequencyTwist_fourier_moment J g
  refine ⟨C, hC, ?_⟩
  intro ρ θ
  have he (t : ℝ) : ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖ =
      ‖(𝓕 (frequencyTwist g θ)) t‖ := by
    rw [norm_fourier_translated_twist, congrFun (SchwartzMap.fourier_coe _) t]
    have hf : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
      funext y
      exact frequencyTwist_apply g θ y
    rw [hf, fourier_phase_shift]
  simp_rw [he]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable _ _, hb θ⟩

theorem eventually_log_scale_pow_le (C η π : ℝ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hπ : 0 < π) (k : ℕ) :
    ∀ᶠ Z : ℝ in Filter.atTop, C*(η*Real.log Z)^k ≤ Z^π := by
  have h := (_root_.isLittleO_log_rpow_rpow_atTop (k:ℝ) hπ).const_mul_left (C*η^k)
  filter_upwards [h.bound (by norm_num : (0:ℝ) < 1),
    Filter.eventually_ge_atTop (1:ℝ)] with Z hZ hZ1
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hz : 0 ≤ Z := by linarith
  rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg hz π), one_mul] at hZ
  convert hZ using 1
  ring

def firstBalancedSlope : Fin 9 → ℝ := ![1/2,1/2,1,-1,-(1/2),0,0,0,0]
def secondBalancedSlope : Fin 6 → ℝ := ![1,-1,0,0,0,0]

theorem first_root_normalization_split (y : Fin 9 → ℝ) (L : ℝ) :
    Real.exp (firstRootExponent y-(9/2:ℝ)*L) =
      (∏ i, Real.exp (firstBalancedSlope i*y i-|firstBalancedSlope i| *L)) *
      Real.exp (-(∑ i, firstLeftSlope i*y i)/2-L/2) *
      Real.exp (-(∑ i, firstRightSlope i*y i)/2-L/2) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [firstRootExponent, firstBalancedSlope, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ]
  ring

theorem second_root_normalization_split (y : Fin 6 → ℝ) (L : ℝ) :
    Real.exp (secondRootExponent y-6*L) =
      (∏ i, Real.exp (secondBalancedSlope i*y i-|secondBalancedSlope i| *L)) *
      Real.exp (-(∑ i, secondLeftSlope i*y i)/2-2*L) *
      Real.exp (-(∑ i, secondRightSlope i*y i)/2-2*L) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [secondRootExponent, secondBalancedSlope, secondLeftSlope, secondRightSlope,
    Fin.sum_univ_succ]
  ring

end SevenEighths.InverseClippingProfiles

end

end OAI
