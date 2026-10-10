import Mathlib
import OAI.Analysis.PathSelection.AdmissibleFunctions

namespace OAI

/-! Uniqueness of holomorphic asymptotic expansions on sectors. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Complex
open scoped Topology

namespace DegeneratingTrees

 
def quadraticRegion (A c : ℝ) : Set ℂ :=
  {z | A < z.re ∧ |z.im| < c * z.re ^ 2}

 
def lossSector (ω : ℝ → ℝ) (R : ℝ) : Set ℂ :=
  {z | R < ‖z‖ ∧ |z.arg| < Real.pi / 2 - ω ‖z‖}

 

def AdmissibleAngularLoss (ω : ℝ → ℝ) : Prop :=
  (∀ᶠ r : ℝ in atTop, 0 < ω r ∧ (Real.log r)⁻¹ ^ 2 ≤ ω r) ∧
  ∃ (n₀ : ℕ) (w : ℕ → ℝ),
    (∀ n, 0 ≤ w n) ∧ Summable w ∧
    ∀ n r, (2 : ℝ) ^ (n + n₀) < r → r < (2 : ℝ) ^ (n + n₀ + 2) → ω r ≤ w n

 

def CentralSuperexponential (f : ℂ → ℂ) : Prop :=
  ∀ B : ℝ, 0 < B → ∃ C R : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, R < ‖z‖ → |z.arg| ≤ Real.pi / 4 →
      ‖f z‖ ≤ C * Real.exp (-B * ‖z‖)

 

def SectorUniquenessStatement : Prop :=
  ∀ (ω : ℝ → ℝ) (R : ℝ) (f : ℂ → ℂ),
    AdmissibleAngularLoss ω →
    AnalyticOnNhd ℂ f (lossSector ω R) →
    (∃ M : ℝ, ∀ z ∈ lossSector ω R, ‖f z‖ ≤ M) →
    CentralSuperexponential f →
    ∃ R' : ℝ, R ≤ R' ∧ EqOn f 0 (lossSector ω R')

 

def sectorKernel (t : ℝ) (z : ℂ) : ℂ := (t : ℂ) / ((t : ℂ) + z)

lemma kernel_den_ne {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 ≤ z.re) :
    (t : ℂ) + z ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [add_re, ofReal_re, zero_re] at this
  linarith

lemma sectorKernel_norm_le {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖sectorKernel t z‖ ≤ 1 := by
  have hden : t ≤ ‖(t : ℂ) + z‖ := by
    calc t ≤ ((t : ℂ) + z).re := by simp only [add_re, ofReal_re]; linarith
         _ ≤ ‖(t : ℂ) + z‖ := re_le_norm _
  rw [sectorKernel, norm_div, Complex.norm_of_nonneg ht.le]
  exact (div_le_one (ht.trans_le hden)).2 hden

lemma sectorKernel_re_nonneg {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (sectorKernel t z).re := by
  simp only [sectorKernel, Complex.div_re, ofReal_re, add_re, ofReal_im,
    zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg ht.le (by linarith)) (normSq_nonneg _)

lemma mul_sectorKernel_re {t : ℝ} (z : ℂ) :
    (z * sectorKernel t z).re =
      t * (t * z.re + ‖z‖ ^ 2) / ‖(t : ℂ) + z‖ ^ 2 := by
  rw [sectorKernel, ← mul_div_assoc, Complex.div_re]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, mul_im,
    zero_add, add_re, add_im, Complex.sq_norm, normSq_apply]
  ring

lemma mul_sectorKernel_re_nonneg {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (z * sectorKernel t z).re := by
  rw [mul_sectorKernel_re]
  positivity

lemma mul_sectorKernel_re_lower {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : 0 ≤ z.re) (hlo : t ≤ ‖z‖) (hhi : ‖z‖ ≤ 2 * t) :
    ‖z‖ / 8 ≤ (z * sectorKernel t z).re := by
  have hr : 0 < ‖z‖ := ht.trans_le hlo
  have hd : 0 < ‖(t : ℂ) + z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (kernel_den_ne ht hz))
  have hden : ‖(t : ℂ) + z‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
    have ha := norm_add_le (t : ℂ) z
    rw [Complex.norm_of_nonneg ht.le] at ha
    nlinarith [norm_nonneg ((t : ℂ) + z)]
  have hlower : t / 4 ≤ (z * sectorKernel t z).re := by
    rw [mul_sectorKernel_re, le_div_iff₀ hd]
    have hmul := mul_le_mul_of_nonneg_left hden ht.le
    have hx : 0 ≤ t * (t * z.re) := by positivity
    nlinarith
  linarith

lemma arg_lt_of_re_lower {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : z ≠ 0) (h : 2 * η * ‖z‖ ≤ z.re) :
    |z.arg| < Real.pi / 2 - η := by
  have hr : 0 ≤ z.re := (by positivity : 0 ≤ 2 * η * ‖z‖).trans h
  have ha := Complex.abs_arg_le_pi_div_two_iff.mpr hr
  have hs := Real.sin_le (sub_nonneg.mpr ha)
  rw [Real.sin_pi_div_two_sub, Real.cos_abs, Complex.cos_arg hz] at hs
  have hn := norm_pos_iff.mpr hz
  have hdiv : 2 * η ≤ z.re / ‖z‖ := (le_div_iff₀ hn).mpr h
  linarith

 
def sectorCorrection (a t : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n, (a n : ℂ) * sectorKernel (t n) z

def sectorMap (a t : ℕ → ℝ) (z : ℂ) : ℂ := z * (1 + sectorCorrection a t z)

section Series
variable {a t : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
  (ht : ∀ n, 0 < t n)
include ha hs ht

omit hs in
lemma sectorTerm_norm_le {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ) :
    ‖(a n : ℂ) * sectorKernel (t n) z‖ ≤ a n := by
  rw [norm_mul, Complex.norm_of_nonneg (ha n)]
  simpa using mul_le_mul_of_nonneg_left (sectorKernel_norm_le (ht n) hz) (ha n)

lemma sectorTerms_summable {z : ℂ} (hz : 0 ≤ z.re) :
    Summable (fun n => (a n : ℂ) * sectorKernel (t n) z) :=
  hs.of_norm_bounded (sectorTerm_norm_le ha ht hz)

lemma sectorCorrection_norm_le {z : ℂ} (hz : 0 ≤ z.re) :
    ‖sectorCorrection a t z‖ ≤ ∑' n, a n := by
  have h := sectorTerms_summable ha hs ht hz
  exact (norm_tsum_le_tsum_norm h.norm).trans
    (h.norm.tsum_le_tsum (sectorTerm_norm_le ha ht hz) hs)

lemma sectorCorrection_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (sectorCorrection a t z).re := by
  rw [sectorCorrection, Complex.re_tsum (sectorTerms_summable ha hs ht hz)]
  apply tsum_nonneg
  intro n
  simpa only [re_ofReal_mul] using
    mul_nonneg (ha n) (sectorKernel_re_nonneg (ht n) hz)

lemma sectorMap_norm_lower {z : ℂ} (hz : 0 ≤ z.re) :
    ‖z‖ ≤ ‖sectorMap a t z‖ := by
  have hA := sectorCorrection_re_nonneg ha hs ht hz
  have h : 1 ≤ ‖1 + sectorCorrection a t z‖ := by
    calc 1 ≤ (1 + sectorCorrection a t z).re := by simpa only [add_re, one_re] using le_add_of_nonneg_right hA
         _ ≤ _ := re_le_norm _
  simpa only [sectorMap, norm_mul, mul_one] using mul_le_mul_of_nonneg_left h (norm_nonneg z)

lemma sectorMap_norm_upper (hsmall : (∑' n, a n) ≤ 1) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖sectorMap a t z‖ ≤ 2 * ‖z‖ := by
  have hA : ‖sectorCorrection a t z‖ ≤ 1 := (sectorCorrection_norm_le ha hs ht hz).trans hsmall
  have h : ‖1 + sectorCorrection a t z‖ ≤ 2 := by
    calc _ ≤ ‖(1 : ℂ)‖ + ‖sectorCorrection a t z‖ := norm_add_le _ _
         _ ≤ 2 := by simp only [norm_one]; linarith
  simpa only [sectorMap, norm_mul, mul_comm ‖z‖ 2] using mul_le_mul_of_nonneg_left h (norm_nonneg z)

lemma sectorMap_re_lower {z : ℂ} (hz : 0 ≤ z.re) (n : ℕ)
    (hlo : t n ≤ ‖z‖) (hhi : ‖z‖ ≤ 2 * t n) :
    a n * (‖z‖ / 8) ≤ (sectorMap a t z).re := by
  have hsum := (sectorTerms_summable ha hs ht hz).mul_left z
  have hne : ∀ m, 0 ≤ (z * ((a m : ℂ) * sectorKernel (t m) z)).re := by
    intro m
    rw [mul_comm z, mul_assoc, re_ofReal_mul, mul_comm (sectorKernel (t m) z)]
    exact mul_nonneg (ha m) (mul_sectorKernel_re_nonneg (ht m) hz)
  have hsingle := (Complex.hasSum_re hsum.hasSum).summable.le_tsum n (fun i _ => hne i)
  rw [sectorMap, mul_add, mul_one, add_re]
  have heq : (z * sectorCorrection a t z).re =
      ∑' m, (z * ((a m : ℂ) * sectorKernel (t m) z)).re := by
    rw [sectorCorrection, ← tsum_mul_left, Complex.re_tsum hsum]
  rw [heq]
  calc a n * (‖z‖ / 8) ≤ a n * (z * sectorKernel (t n) z).re :=
         mul_le_mul_of_nonneg_left (mul_sectorKernel_re_lower (ht n) hz hlo hhi) (ha n)
       _ = (z * ((a n : ℂ) * sectorKernel (t n) z)).re := by
         rw [← re_ofReal_mul]
         congr 1
         ring
       _ ≤ ∑' m, (z * ((a m : ℂ) * sectorKernel (t m) z)).re := hsingle
       _ ≤ z.re + ∑' m, (z * ((a m : ℂ) * sectorKernel (t m) z)).re := le_add_of_nonneg_left hz

lemma sectorCorrection_differentiableOn :
    DifferentiableOn ℂ (sectorCorrection a t) {z : ℂ | 0 < z.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm hs
  · intro n
    apply (differentiableOn_const _).mul
    exact (differentiableOn_const _).div ((differentiableOn_const _).add differentiableOn_id)
      (fun z hz => kernel_den_ne (ht n) hz.le)
  · exact isOpen_lt continuous_const continuous_re
  · intro n z hz
    exact sectorTerm_norm_le ha ht hz.le n

lemma sectorMap_differentiableOn :
    DifferentiableOn ℂ (sectorMap a t) {z : ℂ | 0 < z.re} :=
  differentiableOn_id.mul ((differentiableOn_const _).add (sectorCorrection_differentiableOn ha hs ht))

end Series

lemma dyadic_shell {T r : ℝ} (hT : 0 < T) (hr : T ≤ r) :
    ∃ n : ℕ, T * 2 ^ n ≤ r ∧ r < 2 * (T * 2 ^ n) := by
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near
    ((le_div_iff₀ hT).mpr (by simpa using hr)) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, ?_, ?_⟩
  · have := (le_div_iff₀ hT).mp hlo
    nlinarith
  · have := (div_lt_iff₀ hT).mp hhi
    rw [pow_succ] at this
    nlinarith

 

lemma angularLoss_kernel_data {ω : ℝ → ℝ} (hω : AdmissibleAngularLoss ω) :
    ∃ (a t : ℕ → ℝ) (S : ℝ), 0 < S ∧
      (∀ n, 0 ≤ a n) ∧ Summable a ∧ (∀ n, 0 < t n) ∧ (∑' n, a n) ≤ 1 ∧
      (∀ r, S ≤ r → 0 < ω r ∧ ω r ≤ 1 / 64 ∧
        ∃ n, t n ≤ r ∧ r < 2 * t n ∧
          ∀ s, r ≤ s → s ≤ 2 * r → ω s ≤ a n / 64) := by
  rcases hω with ⟨hpos, n₀, w, hw, hws, hbound⟩
  obtain ⟨Rp, hRp⟩ := eventually_atTop.mp hpos
  let b : ℕ → ℝ := fun n => w n + w (n + 1)
  have hb : ∀ n, 0 ≤ b n := fun n => add_nonneg (hw n) (hw (n + 1))
  have hbs : Summable b := hws.add ((summable_nat_add_iff 1).mpr hws)
  obtain ⟨N, hN⟩ := ((tendsto_sum_nat_add b).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 64 by norm_num))).exists
  let a : ℕ → ℝ := fun n => 64 * b (n + N)
  let T : ℝ := 2 ^ (N + n₀ + 1)
  let t : ℕ → ℝ := fun n => T * 2 ^ n
  have hT : 0 < T := by dsimp [T]; positivity
  have ha : ∀ n, 0 ≤ a n := fun n => mul_nonneg (by norm_num) (hb (n + N))
  have htail : Summable (fun n => b (n + N)) := (summable_nat_add_iff N).mpr hbs
  have has : Summable a := htail.mul_left 64
  have hsmall : (∑' n, a n) ≤ 1 := by
    dsimp [a]
    rw [tsum_mul_left]
    linarith
  have ht : ∀ n, 0 < t n := by intro n; dsimp [t]; positivity
  have t_eq (n : ℕ) : t n = 2 ^ (n + N + n₀ + 1) := by
    dsimp [t, T]
    rw [← pow_add]
    congr 1
    omega
  have hab (n : ℕ) : a n / 64 = b (n + N) := by dsimp [a]; ring
  have hshell (n : ℕ) (s : ℝ) (hslo : t n ≤ s) (hshi : s < 4 * t n) :
      ω s ≤ a n / 64 := by
    rw [hab]
    dsimp [b]
    have hlo : 2 ^ (n + N + n₀) < t n := by
      rw [t_eq, pow_succ]
      have : (0 : ℝ) < 2 ^ (n + N + n₀) := by positivity
      linarith
    have hmid : 2 ^ (n + N + n₀ + 2) = 2 * t n := by
      rw [t_eq]
      rw [show n + N + n₀ + 2 = (n + N + n₀ + 1) + 1 by omega, pow_succ]
      ring
    by_cases hcase : s < 2 * t n
    · have h := hbound (n + N) s (hlo.trans_le hslo) (by simpa only [hmid] using hcase)
      exact h.trans (le_add_of_nonneg_right (hw (n + N + 1)))
    · have hleft : 2 ^ (n + N + 1 + n₀) = t n := by rw [t_eq]; congr 1; omega
      have hright : 2 ^ (n + N + 1 + n₀ + 2) = 4 * t n := by
        rw [t_eq]
        rw [show n + N + 1 + n₀ + 2 = (n + N + n₀ + 1) + 2 by omega, pow_add]
        norm_num
        ring
      have h := hbound (n + N + 1) s (by rw [hleft]; linarith [ht n])
        (by simpa only [hright] using hshi)
      exact h.trans (le_add_of_nonneg_left (hw (n + N)))
  refine ⟨a, t, max T Rp, lt_of_lt_of_le hT (le_max_left _ _), ha, has, ht, hsmall, ?_⟩
  intro r hr
  have hrT : T ≤ r := (le_max_left _ _).trans hr
  have hrp : Rp ≤ r := (le_max_right _ _).trans hr
  have hrpos : 0 < r := hT.trans_le hrT
  obtain ⟨n, hnlo, hnhi⟩ := dyadic_shell hT hrT
  change t n ≤ r at hnlo
  change r < 2 * t n at hnhi
  have hcontrol : ∀ s, r ≤ s → s ≤ 2 * r → ω s ≤ a n / 64 := by
    intro s hslo hshi
    exact hshell n s (hnlo.trans hslo) (by linarith)
  refine ⟨(hRp r hrp).1, ?_, n, hnlo, hnhi, hcontrol⟩
  have hsingle : a n ≤ 1 := (has.le_tsum n (fun i _ => ha i)).trans hsmall
  exact (hcontrol r le_rfl (by linarith)).trans ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 64)).mpr hsingle)

lemma sectorMap_arg_real {a t : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (ht : ∀ n, 0 < t n) {x : ℝ} (hx : 0 ≤ x) :
    (sectorMap a t (x : ℂ)).arg = 0 := by
  have hz : (0 : ℝ) ≤ (x : ℂ).re := hx
  have hA := sectorCorrection_re_nonneg ha hs ht hz
  have hI : (sectorCorrection a t (x : ℂ)).im = 0 := by
    rw [sectorCorrection, Complex.im_tsum (sectorTerms_summable ha hs ht hz)]
    simp [sectorKernel, Complex.div_im]
  apply Complex.arg_eq_zero_iff.mpr
  constructor
  · simp only [sectorMap, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      add_re, one_re]
    positivity
  · simp [sectorMap, mul_im, hI]

lemma sectorMap_mem_lossSector {ω : ℝ → ℝ} {a t : ℕ → ℝ} {S R : ℝ}
    (hS : 0 < S) (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (ht : ∀ n, 0 < t n) (hsmall : (∑' n, a n) ≤ 1)
    (hω : ∀ r, S ≤ r → 0 < ω r ∧ ω r ≤ 1 / 64 ∧
      ∃ n, t n ≤ r ∧ r < 2 * t n ∧
        ∀ s, r ≤ s → s ≤ 2 * r → ω s ≤ a n / 64)
    {z : ℂ} (hz : 0 ≤ z.re) (hlo : S ≤ ‖z‖) (hR : R < ‖z‖) :
    sectorMap a t z ∈ lossSector ω R := by
  have hnormL := sectorMap_norm_lower ha hs ht hz
  have hnormU := sectorMap_norm_upper ha hs ht hsmall hz
  have hpos := (hω _ (hlo.trans hnormL)).1
  obtain ⟨n, hnlo, hnhi, hn⟩ := (hω _ hlo).2.2
  have hbound := hn _ hnormL hnormU
  have hreal := sectorMap_re_lower ha hs ht hz n hnlo hnhi.le
  constructor
  · exact hR.trans_le hnormL
  · apply arg_lt_of_re_lower hpos (norm_pos_iff.mp (hS.trans_le (hlo.trans hnormL)))
    calc 2 * ω ‖sectorMap a t z‖ * ‖sectorMap a t z‖ ≤
            2 * (a n / 64) * ‖sectorMap a t z‖ := by gcongr
         _ ≤ 2 * (a n / 64) * (2 * ‖z‖) :=
            mul_le_mul_of_nonneg_left hnormU (by positivity [ha n])
         _ ≤ a n * (‖z‖ / 8) := by nlinarith [mul_nonneg (ha n) (norm_nonneg z)]
         _ ≤ (sectorMap a t z).re := hreal

 

lemma lossSector_isPreconnected {ω : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hω : ∀ r, R < r → 0 < ω r ∧ ω r < Real.pi / 2) :
    IsPreconnected (lossSector ω R) := by
  let ray : Set ℂ := Complex.ofReal '' Ioi R
  have hray : IsPreconnected ray := isPreconnected_Ioi.image _ continuous_ofReal.continuousOn
  have hray_sub : ray ⊆ lossSector ω R := by
    rintro _ ⟨r, hr, rfl⟩
    have hr0 : 0 ≤ r := (hR.trans hr).le
    simp only [lossSector, mem_ofPred_eq, Complex.norm_of_nonneg hr0,
      Complex.arg_ofReal_of_nonneg hr0, abs_zero]
    exact ⟨hr, sub_pos.mpr (hω r hr).2⟩
  apply isPreconnected_of_forall ((R + 1 : ℝ) : ℂ)
  intro z hz
  let arc : ℝ → ℂ := fun θ => (‖z‖ : ℂ) * Complex.exp ((θ : ℂ) * I)
  let J : Set ℝ := Icc (-|z.arg|) |z.arg|
  have hc : Continuous arc := by dsimp [arc]; fun_prop
  have hn : 0 < ‖z‖ := hR.trans hz.1
  have hnorm (θ : ℝ) : ‖arc θ‖ = ‖z‖ := by
    dsimp [arc]
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg (norm_nonneg z)]
  have harg (θ : ℝ) (hθ : θ ∈ J) : (arc θ).arg = θ := by
    dsimp [arc]
    rw [arg_real_mul _ hn, arg_exp_mul_I]
    apply (toIocMod_eq_self _).mpr
    have hp := (hω ‖z‖ hz.1).1
    have hθabs : |θ| ≤ |z.arg| := abs_le.mpr hθ
    have := abs_le.mp hθabs
    constructor <;> linarith [hz.2, Real.pi_pos]
  have harc_sub : arc '' J ⊆ lossSector ω R := by
    rintro _ ⟨θ, hθ, rfl⟩
    change R < ‖arc θ‖ ∧ |(arc θ).arg| < Real.pi / 2 - ω ‖arc θ‖
    rw [hnorm, harg θ hθ]
    exact ⟨hz.1, (abs_le.mpr hθ).trans_lt hz.2⟩
  have harc : IsPreconnected (arc '' J) := isPreconnected_Icc.image arc hc.continuousOn
  have hzero : arc 0 = (‖z‖ : ℂ) := by simp [arc]
  have hinray : (‖z‖ : ℂ) ∈ ray := ⟨‖z‖, hz.1, rfl⟩
  have hinarc : (‖z‖ : ℂ) ∈ arc '' J := by
    refine ⟨0, ⟨?_, ?_⟩, hzero⟩ <;> linarith [abs_nonneg z.arg]
  refine ⟨ray ∪ arc '' J, union_subset hray_sub harc_sub, ?_, ?_,
    hray.union _ hinray hinarc harc⟩
  · exact Or.inl ⟨R + 1, by simp, rfl⟩
  · apply Or.inr
    refine ⟨z.arg, ⟨neg_abs_le _, le_abs_self _⟩, ?_⟩
    exact Complex.norm_mul_exp_arg_mul_I z

lemma superpolynomialDecay_of_ray_bounds {G : ℂ → ℂ}
    (hG : ∀ B : ℝ, 0 < B → ∃ C R : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, R ≤ x → ‖G x‖ ≤ C * Real.exp (-B * x)) :
    Asymptotics.SuperpolynomialDecay atTop Real.exp (fun x : ℝ => ‖G x‖) := by
  intro n
  obtain ⟨C, R, hC, hbound⟩ := hG (n + 1) (by positivity)
  have hlimit : Tendsto (fun x : ℝ => C * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun x => by positivity)) _ hlimit
  filter_upwards [eventually_ge_atTop R] with x hx
  calc Real.exp x ^ n * ‖G x‖ ≤ Real.exp x ^ n * (C * Real.exp (-(n + 1) * x)) := by
         gcongr
         exact hbound x hx
       _ = C * Real.exp (-x) := by
         rw [← Real.exp_nat_mul]
         calc Real.exp (n * x) * (C * Real.exp (-(n + 1) * x)) =
             C * (Real.exp (n * x) * Real.exp (-(n + 1) * x)) := by ring
              _ = C * Real.exp (-x) := by rw [← Real.exp_add]; congr 2; ring

 

theorem sector_uniqueness : SectorUniquenessStatement := by
  intro ω R f hω hf hbounded hdecay
  obtain ⟨a, t, S, hS, ha, hs, ht, hsmall, hcontrol⟩ := angularLoss_kernel_data hω
  let R' : ℝ := max S R
  let q : ℝ := R' + 1
  have hR'S : S ≤ R' := le_max_left _ _
  have hR'R : R ≤ R' := le_max_right _ _
  have hR' : 0 < R' := hS.trans_le hR'S
  have hq : 0 < q := by dsimp [q]; linarith
  let H : ℂ → ℂ := fun z => sectorMap a t (z + (q : ℂ))
  have hshift (z : ℂ) (hz : 0 ≤ z.re) : 0 < (z + (q : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith
  have hnormshift (z : ℂ) : z.re + q ≤ ‖z + (q : ℂ)‖ := by
    simpa only [add_re, ofReal_re] using re_le_norm (z + (q : ℂ))
  have hHmem (z : ℂ) (hz : 0 ≤ z.re) : H z ∈ lossSector ω R' := by
    apply sectorMap_mem_lossSector hS ha hs ht hsmall hcontrol (hshift z hz).le
    · have := hnormshift z
      dsimp [q] at this
      linarith
    · have := hnormshift z
      dsimp [q] at this
      linarith
  have hsubset : lossSector ω R' ⊆ lossSector ω R := by
    intro z hz
    exact ⟨lt_of_le_of_lt hR'R hz.1, hz.2⟩
  have hf' : AnalyticOnNhd ℂ f (lossSector ω R') := hf.mono hsubset
  obtain ⟨M, hM⟩ := hbounded
  have hHdiff (z : ℂ) (hz : 0 ≤ z.re) : DifferentiableAt ℂ H z := by
    have hd := (sectorMap_differentiableOn ha hs ht).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (hshift z hz))
    exact hd.comp z (differentiableAt_id.add_const (q : ℂ))
  let G : ℂ → ℂ := fun z => f (H z)
  have hGdiff : DiffContOnCl ℂ G {z : ℂ | 0 < z.re} := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_setOfPred_lt_re]
    intro z hz
    exact ((hf' _ (hHmem z hz)).differentiableAt.comp z (hHdiff z hz)).differentiableWithinAt
  have hGbound (z : ℂ) (hz : 0 ≤ z.re) : ‖G z‖ ≤ M := hM _ (hsubset (hHmem z hz))
  have hHnorm (x : ℝ) (hx : 0 ≤ x) : x ≤ ‖H (x : ℂ)‖ := by
    have h1 := hnormshift (x : ℂ)
    have h2 := sectorMap_norm_lower ha hs ht (hshift (x : ℂ) hx).le
    change ‖(x : ℂ) + (q : ℂ)‖ ≤ ‖H (x : ℂ)‖ at h2
    simp only [ofReal_re] at h1
    linarith
  have hGdecay : Asymptotics.SuperpolynomialDecay atTop Real.exp (fun x : ℝ => ‖G x‖) := by
    apply superpolynomialDecay_of_ray_bounds
    intro B hB
    obtain ⟨C, T, hC, hCT⟩ := hdecay B hB
    refine ⟨C, max 0 (T + 1), hC, ?_⟩
    intro x hx
    have hx0 : 0 ≤ x := (le_max_left _ _).trans hx
    have hxT : T < x := by have := (le_max_right 0 (T + 1)).trans hx; linarith
    have harg : (H (x : ℂ)).arg = 0 := by
      dsimp [H]
      rw [← ofReal_add]
      exact sectorMap_arg_real ha hs ht (by linarith)
    have h := hCT (H (x : ℂ)) (hxT.trans_le (hHnorm x hx0))
      (by rw [harg, abs_zero]; positivity)
    calc ‖G x‖ ≤ C * Real.exp (-B * ‖H (x : ℂ)‖) := h
         _ ≤ C * Real.exp (-B * x) := by
           apply mul_le_mul_of_nonneg_left _ hC
           apply Real.exp_le_exp.mpr
           exact mul_le_mul_of_nonpos_left (hHnorm x hx0) (neg_nonpos.mpr hB.le)
  have hGzero : EqOn G 0 {z : ℂ | 0 ≤ z.re} := by
    apply PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay hGdiff
    · refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound M ?_⟩
      apply Eventually.filter_mono inf_le_right
      rw [eventually_principal]
      intro z hz
      simpa using hGbound z hz.le
    · exact hGdecay
    · exact ⟨M, fun x => hGbound _ (by simp)⟩
  have hop : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hHd : DifferentiableOn ℂ H {z : ℂ | 0 < z.re} := by
    intro z hz
    exact (hHdiff z (le_of_lt hz)).differentiableWithinAt
  have hanalytic : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re} := hHd.analyticOnNhd hop
  have hopen : IsOpen (H '' {z : ℂ | 0 < z.re}) := by
    rcases hanalytic.is_constant_or_isOpen (convex_halfSpace_re_gt 0).isPreconnected with
      ⟨c, hc⟩ | ho
    · have hx : (0 : ℝ) < ‖c‖ + 1 := by positivity
      have h1 := hHnorm (‖c‖ + 1) hx.le
      rw [hc _ (by simpa using hx)] at h1
      linarith
    · exact ho _ Subset.rfl hop
  have hzero : f =ᶠ[𝓝 (H 1)] 0 := by
    filter_upwards [hopen.mem_nhds (show H 1 ∈ H '' {z : ℂ | 0 < z.re} from
      ⟨1, by simp, rfl⟩)] with z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact hGzero (show 0 ≤ w.re from le_of_lt hw)
  have hconn : IsPreconnected (lossSector ω R') := by
    apply lossSector_isPreconnected hR'
    intro r hr
    have h := hcontrol r (hR'S.trans hr.le)
    exact ⟨h.1, lt_of_le_of_lt h.2.1 (by linarith [Real.pi_gt_three])⟩
  exact ⟨R', hR'R, hf'.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
    (hHmem 1 (by simp)) hzero⟩

end DegeneratingTrees
end

end OAI
