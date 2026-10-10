import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.BoundedDegreeMonomials
import OAI.Geometry.SmoothYau.Smoothness.WaveDeriv

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

lemma directionalJet_cexp (l : List ℂ) :
    directionalJet l Complex.exp = fun z => Complex.exp z * l.prod := by
  induction l with
  | nil => funext z; simp
  | cons v l ih =>
    rw [directionalJet_cons,ih]
    funext z
    have hd := ((hasFDerivAt_id (𝕜 := ℝ) z).cexp).mul_const l.prod
    change HasFDerivAt (fun y : ℂ => Complex.exp y * l.prod) _ z at hd
    rw [hd.fderiv]
    simp [List.prod_cons, mul_assoc,mul_comm,mul_left_comm]

lemma norm_real_iteratedFDeriv_cexp_le (k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k Complex.exp z‖ ≤ Real.exp z.re := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Real.exp_pos _).le
  intro v
  rw [iteratedFDeriv_eq_directionalJet Complex.contDiff_exp,
    directionalJet_cexp]
  simp [Complex.norm_exp,List.prod_ofFn]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem semiclassical_exponential_jet_bound (S : E → ℂ) (hS : ContDiff ℝ ∞ S)
    (k : ℕ) (x : E) (C n : ℝ) (hC : 1 ≤ C) (hn : 1 ≤ n)
    (hjets : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i S x‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y => Complex.exp ((n : ℂ) * S y)) x‖ ≤
      (k.factorial : ℝ) * C ^ k * n ^ k * Real.exp (n * (S x).re) := by
  have hCd : 0 ≤ C := le_trans zero_le_one hC
  have hnd : 0 ≤ n := le_trans zero_le_one hn
  have hcomp := norm_iteratedFDeriv_comp_le Complex.contDiff_exp
    (hS.const_smul (n : ℂ))
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) x
    (C := Real.exp (n * (S x).re)) (D := n * C)
    (fun i _ => by simpa using norm_real_iteratedFDeriv_cexp_le i ((n : ℂ) * S x))
    (fun i hi hik => by
      rw [iteratedFDeriv_const_smul_apply'
        ((hS.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top i))))).contDiffAt,
        norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnd]
      calc
        n * ‖iteratedFDeriv ℝ i S x‖ ≤ n * C := mul_le_mul_of_nonneg_left (hjets i hi hik) hnd
        _ ≤ (n * C) ^ i := le_self_pow₀ (one_le_mul_of_one_le_of_one_le hn hC) (by omega))
  simpa only [smul_eq_mul,Function.comp_def,mul_pow] using hcomp.trans_eq (by ring)

def expJetConstant (k : ℕ) (C : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * i.factorial * C ^ i

lemma expJetConstant_nonneg (k : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ expJetConstant k C := by
  unfold expJetConstant
  positivity

theorem semiclassical_product_jet_bound (S F : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (k : ℕ) (x : E) (C A n : ℝ) (hC : 1 ≤ C) (_hA : 0 ≤ A) (hn : 1 ≤ n)
    (hSjets : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFjets : ∀ i ≤ k, ‖iteratedFDeriv ℝ i F x‖ ≤ A) :
    ‖iteratedFDeriv ℝ k (fun y => Complex.exp ((n : ℂ) * S y) * F y) x‖ ≤
      expJetConstant k C * A * n ^ k * Real.exp (n * (S x).re) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hExp := Real.exp_pos (n * (S x).re)
  have hb := norm_iteratedFDeriv_mul_le
    ((hS.const_smul (n:ℂ)).cexp) hF x
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
  apply hb.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1),
        (k.choose i : ℝ) * ((i.factorial : ℝ) * C ^ i * n ^ k * Real.exp (n * (S x).re)) * A := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply (semiclassical_exponential_jet_bound S hS i x C n hC hn
          (fun j hj hji => hSjets j hj (hji.trans hik))).trans
        gcongr
      · exact hFjets (k-i) (Nat.sub_le _ _)
      · exact norm_nonneg _
      · positivity
    _ = _ := by
      unfold expJetConstant
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem localized_product_jet_bound (S F : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (k q : ℕ) (x : E) (C A n φ c : ℝ) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hc : 0 < c)
    (hSjets : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFjets : ∀ i ≤ k, ‖iteratedFDeriv ℝ i F x‖ ≤ A * ‖x‖ ^ q)
    (hphase : n * ((S x).re - φ) ≤ Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2) :
    ‖iteratedFDeriv ℝ k (fun y => Complex.exp ((n : ℂ) * S y) * F y) x‖ ≤
      expJetConstant k C * A * n ^ k *
        ((q.factorial : ℝ) * Real.exp c⁻¹ / (Real.sqrt n) ^ q) * Real.exp (n * φ) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have he : Real.exp (n * (S x).re) ≤
      Real.exp (n * φ) * Real.exp (Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hb := semiclassical_product_jet_bound S F hS hF k x C (A * ‖x‖ ^ q) n hC
    (mul_nonneg hA (pow_nonneg (norm_nonneg _) _)) hn hSjets hFjets
  have hmoment := gaussianEnvelope_scaled_moment q c hc n hn0 ‖x‖ (norm_nonneg _)
  have hconst : 0 ≤ expJetConstant k C * A * n ^ k := by
    exact mul_nonneg (mul_nonneg (expJetConstant_nonneg k (zero_le_one.trans hC)) hA)
      (pow_nonneg hn0.le _)
  calc
    _ ≤ expJetConstant k C * (A * ‖x‖ ^ q) * n ^ k * Real.exp (n * (S x).re) := hb
    _ ≤ expJetConstant k C * (A * ‖x‖ ^ q) * n ^ k *
        (Real.exp (n * φ) * Real.exp (Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left he
      convert mul_nonneg hconst (pow_nonneg (norm_nonneg x) q) using 1; ring
    _ = (expJetConstant k C * A * n ^ k) *
        (‖x‖ ^ q * Real.exp (Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2)) * Real.exp (n * φ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmoment hconst)
      (Real.exp_pos _).le

theorem common_vanishing_jet_bound (F : E → ℂ) (hF : ContDiff ℝ ∞ F)
    (K m : ℕ) (hm : m ≤ K) (r A : ℝ) (hr : r ≤ 1) (hA : 0 ≤ A)
    (hzero : ∀ j < K, iteratedFDeriv ℝ j F 0 = 0)
    (hbound : ∀ x ∈ Metric.ball (0 : E) r, ‖iteratedFDeriv ℝ K F x‖ ≤ A) :
    ∀ x ∈ Metric.ball (0 : E) r, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j F x‖ ≤ A * ‖x‖ ^ (K-m) := by
  intro x hx j hj
  have hjK : j ≤ K := hj.trans hm
  have hb := vanishing_jet_norm_bound F hF K r A hA hzero hbound
    (K-j) (Nat.sub_le _ _) x hx
  rw [Nat.sub_sub_self hjK] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hA
  exact pow_le_pow_of_le_one (norm_nonneg _) ((by simpa using hx : ‖x‖ < r).le.trans hr)
    (Nat.sub_le_sub_left hj K)

lemma semiclassical_power_cancellation (n : ℝ) (hn : 0 < n) (a b : ℕ) :
    n ^ a / (Real.sqrt n) ^ (2*(a+b)) = (n ^ b)⁻¹ := by
  rw [pow_mul,Real.sq_sqrt hn.le,pow_add]
  field_simp

theorem scheduled_taylor_wave_bound (S F : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (m D : ℕ) (x : E) (C A n φ c r : ℝ)
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hn : 1 ≤ n) (hc : 0 < c) (hr : r ≤ 1)
    (hx : x ∈ Metric.ball (0 : E) r)
    (hSjets : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hzero : ∀ j < 2*D+3*m+6, iteratedFDeriv ℝ j F 0 = 0)
    (hbound : ∀ y ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (2*D+3*m+6) F y‖ ≤ A)
    (hphase : n * ((S x).re - φ) ≤ Real.sqrt n * ‖x‖ - c * n * ‖x‖ ^ 2) :
    ‖iteratedFDeriv ℝ m (fun y => Complex.exp ((n : ℂ) * S y) * F y) x‖ ≤
      (expJetConstant m C * A * ((2*(m+(D+3))).factorial : ℝ) * Real.exp c⁻¹) *
        (n ^ (D+3))⁻¹ * Real.exp (n * φ) := by
  have hq : 2*D+3*m+6-m = 2*(m+(D+3)) := by omega
  have hFj := common_vanishing_jet_bound F hF (2*D+3*m+6) m (by omega)
    r A hr hA hzero hbound x hx
  rw [hq] at hFj
  apply (localized_product_jet_bound S F hS hF m (2*(m+(D+3))) x C A n φ c
    hC hA hn hc hSjets hFj hphase).trans_eq
  have hp := semiclassical_power_cancellation n (zero_lt_one.trans_le hn) m (D+3)
  calc
    _ = (expJetConstant m C * A * ((2*(m+(D+3))).factorial : ℝ) * Real.exp c⁻¹) *
        (n ^ m / (Real.sqrt n) ^ (2*(m+(D+3)))) * Real.exp (n * φ) := by ring
    _ = _ := by rw [hp]

lemma frequency_exp_gap_bound (n γ : ℝ) (hn : 0 < n) (hγ : 0 < γ) (m D : ℕ) :
    n ^ m * Real.exp (-γ*n) ≤ ((m+D).factorial : ℝ) / γ ^ (m+D) * (n ^ D)⁻¹ := by
  have hfac : (0 : ℝ) < (m+D).factorial := by positivity
  have hp := Real.pow_div_factorial_le_exp (γ*n) (mul_pos hγ hn).le (m+D)
  have hi : Real.exp (-γ*n) ≤ ((m+D).factorial : ℝ) / (γ*n) ^ (m+D) := by
    have hp' := (div_le_iff₀ hfac).mp hp
    apply (le_div_iff₀ (pow_pos (mul_pos hγ hn) _)).mpr
    have hh := mul_le_mul_of_nonneg_right hp' (Real.exp_pos (-γ*n)).le
    have he : Real.exp (γ*n) * Real.exp (-γ*n) = 1 := by
      rw [← Real.exp_add]; convert Real.exp_zero using 1; ring_nf
    calc
      _ = (γ*n) ^ (m+D) * Real.exp (-γ*n) := by ring
      _ ≤ (Real.exp (γ*n) * (m+D).factorial) * Real.exp (-γ*n) := hh
      _ = ((m+D).factorial : ℝ) := by rw [mul_assoc,← mul_left_comm,he,mul_one]
  apply (mul_le_mul_of_nonneg_left hi (pow_nonneg hn.le _)).trans_eq
  rw [mul_pow,pow_add n]
  field_simp

theorem gap_product_jet_bound (S F : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (m D : ℕ) (x : E) (C A n φ γ : ℝ) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hγ : 0 < γ)
    (hSjets : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFjets : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F x‖ ≤ A)
    (hphase : (S x).re - φ ≤ -γ) :
    ‖iteratedFDeriv ℝ m (fun y => Complex.exp ((n : ℂ) * S y) * F y) x‖ ≤
      (expJetConstant m C * A * ((m+D).factorial : ℝ) / γ ^ (m+D)) *
        (n ^ D)⁻¹ * Real.exp (n * φ) := by
  have hn0 := zero_lt_one.trans_le hn
  have hphase' : Real.exp (n * (S x).re) ≤ Real.exp (n*φ) * Real.exp (-γ*n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hconst : 0 ≤ expJetConstant m C * A :=
    mul_nonneg (expJetConstant_nonneg _ (zero_le_one.trans hC)) hA
  calc
    _ ≤ expJetConstant m C * A * n ^ m * Real.exp (n * (S x).re) :=
      semiclassical_product_jet_bound S F hS hF m x C A n hC hA hn hSjets hFjets
    _ ≤ expJetConstant m C * A * n ^ m * (Real.exp (n*φ) * Real.exp (-γ*n)) :=
      mul_le_mul_of_nonneg_left hphase' (mul_nonneg hconst (pow_nonneg hn0.le _))
    _ = (expJetConstant m C * A) * (n ^ m * Real.exp (-γ*n)) * Real.exp (n*φ) := by ring
    _ ≤ (expJetConstant m C * A) *
        (((m+D).factorial : ℝ) / γ ^ (m+D) * (n ^ D)⁻¹) * Real.exp (n*φ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (frequency_exp_gap_bound n γ hn0 hγ m D) hconst) (Real.exp_pos _).le
    _ = _ := by ring

lemma gaussian_collar_gap {δ c ρ r : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    (hr : ρ ≤ r) (hδ : δ ≤ c*ρ/2) :
    δ*r-c*r^2 ≤ -(c*ρ^2/2) := by
  have hr0 := hρ.le.trans hr
  have hs := mul_nonneg (sub_nonneg.mpr hr) hr0
  have h1 := mul_le_mul_of_nonneg_right hδ hr0
  have h2 := mul_nonneg hc.le hs
  have h3 := mul_nonneg hc.le (show 0 ≤ r^2-ρ^2 by nlinarith)
  nlinarith

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_iteratedFDeriv_const_mul (c : ℂ) (F : E → ℂ) (hF : ContDiff ℝ ∞ F)
    (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => c * F y) x‖ = ‖c‖ * ‖iteratedFDeriv ℝ m F x‖ := by
  change ‖iteratedFDeriv ℝ m (fun y => c • F y) x‖ = _
  rw [iteratedFDeriv_const_smul_apply'
    ((hF.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))))).contDiffAt,
    norm_smul]

lemma norm_iteratedFDeriv_add_le (F G : E → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => F y + G y) x‖ ≤
      ‖iteratedFDeriv ℝ m F x‖ + ‖iteratedFDeriv ℝ m G x‖ := by
  change ‖iteratedFDeriv ℝ m (F+G) x‖ ≤ _
  rw [iteratedFDeriv_add_apply
    ((hF.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))))).contDiffAt
    ((hG.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))))).contDiffAt]
  exact norm_add_le _ _

lemma norm_iteratedFDeriv_linear_three (F G H : E → ℂ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (c d e : ℂ) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => c*F y+d*G y+e*H y) x‖ ≤
      ‖c‖*‖iteratedFDeriv ℝ m F x‖ + ‖d‖*‖iteratedFDeriv ℝ m G x‖ +
        ‖e‖*‖iteratedFDeriv ℝ m H x‖ := by
  have hc : ContDiff ℝ ∞ (fun y => c*F y) := contDiff_const.mul hF
  have hd : ContDiff ℝ ∞ (fun y => d*G y) := contDiff_const.mul hG
  have he : ContDiff ℝ ∞ (fun y => e*H y) := contDiff_const.mul hH
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (fun y => c*F y+d*G y) x‖ +
        ‖iteratedFDeriv ℝ m (fun y => e*H y) x‖ :=
      norm_iteratedFDeriv_add_le _ _ (hc.add hd) he m x
    _ ≤ (‖iteratedFDeriv ℝ m (fun y => c*F y) x‖ +
          ‖iteratedFDeriv ℝ m (fun y => d*G y) x‖) +
        ‖iteratedFDeriv ℝ m (fun y => e*H y) x‖ :=
      add_le_add (norm_iteratedFDeriv_add_le _ _ hc hd m x) le_rfl
    _ = _ := by rw [norm_iteratedFDeriv_const_mul c F hF,
      norm_iteratedFDeriv_const_mul d G hG, norm_iteratedFDeriv_const_mul e H hH]

lemma norm_iteratedFDeriv_weighted_sum (F : ℕ → E → ℂ)
    (hF : ∀ j, ContDiff ℝ ∞ (F j)) (J m : ℕ) (x : E) (t : ℂ) (ht : ‖t‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ j ≤ J, ‖iteratedFDeriv ℝ m (F j) x‖ ≤ A) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ j ∈ Finset.range (J+1), t^j * F j y) x‖ ≤
      (J+1 : ℕ) * A := by
  rw [iteratedFDeriv_fun_sum_apply (fun j _ =>
    ((contDiff_const.mul (hF j)).of_le
      (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)))).contDiffAt)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (J+1), A := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_iteratedFDeriv_const_mul _ _ (hF j), norm_pow]
      exact (mul_le_mul_of_nonneg_left (hbound j (by simpa using hj))
        (pow_nonneg (norm_nonneg _) _)).trans
        ((mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) ht) hA).trans_eq
          (one_mul A))
    _ = _ := by simp

lemma inverse_frequency_norm_le_one {n : ℝ} (hn : 1 ≤ n) : ‖((n : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hn)]
  exact inv_le_one_of_one_le₀ hn

lemma frequency_schedule_cancellation {n : ℝ} (hn : 0 < n) (a b : ℕ) :
    n^a * (n^(a+b))⁻¹ = (n^b)⁻¹ := by
  rw [pow_add]
  field_simp

lemma frequency_inverse_power_mono {n : ℝ} (hn : 1 ≤ n) {a b : ℕ} (hab : a ≤ b) :
    (n^b)⁻¹ ≤ (n^a)⁻¹ := by
  apply inv_anti₀ (pow_pos (zero_lt_one.trans_le hn) a)
  exact pow_le_pow_right₀ hn hab

lemma bounded_wave_term (S F : E → ℂ) (hS : ContDiff ℝ ∞ S) (hF : ContDiff ℝ ∞ F)
    (m : ℕ) (x : E) (C A n φ c : ℝ) (hC : 1 ≤ C) (hA : 0 ≤ A)
    (hn : 1 ≤ n) (hc : 0 < c)
    (hSjets : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFjets : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F x‖ ≤ A)
    (hphase : n * ((S x).re - φ) ≤ Real.sqrt n * ‖x‖ - c*n*‖x‖^2) :
    ‖iteratedFDeriv ℝ m (fun y => Complex.exp ((n : ℂ)*S y)*F y) x‖ ≤
      expJetConstant m C * A * Real.exp c⁻¹ * n^m * Real.exp (n*φ) := by
  have hb := localized_product_jet_bound S F hS hF m 0 x C A n φ c
    hC hA hn hc hSjets (by simpa using hFjets) hphase
  simpa [mul_assoc, mul_left_comm, mul_comm] using hb

theorem finite_scheduled_residual_bound
    (S : E → ℂ) (F R : ℕ → E → ℂ) (L : E → ℂ)
    (hS : ContDiff ℝ ∞ S) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (hR : ∀ j, ContDiff ℝ ∞ (R j)) (hL : ContDiff ℝ ∞ L)
    (m D J : ℕ) (hJ : D+m+1 ≤ J) (x : E) (C A n φ c r : ℝ)
    (hC : 1 ≤ C) (hA : 0 ≤ A) (hn : 1 ≤ n) (hc : 0 < c) (hr : r ≤ 1)
    (hx : x ∈ Metric.ball (0 : E) r)
    (hSjets : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i S x‖ ≤ C)
    (hFzero : ∀ j ≤ J, SmoothJetZero (F j) (2*D+3*m+6))
    (hRzero : ∀ j ≤ J, SmoothJetZero (R j) (2*D+3*m+6))
    (hFbound : ∀ j ≤ J, ∀ y ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (2*D+3*m+6) (F j) y‖ ≤ A)
    (hRbound : ∀ j ≤ J, ∀ y ∈ Metric.ball (0 : E) r,
      ‖iteratedFDeriv ℝ (2*D+3*m+6) (R j) y‖ ≤ A)
    (hLbound : ∀ i ≤ m, ‖iteratedFDeriv ℝ i L x‖ ≤ A)
    (hphase : n * ((S x).re - φ) ≤ Real.sqrt n * ‖x‖ - c*n*‖x‖^2) :
    let H := fun y => (n : ℂ)^2 *
        (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j * (Complex.exp ((n : ℂ)*S y)*F j y)) +
      (n : ℂ) * (∑ j ∈ Finset.range (J+1), ((n : ℂ)⁻¹)^j *
        (Complex.exp ((n : ℂ)*S y)*R j y)) +
      ((n : ℂ)⁻¹)^J * (Complex.exp ((n : ℂ)*S y)*L y)
    let T := expJetConstant m C * A * ((2*(m+(D+3))).factorial : ℝ) * Real.exp c⁻¹
    ‖iteratedFDeriv ℝ m H x‖ ≤
      (2*(J+1 : ℕ)*T + expJetConstant m C*A*Real.exp c⁻¹) *
        (n^(D+1))⁻¹ * Real.exp (n*φ) := by
  dsimp only
  let T := expJetConstant m C * A * ((2*(m+(D+3))).factorial : ℝ) * Real.exp c⁻¹
  let U := expJetConstant m C * A * Real.exp c⁻¹
  let V := Real.exp (n*φ)
  have hn0 := zero_lt_one.trans_le hn
  have hnn : ‖(n : ℂ)‖ = n := by simp [abs_of_pos hn0]
  have hT : 0 ≤ T := by
    dsimp [T]; exact mul_nonneg (mul_nonneg
      (mul_nonneg (expJetConstant_nonneg _ (zero_le_one.trans hC)) hA)
      (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hU : 0 ≤ U := mul_nonneg
    (mul_nonneg (expJetConstant_nonneg _ (zero_le_one.trans hC)) hA) (Real.exp_pos _).le
  have hV : 0 < V := Real.exp_pos _
  have he : ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S y)) :=
    (contDiff_const.mul hS).cexp
  have hEF (j : ℕ) : ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S y)*F j y) := he.mul (hF j)
  have hER (j : ℕ) : ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S y)*R j y) := he.mul (hR j)
  have hEL : ContDiff ℝ ∞ (fun y => Complex.exp ((n : ℂ)*S y)*L y) := he.mul hL
  have hFS := norm_iteratedFDeriv_weighted_sum _ hEF J m x
    ((n : ℂ)⁻¹) (inverse_frequency_norm_le_one hn) (T * (n^(D+3))⁻¹ * V)
    (by positivity) (fun j hj => scheduled_taylor_wave_bound S (F j) hS (hF j)
      m D x C A n φ c r hC hA hn hc hr hx hSjets (hFzero j hj) (hFbound j hj) hphase)
  have hRS := norm_iteratedFDeriv_weighted_sum _ hER J m x
    ((n : ℂ)⁻¹) (inverse_frequency_norm_le_one hn) (T * (n^(D+3))⁻¹ * V)
    (by positivity) (fun j hj => scheduled_taylor_wave_bound S (R j) hS (hR j)
      m D x C A n φ c r hC hA hn hc hr hx hSjets (hRzero j hj) (hRbound j hj) hphase)
  have hLB := bounded_wave_term S L hS hL m x C A n φ c hC hA hn hc hSjets hLbound hphase
  have hSF : ContDiff ℝ ∞ (fun y => ∑ j ∈ Finset.range (J+1),
      ((n : ℂ)⁻¹)^j * (Complex.exp ((n : ℂ)*S y)*F j y)) :=
    ContDiff.sum (fun j _ => contDiff_const.mul (hEF j))
  have hSR : ContDiff ℝ ∞ (fun y => ∑ j ∈ Finset.range (J+1),
      ((n : ℂ)⁻¹)^j * (Complex.exp ((n : ℂ)*S y)*R j y)) :=
    ContDiff.sum (fun j _ => contDiff_const.mul (hER j))
  have htri := norm_iteratedFDeriv_linear_three _ _ _ hSF hSR hEL
    ((n : ℂ)^2) (n : ℂ) (((n : ℂ)⁻¹)^J) m x
  apply htri.trans
  rw [norm_pow, norm_pow, norm_inv, hnn]
  have hb1 := mul_le_mul_of_nonneg_left hFS (pow_nonneg hn0.le 2)
  have hb2 := mul_le_mul_of_nonneg_left hRS hn0.le
  have hb3 := mul_le_mul_of_nonneg_left hLB (pow_nonneg (inv_nonneg.mpr hn0.le) J)
  apply (add_le_add (add_le_add hb1 hb2) hb3).trans
  have hc1 : n^2 * (n^(D+3))⁻¹ = (n^(D+1))⁻¹ := by
    simpa only [show 2+(D+1)=D+3 by omega] using frequency_schedule_cancellation hn0 2 (D+1)
  have hc2 : n * (n^(D+3))⁻¹ ≤ (n^(D+1))⁻¹ := by
    calc
      n * (n^(D+3))⁻¹ ≤ n^2 * (n^(D+3))⁻¹ := by gcongr; exact le_self_pow₀ hn (by omega)
      _ = _ := hc1
  have hc3 : (n⁻¹)^J * n^m ≤ (n^(D+1))⁻¹ := by
    rw [inv_pow]
    calc
      _ ≤ (n^(m+(D+1)))⁻¹ * n^m := by
        exact mul_le_mul_of_nonneg_right
          (frequency_inverse_power_mono hn (by omega)) (pow_nonneg hn0.le _)
      _ = _ := by rw [mul_comm]; exact frequency_schedule_cancellation hn0 m (D+1)
  change n^2 * ((J+1 : ℕ) * (T * (n^(D+3))⁻¹ * V)) +
      n * ((J+1 : ℕ) * (T * (n^(D+3))⁻¹ * V)) +
      (n⁻¹)^J * (U*n^m*V) ≤ _
  calc
    _ = (J+1 : ℕ)*T*V*(n^2*(n^(D+3))⁻¹) +
        (J+1 : ℕ)*T*V*(n*(n^(D+3))⁻¹) + U*V*((n⁻¹)^J*n^m) := by ring
    _ ≤ (J+1 : ℕ)*T*V*(n^(D+1))⁻¹ +
        (J+1 : ℕ)*T*V*(n^(D+1))⁻¹ + U*V*(n^(D+1))⁻¹ := by
      rw [hc1]
      have hh : (J+1 : ℕ)*T*V*(n*(n^(D+3))⁻¹) ≤
          (J+1 : ℕ)*T*V*(n^(D+1))⁻¹ :=
        mul_le_mul_of_nonneg_left hc2 (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hT) hV.le)
      exact add_le_add (add_le_add le_rfl hh)
        (mul_le_mul_of_nonneg_left hc3 (mul_nonneg hU hV.le))
    _ = _ := by dsimp [T,U,V]; ring


end YauCounterexamples
end

end OAI
