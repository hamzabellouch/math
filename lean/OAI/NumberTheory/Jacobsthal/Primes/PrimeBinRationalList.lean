import OAI.NumberTheory.Jacobsthal.Estimates.ActualCollisionBound
import OAI.NumberTheory.Jacobsthal.Primes.HighPrimeRemoval

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin
open _root_.Filter
open scoped Topology

theorem primeBin_log_sum_lower {R xi : ℝ} (hR : 0 < R) (hxi : 0 ≤ xi) :
    (primeBin R xi).card*Real.log R ≤ ∑ p ∈ primeBin R xi,Real.log p := by
  calc
    _ = ∑ _p ∈ primeBin R xi,Real.log R := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log hR ((mem_primeBin hR.le hxi p).mp hp).2.1.le

theorem uniform_prime_bin_count {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 →
      xi*R/(4*Real.log R) ≤ (primeBin R xi).card ∧
      (primeBin R xi).card ≤ 2*xi*R/Real.log R := by
  filter_upwards [uniform_bin_theta_error heta] with R hR
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have hxi0 := heta.le.trans hxi
  have hR0 : 0 < R := by linarith [hR.1]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hR.1])
  have he := hR.2 xi hxi hxi1
  rw [← primeBin_log_sum hR0.le hxi0] at he
  have hlow := (abs_le.mp he).1
  have hhigh := (abs_le.mp he).2
  have hcountupper := primeBin_log_sum_upper hR.1 hxi0 hxi1
  have hcountlower := primeBin_log_sum_lower hR0 hxi0
  constructor
  · apply (div_le_iff₀ (show 0 < 4*Real.log R by positivity)).mpr
    nlinarith only [hlow,hcountupper]
  · apply (le_div_iff₀ hlog).mpr
    have hprod := mul_nonneg hxi0 hR0.le
    nlinarith only [hhigh,hcountlower,hprod]

theorem log_le_two_sqrt {R : ℝ} (hR : 0 < R) : Real.log R ≤ 2*Real.sqrt R := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hR)
  have he : Real.log R = 2*Real.log (Real.sqrt R) := by
    rw [← Real.sq_sqrt hR.le,Real.log_pow]
    norm_num
  rw [he]
  linarith

theorem bin_scale_sqrt_lower {R xi eta : ℝ} (hR : 2 ≤ R) (heta : 0 < eta) (hxi : eta ≤ xi) :
    eta*Real.sqrt R/8 ≤ xi*R/(4*Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) (show 0 < 4*Real.log R by positivity)).mpr
  have hlogbound := mul_le_mul_of_nonneg_left (log_le_two_sqrt hR0)
    (show 0 ≤ eta*Real.sqrt R by positivity)
  have hRxi := mul_le_mul_of_nonneg_right hxi hR0.le
  have hs := Real.sq_sqrt hR0.le
  have he : eta*Real.sqrt R*(2*Real.sqrt R) = 2*eta*R := by
    calc
      _ = 2*eta*(Real.sqrt R)^2 := by ring
      _ = _ := by rw [hs]
  rw [he] at hlogbound
  nlinarith only [hlogbound,hRxi]

end ErdosInversePrimeBin

end

section

namespace ErdosInversePrimeBin
open _root_.Filter
open scoped Topology

theorem uniform_prime_bin_many {eta : ℝ} (heta : 0 < eta) (N : ℕ) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 → N ≤ (primeBin R xi).card := by
  filter_upwards [uniform_prime_bin_count heta,
    eventually_ge_atTop ((8*(N : ℝ)/eta)^2)] with R hR hsize
  have hR0 : 0 < R := by linarith [hR.1]
  have hs : 8*(N : ℝ)/eta ≤ Real.sqrt R :=
    (Real.le_sqrt (by positivity) hR0.le).mpr hsize
  have hn : (N : ℝ) ≤ eta*Real.sqrt R/8 := by
    have h := (div_le_iff₀ heta).mp hs
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    nlinarith only [h]
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have h := hn.trans ((bin_scale_sqrt_lower hR.1 heta hxi).trans (hR.2 xi hxi hxi1).1)
  exact_mod_cast h

end ErdosInversePrimeBin

end

section

namespace ErdosInverseCells
open ErdosInversePrimeBin

theorem prime_bin_weight_spread (R theta xi : ℝ) (hR : 0 < R) (htheta : 0 ≤ theta)
    (hxi : 0 ≤ xi) (hthetaXi : theta ≤ xi) :
    ∀ p ∈ primeBin R theta,∀ r ∈ primeBin R theta,(p : ℝ)⁻¹ ≤ (1+xi)*(r : ℝ)⁻¹ := by
  intro p hp r hr
  have hpm := (mem_primeBin hR.le htheta p).mp hp
  have hrm := (mem_primeBin hR.le htheta r).mp hr
  have hp0 : (0 : ℝ) < p := hR.trans hpm.2.1
  have hr0 : (0 : ℝ) < r := hR.trans hrm.2.1
  have htop : (r : ℝ) ≤ (1+xi)*(p : ℝ) := by
    calc
      _ ≤ (1+theta)*R := hrm.2.2
      _ ≤ (1+xi)*R := mul_le_mul_of_nonneg_right (by linarith) hR.le
      _ ≤ (1+xi)*(p : ℝ) := mul_le_mul_of_nonneg_left hpm.2.1.le (by linarith)
  have hh : (1 : ℝ)/(p : ℝ) ≤ (1+xi)/(r : ℝ) :=
    (div_le_div_iff₀ hp0 hr0).mpr (by simpa only [one_mul] using htop)
  simpa only [one_div,div_eq_mul_inv,one_mul] using hh

end ErdosInverseCells

end

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosInversePrimeBin

theorem prime_bin_log_upper {R xi : ℝ} (hR : 2 ≤ R) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (p : primeBin R xi) : Real.log (p.val : ℝ) ≤ 2*Real.log R := by
  have hR0 : 0 < R := by linarith
  have hp := (mem_primeBin hR0.le hxi0 p.val).mp p.property
  have hp2 : (p.val : ℝ) ≤ 2*R := hp.2.2.trans
    (mul_le_mul_of_nonneg_right (by linarith : 1+xi ≤ 2) hR0.le)
  have hsq : 2*R ≤ R^2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hR hR0.le
  have h := Real.log_le_log (hR0.trans hp.2.1) (hp2.trans hsq)
  simpa only [Real.log_pow,Nat.cast_ofNat] using h

theorem prime_bin_slope_cost_bound {R xi L : ℝ} (hR : 2 ≤ R) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hL : 0 < L) (T : primeBin R xi → Finset ℤ)
    (hcount : ((primeBin R xi).card : ℝ) ≤ 2*R/Real.log R)
    (hthin : (∑ p : primeBin R xi, ((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/L^6) :
    (∑ p : primeBin R xi, ((T p).card : ℝ)*Real.log (p.val : ℝ)) ≤ 4*R^2/L^6 := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  calc
    _ ≤ ∑ p : primeBin R xi, ((T p).card : ℝ)*(2*Real.log R) :=
      Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (prime_bin_log_upper hR hxi0 hxi1 p) (Nat.cast_nonneg _))
    _ = (∑ p : primeBin R xi, ((T p).card : ℝ))*(2*Real.log R) := by rw [Finset.sum_mul]
    _ ≤ (((primeBin R xi).card : ℝ)*R/L^6)*(2*Real.log R) :=
      mul_le_mul_of_nonneg_right hthin (by positivity)
    _ ≤ ((2*R/Real.log R)*R/L^6)*(2*Real.log R) := by gcongr
    _ = 4*R^2/L^6 := by field_simp; ring

theorem rich_prime_log_lower {R xi eta c : ℝ} (hR : 2 ≤ R) (heta : 0 < eta)
    (hxi : eta ≤ xi) (hc : 0 ≤ c)
    (hcount : xi*R/(4*Real.log R) ≤ ((primeBin R xi).card : ℝ))
    (I : Finset ℕ) (hIP : I ⊆ primeBin R xi)
    (hrich : c*((primeBin R xi).card : ℝ) ≤ (I.card : ℝ)) :
    c*eta*R/4 ≤ ∑ p ∈ I, Real.log (p : ℝ) := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log R := Real.log_pos (by linarith)
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hsum : (I.card : ℝ)*Real.log R ≤ ∑ p ∈ I, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ I, Real.log R := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p hp =>
        Real.log_le_log hR0 ((mem_primeBin hR0.le hxi0 p).mp (hIP hp)).2.1.le)
  calc
    c*eta*R/4 ≤ c*xi*R/4 := by gcongr
    _ = c*(xi*R/(4*Real.log R))*Real.log R := by field_simp
    _ ≤ c*((primeBin R xi).card : ℝ)*Real.log R := by gcongr
    _ ≤ (I.card : ℝ)*Real.log R := mul_le_mul_of_nonneg_right hrich hlog.le
    _ ≤ _ := hsum

theorem uniform_prime_bin_budgets {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop, 2 ≤ R ∧ ∀ xi : ℝ, eta ≤ xi → xi ≤ 1 →
      (∀ L : ℝ, 0 < L → ∀ T : primeBin R xi → Finset ℤ,
        (∑ p : primeBin R xi, ((T p).card : ℝ)) ≤ ((primeBin R xi).card : ℝ)*R/L^6 →
        (∑ p : primeBin R xi, ((T p).card : ℝ)*Real.log (p.val : ℝ)) ≤ 4*R^2/L^6) ∧
      (∀ c : ℝ, 0 ≤ c → ∀ I : Finset ℕ, I ⊆ primeBin R xi →
        c*((primeBin R xi).card : ℝ) ≤ (I.card : ℝ) → c*eta*R/4 ≤ ∑ p ∈ I, Real.log (p : ℝ)) := by
  filter_upwards [uniform_prime_bin_count heta] with R hR
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have hxi0 := heta.le.trans hxi
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hR.1])
  have hR0 : 0 < R := by linarith [hR.1]
  have hbounds := hR.2 xi hxi hxi1
  have hupper : ((primeBin R xi).card : ℝ) ≤ 2*R/Real.log R := by
    apply hbounds.2.trans
    gcongr
    linarith
  exact ⟨fun L hL T hthin => prime_bin_slope_cost_bound hR.1 hxi0 hxi1 hL T hupper hthin,
    fun c hc I hIP hrich => rich_prime_log_lower hR.1 heta hxi hc hbounds.1 I hIP hrich⟩

end ErdosSourcePolynomial

end

section

namespace ErdosInversePrimeBin
open _root_.Filter ErdosInverseAlignment
open scoped Topology

theorem uniform_source_prime_bin_list {eta α C c : ℝ}
    (heta : 0 < eta) (hα : 0 < α) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R xi Sq Z : ℝ,∀ a : ℕ → ℤ,
      z^α ≤ R → eta ≤ xi → xi ≤ 1 → 0 ≤ Sq → 2*Sq*R^2*Z^20 ≤ z^C →
      (sourceRationalList (primeBin R xi) a Sq R Z c).card ≤ ⌈2/c^2⌉₊ := by
  let N : ℕ := ⌈max 1 (2*(C/α)/c^2)⌉₊
  have hN : max 1 (2*(C/α)/c^2) ≤ (N : ℝ) := Nat.le_ceil _
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (uniform_prime_bin_many heta N)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hα).eventually (eventually_ge_atTop R₀)] with z hz hlarge
  refine ⟨hz,?_⟩
  intro R xi Sq Z a hR hxi hxi1 hSq hheight
  have hbin := hR₀ R (hlarge.trans hR)
  have hR0 : 0 ≤ R := by linarith [hbin.1]
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hmany : N ≤ (primeBin R xi).card := hbin.2 xi hxi hxi1
  have hmanyR : (N : ℝ) ≤ ((primeBin R xi).card : ℝ) := by exact_mod_cast hmany
  have hPpos : 0 < (primeBin R xi).card := by
    have hN1 : (1 : ℝ) ≤ N := (le_max_left _ _).trans hN
    have hpositive : (0 : ℝ) < (primeBin R xi).card := by linarith only [hN1,hmanyR]
    exact_mod_cast hpositive
  have henough : 2*(C/α) ≤ c^2*((primeBin R xi).card : ℝ) := by
    have hneed : 2*(C/α)/c^2 ≤ ((primeBin R xi).card : ℝ) :=
      (le_max_right _ _).trans (hN.trans hmanyR)
    simpa only [mul_comm] using (div_le_iff₀ (sq_pos_of_pos hc)).mp hneed
  apply source_rational_list_bound (primeBin R xi) a hSq hR0 hz hα hC hc
  · intro p hp
    exact ((mem_primeBin hR0 hxi0 p).mp hp).1
  · intro p hp
    exact hR.trans ((mem_primeBin hR0 hxi0 p).mp hp).2.1.le
  · exact hheight
  · exact hPpos
  · exact henough

end ErdosInversePrimeBin

end

end Erdos970

end OAI
