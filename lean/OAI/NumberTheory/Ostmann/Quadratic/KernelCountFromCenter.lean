import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterCoefficientBudget
import OAI.NumberTheory.Ostmann.Quadratic.KernelAmplificationMargin

namespace OAI

/-! # The quadratic sieve counts the kernels of the actual common-center bias -/

namespace Ostmann

open Filter

theorem quadratic_count_scalar_budget (C F E S M g T : ℝ)
    (hC : 0 ≤ C) (hF : 0 ≤ F) (hE : 0 ≤ E) (hM : M ≤ S)
    (henergy : S * E ≤ Real.exp (3 * T)) (hgap : g⁻¹ ^ 2 ≤ Real.exp T) :
    C * F * (M + S) * E / g ^ 2 ≤ 2 * C * F * Real.exp (4 * T) := by
  calc
    _ ≤ C * F * (2 * S) * E / g ^ 2 := by gcongr; linarith
    _ = 2 * C * F * (S * E) * (g⁻¹ ^ 2) := by rw [div_eq_mul_inv, inv_pow]; ring
    _ ≤ 2 * C * F * Real.exp (3 * T) * Real.exp T := by gcongr
    _ = 2 * C * F * (Real.exp (3 * T) * Real.exp T) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem eventual_kernel_count_prefactor (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℝ, T ^ (3 / 2 : ℝ) ≤ L →
      2 * C * Real.exp (4 * T) ≤ Real.exp (ε * L) := by
  let D := |Real.log (2 * C)| + 4
  have hD : 0 < D := by dsimp [D]; positivity
  have hp := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop (D / ε)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with T hpow hT L hL
  have hTpos : 0 < T := by linarith
  have hd : D * T ≤ ε * T ^ (3 / 2 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hε).mp hpow) hTpos.le
    have he : T ^ (1 / 2 : ℝ) * T = T ^ (3 / 2 : ℝ) := by
      calc
        _ = T ^ (1 / 2 : ℝ) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = T ^ (1 / 2 + 1 : ℝ) := (Real.rpow_add hTpos _ _).symm
        _ = _ := by norm_num
    rw [mul_right_comm, he] at hh
    nlinarith only [hh]
  have hl : Real.log (2 * C) + 4 * T ≤ ε * L := by
    have hh := mul_le_mul_of_nonneg_left hT (abs_nonneg (Real.log (2 * C)))
    have hll := mul_le_mul_of_nonneg_left hL hε.le
    dsimp [D] at hd
    nlinarith [le_abs_self (Real.log (2 * C))]
  calc
    _ = Real.exp (Real.log (2 * C) + 4 * T) := by rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr hl

/-- A concrete version of the manuscript's X^(3 epsilon + o(1)) count.
The common-center loss and distinct-tuple error are both discharged. -/
theorem eventual_kernel_count_from_commonCenter (sieve : PublishedQuadraticLargeSieve)
    (Cpop : ℝ) (hCpop : 500 ≤ Cpop)
    (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ (L J : ℝ) (P : Finset ℕ) (r Z M : ℕ)
      (e : ℕ → ℂ) (U : Finset ℤ),
      T ^ (3 / 2 : ℝ) ≤ L → 2 ≤ r → (r : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      0 < J → Real.exp T ≤ Cpop * T * J →
      J * Real.exp (-T / (r - 1 : ℕ)) ≤ P.card →
      Real.exp (3 * T / 5) ≤ P.card → (Z : ℝ) ≤ Real.exp (T + 1) →
      1 ≤ Z → 1 ≤ M → M ≤ Z ^ r → ((Z : ℝ) ^ r) ≤ Real.exp (2 * L) →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Odd p) → (∀ p ∈ P, p ≤ Z) →
      (∀ p ∈ P, ‖e p‖ ≤ 1) → U ⊆ signedSquarefreeRange M →
      (∀ u ∈ U, c ≤ ‖quadraticPrimeMean P e u‖) →
      (U.card : ℝ) ≤ Real.exp (3 * ε * L) := by
  obtain ⟨C, hC, hbound⟩ := quadratic_biased_kernel_count sieve (ε / 2) (by positivity)
  filter_upwards [eventual_commonCenter_coefficient_budget Cpop hCpop, eventual_kernel_amplification_margin c hc,
    eventual_kernel_count_prefactor C ε hC hε] with T hcoef hmargin hpref
  intro L J P r Z M e U hL hr hrU hJ hpop hcenter hsize hZupper hZ hM hMS hS
    hP hodd hPZ he hU hbias
  have hcard : (0 : ℝ) < P.card := (Real.exp_pos _).trans_le hsize
  have hcardN : 0 < P.card := by exact_mod_cast hcard
  obtain ⟨_, hgapPos, hgap⟩ := hmargin r P.card hrU hsize
  have henergy := hcoef r J P.card Z hr hrU hJ hcard (Nat.cast_nonneg _) hpop hcenter hZupper
  have hcount := hbound P r Z M e U c hP hodd hPZ he hcardN (by omega) hZ hM hc.le hgapPos hU hbias
  have hMSR : (M : ℝ) ≤ (Z : ℝ) ^ r := by exact_mod_cast hMS
  have heR : (Z : ℝ) ^ r * ((r.factorial : ℝ) / (P.card : ℝ) ^ r) ≤ Real.exp (3 * T) := by
    simpa only [mul_div_assoc] using henergy
  have hb := quadratic_count_scalar_budget C (((M : ℝ) * (Z : ℝ) ^ r) ^ (ε / 2))
    ((r.factorial : ℝ) / (P.card : ℝ) ^ r) ((Z : ℝ) ^ r) M
    (c ^ r - (r : ℝ) ^ 2 / P.card) T hC.le (by positivity) (by positivity) hMSR heR hgap
  have hh : (U.card : ℝ) ≤ 2 * C * (((M : ℝ) * (Z : ℝ) ^ r) ^ (ε / 2)) * Real.exp (4 * T) :=
    hcount.trans hb
  have hprod : (M : ℝ) * (Z : ℝ) ^ r ≤ Real.exp (4 * L) := by
    calc
      _ ≤ Real.exp (2 * L) * Real.exp (2 * L) := mul_le_mul (hMSR.trans hS) hS (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpower : ((M : ℝ) * (Z : ℝ) ^ r) ^ (ε / 2) ≤ Real.exp (2 * ε * L) := by
    calc
      _ ≤ (Real.exp (4 * L)) ^ (ε / 2) := Real.rpow_le_rpow (by positivity) hprod (by positivity)
      _ = _ := by rw [← Real.exp_mul]; congr 1; ring
  calc
    (U.card : ℝ) ≤ _ := hh
    _ = (2 * C * Real.exp (4 * T)) * (((M : ℝ) * (Z : ℝ) ^ r) ^ (ε / 2)) := by ring
    _ ≤ Real.exp (ε * L) * Real.exp (2 * ε * L) := mul_le_mul (hpref L hL) hpower (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
