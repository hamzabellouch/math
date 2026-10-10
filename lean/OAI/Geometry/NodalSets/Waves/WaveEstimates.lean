import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Waves
open Set Filter
open scoped Topology ContDiff
noncomputable section
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedDeriv_line {f : E → F} {n k : ℕ} (hf : ContDiff ℝ n f)
    (hk : k ≤ n) (y z : E) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ ↦ f (y + s • z)) t =
      iteratedFDeriv ℝ k f (y + t • z) (fun _ ↦ z) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight z
  have hshift : ContDiff ℝ n (fun x ↦ f (y + x)) :=
    hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k ((fun x ↦ f (y + x)) ∘ L) t (fun _ ↦ 1) = _
  rw [L.iteratedFDeriv_comp_right hshift t (by exact_mod_cast hk)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]
  simp [L]

theorem vanishing_jet_taylor_bound {f : E → F} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    (y z : E) (C : ℝ)
    (hzero : ∀ k, k ≤ n → iteratedFDeriv ℝ k f y = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (n + 1) f (y + t • z)‖ ≤ C) :
    ‖f (y + z)‖ ≤ C * ‖z‖ ^ (n + 1) / (n.factorial : ℝ) := by
  let g : ℝ → F := fun t ↦ f (y + t • z)
  have hg : ContDiff ℝ (n + 1) g :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hi (k : ℕ) (hk : k ≤ n + 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin k g (Icc (0 : ℝ) 1) t =
        iteratedFDeriv ℝ k f (y + t • z) (fun _ ↦ z) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      (hg.of_le (by exact_mod_cast hk)).contDiffAt ht]
    exact iteratedDeriv_line hf hk y z t
  have htaylor : taylorWithinEval g n (Icc (0 : ℝ) 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hi k (by have := Finset.mem_range.mp hk; omega) 0 (by constructor <;> norm_num)]
    simp [hzero k (by have := Finset.mem_range.mp hk; omega)]
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin (n + 1) g (Icc (0 : ℝ) 1) t‖ ≤ C * ‖z‖ ^ (n + 1) := by
    intro t ht
    rw [hi (n + 1) le_rfl t ht]
    calc
      _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (y + t • z)‖ * ∏ _ : Fin (n + 1), ‖z‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C * ‖z‖ ^ (n + 1) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right (hbound t ht) (pow_nonneg (norm_nonneg _) _)
  have h := taylor_mean_remainder_bound (by norm_num : (0 : ℝ) ≤ 1)
    hg.contDiffOn (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hderiv
  simpa [htaylor, g] using h

theorem vanishing_jet_derivative_bound {f : E → F} {m l : ℕ}
    (hf : ContDiff ℝ ∞ f) (hl : l ≤ m) (y z : E) (C : ℝ)
    (hzero : ∀ k, k ≤ m → iteratedFDeriv ℝ k f y = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (m + 1) f (y + t • z)‖ ≤ C) :
    ‖iteratedFDeriv ℝ l f (y + z)‖ ≤
      C * ‖z‖ ^ (m + 1 - l) / ((m - l).factorial : ℝ) := by
  induction l generalizing F m with
  | zero =>
    have hf0 : ContDiff ℝ (m + 1 : ℕ) f := hf.of_le (by
      exact_mod_cast (show (m + 1 : ℕ∞) ≤ ⊤ from le_top))
    simpa [norm_iteratedFDeriv_zero] using
      vanishing_jet_taylor_bound (n := m) hf0 y z C hzero hbound
  | succ l ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hf' : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
      have hz' : ∀ k, k ≤ m → iteratedFDeriv ℝ k (fderiv ℝ f) y = 0 := by
        intro k hk
        apply norm_eq_zero.mp
        rw [norm_iteratedFDeriv_fderiv, hzero (k + 1) (by omega), norm_zero]
      have hb' : ∀ t ∈ Icc (0 : ℝ) 1,
          ‖iteratedFDeriv ℝ (m + 1) (fderiv ℝ f) (y + t • z)‖ ≤ C := by
        intro t ht
        rw [norm_iteratedFDeriv_fderiv]
        exact hbound t ht
      have h := ih hf' (by omega : l ≤ m) hz' hb'
      simpa [norm_iteratedFDeriv_fderiv] using h

theorem quadratic_gap_of_cubic_remainder {eta C r gap : ℝ}
    (hr : 0 ≤ r) (hsmall : C * r ≤ eta / 4)
    (hgap : gap ≤ -(eta / 2) * r ^ 2 + C * r ^ 3) :
    gap ≤ -(eta / 4) * r ^ 2 := by
  have := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hr hr)
  nlinarith

theorem complex_exponential_gaussian_bound {phi : ℂ} {S c N r : ℝ}
    (hN : 0 ≤ N) (hgap : phi.re - S ≤ -c * r ^ 2) :
    ‖Complex.exp ((N : ℂ) * phi)‖ ≤ Real.exp (N * S - c * N * r ^ 2) := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left hgap hN
  nlinarith

theorem gaussian_absorbs_power (c : ℝ) (hc : 0 < c) (p K : ℝ) :
    ∀ᶠ N : ℝ in atTop,
      N ^ p * Real.exp (-c * N ^ (1 / 3 : ℝ)) ≤ N ^ (-K) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (3 * (p + K)) c hc).comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3))
  have he : ∀ᶠ N : ℝ in atTop,
      (N ^ (1 / 3 : ℝ)) ^ (3 * (p + K)) * Real.exp (-c * N ^ (1 / 3 : ℝ)) ≤ 1 :=
    ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with N hN hpos
  have heq : (N ^ (1 / 3 : ℝ)) ^ (3 * (p + K)) = N ^ (p + K) := by
    rw [← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [heq] at hN
  rw [Real.rpow_neg hpos.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hpos K)]
  simpa [Real.rpow_add hpos, mul_assoc, mul_left_comm, mul_comm] using hN

theorem gaussian_cutoff_bound (c b : ℝ) (hc : 0 < c) (hb : 0 < b) (p K : ℝ) :
    ∀ᶠ N : ℝ in atTop, ∀ S r A : ℝ, 0 ≤ A →
      b * N ^ (1 / 3 : ℝ) ≤ N * r ^ 2 →
      A * N ^ p * Real.exp (N * S - c * N * r ^ 2) ≤
        A * N ^ (-K) * Real.exp (N * S) := by
  filter_upwards [gaussian_absorbs_power (c * b) (mul_pos hc hb) p K,
    eventually_gt_atTop (0 : ℝ)] with N hN hpos
  intro S r A hA hann
  have hexp : Real.exp (-c * N * r ^ 2) ≤ Real.exp (-(c * b) * N ^ (1 / 3 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hann hc.le
    nlinarith
  have hcost : N ^ p * Real.exp (-c * N * r ^ 2) ≤ N ^ (-K) :=
    (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hpos.le _)).trans hN
  have h := mul_le_mul_of_nonneg_left hcost hA
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (N * S)).le
  rw [show N * S - c * N * r ^ 2 = N * S + (-c * N * r ^ 2) by ring,
    Real.exp_add]
  nlinarith [h']

theorem residual_exponent_budgets {m J K k k0 : ℕ}
    (hm : 3 * K + 4 * k0 + 6 < m + 1) (hJ : K + k0 + 1 ≤ J) (hk : k ≤ k0) :
    (k : ℝ) + 2 - ((m : ℝ) + 1 - k) / 3 < -(K : ℝ) ∧
    (k : ℤ) - J ≤ -(K : ℤ) - 1 := by
  constructor
  · have hm' : (3 : ℝ) * K + 4 * k0 + 6 < m + 1 := by exact_mod_cast hm
    have hk' : (k : ℝ) ≤ k0 := by exact_mod_cast hk
    linarith
  · omega

theorem scaled_taylor_defect_bound {f : E → F} {m K k k0 : ℕ}
    (hf : ContDiff ℝ ∞ f) (hm : 3 * K + 4 * k0 + 6 < m + 1) (hk : k ≤ k0)
    (y z : E) {C R N : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) (hN : 1 ≤ N)
    (hzero : ∀ j, j ≤ m → iteratedFDeriv ℝ j f y = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (m + 1) f (y + t • z)‖ ≤ C)
    (hradius : ‖z‖ ≤ R * N ^ (-1 / 3 : ℝ)) :
    N ^ ((k : ℝ) + 2) * ‖iteratedFDeriv ℝ k f (y + z)‖ ≤
      C * R ^ (m + 1 - k) * N ^ (-(K : ℝ)) := by
  have hkm : k ≤ m := by omega
  have hpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let q : ℕ := m + 1 - k
  have ht := vanishing_jet_derivative_bound hf hkm y z C hzero hbound
  have hfact : (1 : ℝ) ≤ ((m - k).factorial : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (m - k))
  have hsmall : ‖iteratedFDeriv ℝ k f (y + z)‖ ≤ C * (R * N ^ (-1 / 3 : ℝ)) ^ q := by
    calc
      _ ≤ C * ‖z‖ ^ q := ht.trans (div_le_self (mul_nonneg hC (pow_nonneg (norm_nonneg _) _)) hfact)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hradius q) hC
  have hp : (N ^ (-1 / 3 : ℝ)) ^ q = N ^ (-(q : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  have he : (k : ℝ) + 2 + (-(q : ℝ) / 3) ≤ -(K : ℝ) := by
    have hq : (q : ℝ) = (m : ℝ) + 1 - k := by
      dsimp [q]
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    rw [hq]
    have hm' : (3 : ℝ) * K + 4 * k0 + 6 < m + 1 := by exact_mod_cast hm
    have hk' : (k : ℝ) ≤ k0 := by exact_mod_cast hk
    linarith
  calc
    _ ≤ N ^ ((k : ℝ) + 2) * (C * (R * N ^ (-1 / 3 : ℝ)) ^ q) :=
      mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hpos.le _)
    _ = C * R ^ q * N ^ ((k : ℝ) + 2 + (-(q : ℝ) / 3)) := by
      rw [mul_pow, hp, Real.rpow_add hpos ((k : ℝ) + 2) (-(q : ℝ) / 3)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN he)
      (mul_nonneg hC (pow_nonneg hR _))

end
end Yau.Waves

end OAI
