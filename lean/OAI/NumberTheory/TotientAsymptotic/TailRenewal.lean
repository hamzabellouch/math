import OAI.NumberTheory.TotientAsymptotic.TailVolume
import OAI.NumberTheory.TotientAsymptotic.RenewalConvolution
import OAI.NumberTheory.TotientAsymptotic.BandComparison

namespace OAI

/-! The normalized finite-tail budget and its renewal-convolution limit. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

def tailSequence {H : ℕ} (T : Finset (TailDatum H)) (n : ℕ) : ℝ :=
  rho^(H+n)*maxD (H+n) T

lemma tailBudget_eq_sum (x : ℝ) (H : ℕ) (T : Finset (TailDatum H)) :
    tailBudget x H T =
      ∑ i ∈ Finset.range (R x H+1), g i*maxD (m x-i) T := by
  rw [Finset.sum_range_succ']
  have hg0 : g 0 = 1 := by simp [g]
  simp only [Nat.sub_zero, hg0, one_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  unfold tailBudget
  ring

lemma renewalConvolution_tailSequence (x : ℝ) (H : ℕ) (T : Finset (TailDatum H))
    (hm : H ≤ m x) :
    renewalConvolution (tailSequence T) (R x H) = rho^(m x)*tailBudget x H T := by
  rw [renewalConvolution, tailBudget_eq_sum, Finset.mul_sum]
  apply Finset.sum_bij (fun i _ => R x H-i)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (by omega)
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    omega
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    exact ⟨R x H-j, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    have hR : R x H = m x-H := rfl
    have hidx : m x-(R x H-i) = H+i := by omega
    have hexp : (R x H-i)+(H+i) = m x := by omega
    have hpow : rho^(R x H-i)*rho^(H+i) = rho^(m x) := by
      rw [← pow_add, hexp]
    dsimp [normalizedRenewal, tailSequence]
    rw [hidx]
    calc
      _ = (rho^(R x H-i)*rho^(H+i)) *
          (g (R x H-i)*maxD (H+i) T) := by ring
      _ = _ := by rw [hpow]

/-- The exact tail budget converges after multiplication by `rho^m`.
This is the analytic numerator in the manuscript's finite-tail approximation. -/
theorem normalized_tailBudget_tendsto (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ => rho^(m x)*tailBudget x H T) atTop
      (nhds (gamma * ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)) := by
  have hc : Summable (tailSequence T) := summable_tail_threshold hT
  have hh := (renewalConvolution_tendsto hford (tailSequence T) hc).comp
    ((tendsto_sub_atTop_nat H).comp m_tendsto)
  apply hh.congr'
  filter_upwards [m_tendsto.eventually (eventually_ge_atTop H)] with x hx
  exact renewalConvolution_tailSequence x H T hx

lemma alpha_ge_lam {s : ℝ} (hs : 0 ≤ s) : lam ≤ alpha s := by
  unfold alpha
  have he : 1 ≤ Real.exp (lam*s) := Real.one_le_exp (mul_nonneg lam_pos.le hs)
  nlinarith [lam_pos]

lemma phase_division_error {ι : Type*} {l : Filter ι} (z v a : ι → ℝ)
    (L c : ℝ) (hc : 0 < c) (hz : Tendsto z l (nhds L))
    (hv : Tendsto v l (nhds 1)) (ha : ∀ᶠ x in l, c ≤ a x) :
    Tendsto (fun x => z x/(a x*v x)-L/a x) l (nhds 0) := by
  have ht : Tendsto (fun x => z x/v x-L) l (nhds 0) := by
    simpa using (hz.div hv (by norm_num : (1 : ℝ) ≠ 0)).sub_const L
  apply squeeze_zero_norm' (a := fun x => |z x/v x-L|/c)
  · filter_upwards [ha] with x hx
    have he : z x/(a x*v x)-L/a x = (z x/v x-L)/a x := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos (hc.trans_le hx)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc hx
  · simpa using ht.abs.div_const c

/-- The phase-dependent exponent in the simplex volume, before replacing `m`
by the prefix dimension `m-H`. -/
theorem tailBudget_exponent_error (hford : FordRenewalInput)
    {H : ℕ} {s : ℝ} (T : Finset (TailDatum H))
    (hT : ∀ η ∈ T, IsWitness H s η) :
    Tendsto (fun x : ℝ => (m x : ℝ)*tailBudget x H T/B x -
      (gamma / alpha (theta x)) * ∑' n : ℕ, rho^(H+n)*maxD (H+n) T)
      atTop (nhds 0) := by
  have hphase : ∀ᶠ x : ℝ in atTop, lam ≤ alpha (theta x) :=
    theta_eventually_mem.mono (fun _ hx => alpha_ge_lam hx.1)
  have hh := phase_division_error
    (fun x : ℝ => rho^(m x)*tailBudget x H T) bandCenterRatio
    (fun x => alpha (theta x))
    (gamma * ∑' n : ℕ, rho^(H+n)*maxD (H+n) T) lam lam_pos
    (normalized_tailBudget_tendsto hford T hT) bandCenterRatio_tendsto hphase
  apply hh.congr'
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    m_tendsto.eventually (eventually_gt_atTop 0)] with x hB hm
  have hmn : (m x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hr : rho^(m x) ≠ 0 := pow_ne_zero _ rho_pos.ne'
  have hl : Real.log (B x) ≠ 0 := (Real.log_pos hB).ne'
  rw [alpha_theta_eq hB]
  unfold bandCenterRatio
  field_simp [hmn, hr, hl, lam_pos.ne', (zero_lt_one.trans hB).ne']

end TotientAsymptotic

end

end OAI
