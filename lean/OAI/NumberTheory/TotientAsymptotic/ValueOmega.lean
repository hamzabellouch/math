import OAI.NumberTheory.TotientAsymptotic.PreimageOmega
import OAI.NumberTheory.TotientAsymptotic.BandComparison

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def largeOmegaValues (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n => 20*B x < (n.primeFactorsList.length : ℝ))

/-- A deliberately coarse factor-count cutoff still has vanishing relative
cost and supplies the head-prime lower bound in every remaining preimage. -/
theorem large_omega_value_count (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      ((largeOmegaValues x).card : ℝ) ≤ (C/Real.log x)*(x/Real.log x) := by
  obtain ⟨D,hD,hprod⟩ := hmertens
  refine ⟨D^3,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ),B_tendsto.eventually (eventually_ge_atTop (0 : ℝ))]
    with x hx hB
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlog := Real.log_pos hx1
  have hN : 2 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by norm_num; linarith)
  have hQ (n : ℕ) (hn : n ∈ largeOmegaValues x) :
      0 < n ∧ n ≤ ⌊x⌋₊ ∧ 20*B x ≤ (n.primeFactorsList.length : ℝ) := by
    obtain ⟨hi,hh⟩ := Finset.mem_filter.mp hn
    exact ⟨(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,hh.le⟩
  have hcount : ((largeOmegaValues x).card : ℝ) ≤ x*∑ n ∈ largeOmegaValues x, (n : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ _n ∈ largeOmegaValues x, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        have hn0 : (0 : ℝ)<n := by exact_mod_cast (hQ n hn).1
        have hnx : (n : ℝ) ≤ x := (show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast (hQ n hn).2.1).trans (Nat.floor_le hx0.le)
        simpa only [div_eq_mul_inv] using (one_le_div hn0).mpr hnx
  have hm := omega_exceptional_mass (largeOmegaValues x) hQ
  have hE : primeEulerProduct ⌊x⌋₊ ≤ D*Real.log x := (hprod _ hN).trans
    (mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast (show 0<⌊x⌋₊ by omega))
      (Nat.floor_le hx0.le)) hD.le)
  have hE0 : 0 ≤ primeEulerProduct ⌊x⌋₊ := by
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ)<p := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hpow : (3/2 : ℝ)^(-(20*B x))*(Real.log x)^5 ≤ 1 := by
    have hl : (1/3 : ℝ) ≤ Real.log (3/2 : ℝ) := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ)<3/2)
      norm_num at hh ⊢
      exact hh
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ)<3/2)]
    have he : (Real.log x)^5=Real.exp (5*B x) := by
      calc
        _ = (Real.exp (B x))^5 := by rw [B,Real.exp_log hlog]
        _ = _ := (Real.exp_nat_mul (B x) 5).symm
    rw [he,← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  calc
    _ ≤ x*((3/2 : ℝ)^(-(20*B x))*(primeEulerProduct ⌊x⌋₊)^3) :=
      hcount.trans (mul_le_mul_of_nonneg_left hm hx0.le)
    _ ≤ x*((3/2 : ℝ)^(-(20*B x))*(D*Real.log x)^3) := by
      gcongr
    _ = D^3*x*((3/2 : ℝ)^(-(20*B x))*(Real.log x)^3) := by ring
    _ ≤ D^3*x*(1/(Real.log x)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
      convert hpow using 1
      ring
    _ = (D^3/Real.log x)*(x/Real.log x) := by field_simp

end TotientAsymptotic

end

end OAI
