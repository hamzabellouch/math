import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductResidueInterval
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductLocalLaw

namespace OAI

/-! # The uniform residue-restricted local prime-product law -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The actual prime-product probability of a log-coordinate interval in a unit class. -/
theorem primeProduct_residue_log_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        0 < a → a ≤ b → b ≤ 4 →
        9 ≤ Real.exp (B * a) → (B : ℝ) ^ (89 / 100 : ℝ) ≤ B * a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) + K * (B : ℝ) ^ (-D) * (2 + B * (b - a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_residue_interval_law hSD hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hsize hscale q _ hq r
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB0
  have hexp : Real.exp (B * a) ≤ Real.exp (B * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hupper : Real.exp (B * b) ≤ auxiliaryUpper B := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h := hB (Real.exp (B * a)) (Real.exp (B * b)) hsize hexp hupper
    (by simpa only [Real.log_exp] using hscale) q hq r
  rw [← scaledRoughDensity_integral c z H B hB0 ha hab] at h
  have hlog : Real.log (Real.exp (B * b) / Real.exp (B * a)) = B * (b - a) := by
    rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring
  simpa only [hlog] using h


open Classical in
/-- All intervals in the range have the same absolute error constant. -/
theorem primeProduct_residue_local_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤ C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_residue_log_interval_law hSD hSW hM hz (by norm_num : (0 : ℝ) ≤ 81)
  refine ⟨c, hc0, hcpos, H, 1 + 6 * K, by positivity, ?_⟩
  have hlarge : ∀ᶠ B : ℕ in atTop, (9 : ℝ) ≤ (B : ℝ) ^ (9 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 9)
  filter_upwards [hbound, hlarge, eventually_ge_atTop 1] with B hB hlargeB hB1
  intro a b ha hab hb q _ hq r
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hB0 : (0 : ℝ) < B := by linarith
  obtain ⟨ha0, hsize, hscale⟩ := auxiliary_log_endpoint_conditions hB1 ha hlargeB
  have h := hB a b ha0 hab (by linarith) hsize hscale q hq r
  have hzsq : z ^ 2 ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have htail : z ^ 2 / (auxiliaryCutoff B : ℝ) ≤ (B : ℝ) ^ (-(80 : ℝ)) := by
    calc
      _ ≤ 1 / (auxiliaryCutoff B : ℝ) :=
        div_le_div_of_nonneg_right hzsq (by positivity)
      _ = (B : ℝ) ^ (-(1000 : ℝ)) := by
        rw [Real.rpow_neg hB0.le]
        norm_num [auxiliaryCutoff]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hBreal (by norm_num)
  have hlen : 2 + (B : ℝ) * (b - a) ≤ 6 * B := by nlinarith
  have hpoly : K * (B : ℝ) ^ (-(81 : ℝ)) * (2 + (B : ℝ) * (b - a)) ≤
      6 * K * (B : ℝ) ^ (-(80 : ℝ)) := by
    calc
      _ ≤ K * (B : ℝ) ^ (-(81 : ℝ)) * (6 * B) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = _ := by
        have heq : (B : ℝ) ^ (-(81 : ℝ)) * B = (B : ℝ) ^ (-(80 : ℝ)) := by
          rw [show (-(80 : ℝ)) = -81 + 1 by norm_num, Real.rpow_add hB0, Real.rpow_one]
        nlinarith [heq]
  calc
    _ ≤ z ^ 2 / (auxiliaryCutoff B : ℝ) +
        K * (B : ℝ) ^ (-(81 : ℝ)) * (2 + B * (b - a)) := h
    _ ≤ (B : ℝ) ^ (-(80 : ℝ)) + 6 * K * (B : ℝ) ^ (-(80 : ℝ)) := add_le_add htail hpoly
    _ = _ := by ring


end JointDickman

end OAI
