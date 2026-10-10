import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductLogLaw

namespace OAI

/-!
# Uniform local prime-product law without residue restrictions

This is the modulus-one case of the manuscript's local product law, with
its stated `B^(-80)` absolute error on the shrinking lower-endpoint range.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliary_log_endpoint_conditions {B : ℕ} {a : ℝ}
    (hB : 1 ≤ B) (ha : (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a)
    (hlarge : 9 ≤ (B : ℝ) ^ (9 / 10 : ℝ)) :
    0 < a ∧ 9 ≤ Real.exp (B * a) ∧ (B : ℝ) ^ (89 / 100 : ℝ) ≤ B * a := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hpow : (B : ℝ) * (B : ℝ) ^ (-(1 / 10 : ℝ)) = (B : ℝ) ^ (9 / 10 : ℝ) := by
    rw [show (9 / 10 : ℝ) = 1 + -(1 / 10 : ℝ) by norm_num, Real.rpow_add hB0, Real.rpow_one]
  have hBa : (B : ℝ) ^ (9 / 10 : ℝ) ≤ B * a := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left ha hB0.le
  refine ⟨(Real.rpow_pos_of_pos hB0 _).trans_le ha, ?_, ?_⟩
  · have h := Real.add_one_le_exp ((B : ℝ) * a)
    linarith
  · exact (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (89 / 100 : ℝ) ≤ 9 / 10)).trans hBa

/-- All intervals in the range have the same absolute error constant. -/
theorem primeProduct_local_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        |(∑ n ∈ Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊,
            primeProductMass (auxiliaryPrimes B) z n) -
          ∫ s in a..b, scaledRoughDensity c z H B s| ≤ C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_log_interval_law hSD hM hz 81
  refine ⟨c, hc0, hcpos, H, 1 + 6 * K, by positivity, ?_⟩
  have hlarge : ∀ᶠ B : ℕ in atTop, (9 : ℝ) ≤ (B : ℝ) ^ (9 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 9)
  filter_upwards [hbound, hlarge, eventually_ge_atTop 1] with B hB hlargeB hB1
  intro a b ha hab hb
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hB0 : (0 : ℝ) < B := by linarith
  obtain ⟨ha0, hsize, hscale⟩ := auxiliary_log_endpoint_conditions hB1 ha hlargeB
  have h := hB a b ha0 hab (by linarith) hsize hscale
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
