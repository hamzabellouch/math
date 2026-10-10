import OAI.NumberTheory.EgyptianFractions.SupplySize
import OAI.NumberTheory.EgyptianFractions.PrimeProductGrowth

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- Prime-prefix supply with an arbitrary logarithmic coefficient. -/
def thinSupplyBase (a : ℝ) (u : ℕ) : ℕ :=
  primePrefixProduct (supplyPrimeCount a u)

lemma thinSupplyBase_pos (a : ℝ) (u : ℕ) : 0 < thinSupplyBase a u :=
  primePrefixProduct_pos _

lemma thinSupplyBase_dvd_mono {a : ℝ} (ha : 0 ≤ a) {u v : ℕ}
    (hu : 0 < u) (huv : u ≤ v) : thinSupplyBase a u ∣ thinSupplyBase a v := by
  apply primePrefixProduct_dvd_mono
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ ha
  exact Real.log_le_log (by exact_mod_cast hu) (by exact_mod_cast huv)

lemma thinSupplyBase_fourth_power (a : ℝ) (m : ℕ) :
    thinSupplyBase a (m ^ 4) = thinSupplyBase (4 * a) m := by
  unfold thinSupplyBase supplyPrimeCount
  rw [Nat.cast_pow, Real.log_pow]
  congr 2
  ring

lemma thinSupplyBase_sq_dvd_supplyInteger {a : ℝ} (ha : 0 ≤ a)
    {u m : ℕ} (hu : 0 < u) (hum : u ≤ m ^ 4) :
    thinSupplyBase a u ^ 2 ∣ supplyInteger (4 * a) m := by
  have hd := thinSupplyBase_dvd_mono ha hu hum
  rw [thinSupplyBase_fourth_power] at hd
  exact (pow_dvd_pow_of_dvd hd 2).trans (dvd_mul_right _ _)

/-- The exact divisor cardinality already dominates the real power dictated by
its logarithmic prime-prefix coefficient. -/
lemma rpow_le_divisors_card_thinSupplyBase (a : ℝ) {u : ℕ} (hu : 0 < u) :
    (u : ℝ) ^ (a * Real.log 2) ≤ ((thinSupplyBase a u).divisors.card : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  rw [thinSupplyBase, card_divisors_primePrefixProduct, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.rpow_def_of_pos huR]
  have hceil : a * Real.log (u : ℝ) ≤ (supplyPrimeCount a u : ℝ) := Nat.le_ceil _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.log (u : ℝ) * (a * Real.log 2) ≤
      (supplyPrimeCount a u : ℝ) * Real.log 2 := by nlinarith
  calc
    Real.exp (Real.log (u : ℝ) * (a * Real.log 2)) ≤
        Real.exp ((supplyPrimeCount a u : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
    _ = (2 : ℝ) ^ supplyPrimeCount a u := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Only a small power margin, not the manuscript's fourth-power overkill,
is needed to ensure the factor-two collision-cardinality hypothesis. -/
theorem eventually_twice_rpow_le_divisors_card_thinSupplyBase
    (a θ : ℝ) (hgap : θ < a * Real.log 2) :
    ∀ᶠ u : ℕ in atTop,
      2 * (u : ℝ) ^ θ ≤ ((thinSupplyBase a u).divisors.card : ℝ) := by
  have hδ : 0 < a * Real.log 2 - θ := by linarith
  have ht : Tendsto (fun u : ℕ => Real.log (u : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (Real.log 2 / (a * Real.log 2 - θ)),
    eventually_ge_atTop (1 : ℕ)] with u hlarge hu
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hprod : Real.log 2 ≤ Real.log (u : ℝ) * (a * Real.log 2 - θ) :=
    (div_le_iff₀ hδ).mp hlarge
  calc
    2 * (u : ℝ) ^ θ = Real.exp (Real.log 2 + Real.log (u : ℝ) * θ) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos huR]
    _ ≤ Real.exp (Real.log (u : ℝ) * (a * Real.log 2)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = (u : ℝ) ^ (a * Real.log 2) := (Real.rpow_def_of_pos huR _).symm
    _ ≤ _ := rpow_le_divisors_card_thinSupplyBase a hu

/-- Sharp leading logarithmic size of the smaller prime-prefix base itself. -/
theorem eventually_log_thinSupplyBase_le (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      Real.log (thinSupplyBase a u : ℝ) ≤
        (a + ε) * Real.log (u : ℝ) * Real.log (Real.log (u : ℝ)) := by
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_log_primePrefixProduct_ceil_le a ε ha hε)

/-- The nested common multiplier has leading logarithmic size `8*a`. -/
theorem eventually_log_thinSupplyInteger_le (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (supplyInteger (4 * a) m : ℝ) ≤
        (8 * a + ε) * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by
  simpa only [show (2 : ℝ) * (4 * a) = 8 * a by ring] using
    (eventually_log_supplyInteger_le (a := 4 * a) (by positivity) hε)

lemma lt_thinSupplyInteger {a : ℝ} (ha : 1 < 8 * a * Real.log 2)
    {m : ℕ} (hm : 2 ≤ m) : m < supplyInteger (4 * a) m := by
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hlower := log_supplyInteger_lower (4 * a) m
  have hstrict : Real.log (m : ℝ) < 8 * a * Real.log 2 * Real.log (m : ℝ) := by
    nlinarith
  by_contra h
  have hle : supplyInteger (4 * a) m ≤ m := by omega
  have hlogle : Real.log (supplyInteger (4 * a) m : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by exact_mod_cast supplyInteger_pos (4 * a) m)
      (by exact_mod_cast hle)
  nlinarith

end Problem337

end

end OAI
