import OAI.NumberTheory.EgyptianFractions.RoughModulusCollision
import OAI.NumberTheory.EgyptianFractions.ThinSupplyBase
import OAI.NumberTheory.EgyptianFractions.RestrictedRoughAsymptotic

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- Bad moduli on one block use one common divisor list.  This deliberate
fixed-base choice is needed for the off-diagonal double count. -/
def roughModulusBadBlock (D : ℕ) : Finset ℕ := by
  classical
  let A := (thinSupplyBase (2 / Real.log 2) D).divisors
  exact (Finset.Ico D (2 * D)).filter (fun q =>
    (∀ p ∈ q.primeFactorsList, Real.log (2 * (D : ℝ)) ≤ (p : ℝ)) ∧
    (A.card : ℝ) ^ 2 ≤ (q : ℝ) ^ (7 / 8 : ℝ) *
      ((collisionPairs A (fun a => a % q)).card : ℝ))

theorem roughModulusBadBlock_card_le (D : ℕ) (hD : 4 ≤ D)
    (R : ℝ) (hR : 0 ≤ R)
    (hdivisors : ∀ n : ℕ, 0 < n →
      n ≤ thinSupplyBase (2 / Real.log 2) D →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * (D : ℝ) ∧
        ∀ p ∈ d.primeFactorsList, Real.log (2 * (D : ℝ)) ≤ (p : ℝ))).card : ℝ) ≤ R) :
    ((roughModulusBadBlock D).card : ℝ) ≤
      2 * (2 * (D : ℝ)) ^ (7 / 8 : ℝ) * R := by
  classical
  let A := (thinSupplyBase (2 / Real.log 2) D).divisors
  have hDpos : 0 < D := by omega
  have hDR : (4 : ℝ) ≤ D := by exact_mod_cast hD
  have hcard := rpow_le_divisors_card_thinSupplyBase (2 / Real.log 2) hDpos
  have hcoef : (2 / Real.log 2) * Real.log 2 = (2 : ℝ) := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    field_simp
  rw [hcoef, Real.rpow_two] at hcard
  have hpow : (2 * (D : ℝ)) ^ (7 / 8 : ℝ) ≤ 2 * (D : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 * D by linarith) (show (7 / 8 : ℝ) ≤ 1 by norm_num)
  apply moduli_rpow_energy_card_le (roughModulusBadBlock D) A
    (thinSupplyBase (2 / Real.log 2) D) (2 * (D : ℝ)) (7 / 8)
    (fun q => ∀ p ∈ q.primeFactorsList, Real.log (2 * (D : ℝ)) ≤ (p : ℝ))
    (by positivity) (by norm_num) hR
  · intro a ha
    exact ⟨Nat.pos_of_mem_divisors ha, Nat.divisor_le ha⟩
  · intro q hq
    obtain ⟨hqrange, hrough, _⟩ := Finset.mem_filter.mp hq
    exact ⟨by exact_mod_cast (Finset.mem_Ico.mp hqrange).2.le, hrough⟩
  · change 2 * (2 * (D : ℝ)) ^ (7 / 8 : ℝ) ≤
      ((thinSupplyBase (2 / Real.log 2) D).divisors.card : ℝ)
    nlinarith
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.2
  · exact hdivisors

/-- The small subpower divisor error still leaves a fixed power saving in
the bad-modulus count, including the dyadic-block factor of two. -/
lemma roughModulusBlock_power_budget {D : ℝ} (hD : 0 < D)
    (hlarge : 4 ≤ D ^ (1 / 32 : ℝ)) :
    2 * (2 * D) ^ (7 / 8 : ℝ) * (2 * D) ^ (1 / 32 : ℝ) ≤
      D ^ (15 / 16 : ℝ) := by
  have htwo : (2 : ℝ) ^ (29 / 32 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (29 / 32 : ℝ) ≤ 1)
  calc
    2 * (2 * D) ^ (7 / 8 : ℝ) * (2 * D) ^ (1 / 32 : ℝ) =
        2 * (2 * D) ^ (29 / 32 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add (by positivity : 0 < 2 * D)]
      norm_num
    _ = 2 * ((2 : ℝ) ^ (29 / 32 : ℝ) * D ^ (29 / 32 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD.le]
    _ ≤ 4 * D ^ (29 / 32 : ℝ) := by
      nlinarith [Real.rpow_nonneg hD.le (29 / 32),
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hD.le (29 / 32))]
    _ ≤ D ^ (1 / 32 : ℝ) * D ^ (29 / 32 : ℝ) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hD.le _)
    _ = D ^ (15 / 16 : ℝ) := by
      rw [← Real.rpow_add hD]
      norm_num

/-- The actual prime-prefix cardinality and size estimates discharge all
inputs to the block double count except the uniform restricted-divisor
estimate.  That estimate concerns arbitrary positive differences, not
rough ambient integers. -/
theorem eventually_roughModulusBadBlock_card_le_of_divisor_subpower
    (hrough : ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, n ≠ 0 →
      Real.log (n : ℝ) ≤ (2 / Real.log 2 + 1) * Real.log X * Real.log (Real.log X) →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧
        ∀ p ∈ d.primeFactorsList, Real.log X ≤ (p : ℝ))).card : ℝ) ≤
        X ^ (1 / 32 : ℝ)) :
    ∀ᶠ D : ℕ in atTop,
      ((roughModulusBadBlock D).card : ℝ) ≤ (D : ℝ) ^ (15 / 16 : ℝ) := by
  have ha : 0 < (2 : ℝ) / Real.log 2 := by positivity
  have hA : 0 < (2 : ℝ) / Real.log 2 + 1 := by positivity
  have htX : Tendsto (fun D : ℕ => 2 * (D : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have htpow : Tendsto (fun D : ℕ => (D : ℝ) ^ (1 / 32 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp tendsto_natCast_atTop_atTop
  have htlog : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htX.eventually hrough,
    eventually_log_thinSupplyBase_le (2 / Real.log 2) 1 ha zero_lt_one,
    htpow.eventually_ge_atTop 4, htlog.eventually_ge_atTop 1,
    eventually_ge_atTop (4 : ℕ)] with D hroughD hbase hlarge hlogD hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogDX : Real.log (D : ℝ) ≤ Real.log (2 * (D : ℝ)) :=
    Real.log_le_log hDpos (by linarith)
  have hloglogDX : Real.log (Real.log (D : ℝ)) ≤
      Real.log (Real.log (2 * (D : ℝ))) :=
    Real.log_le_log (by linarith) hlogDX
  have hloglogD : 0 ≤ Real.log (Real.log (D : ℝ)) := Real.log_nonneg hlogD
  have hwindow : Real.log (thinSupplyBase (2 / Real.log 2) D : ℝ) ≤
      (2 / Real.log 2 + 1) * Real.log (2 * (D : ℝ)) *
        Real.log (Real.log (2 * (D : ℝ))) := by
    refine hbase.trans ?_
    gcongr
    exact mul_nonneg hA.le (by linarith)
  have hcount := roughModulusBadBlock_card_le D hD
    ((2 * (D : ℝ)) ^ (1 / 32 : ℝ)) (by positivity) (by
      intro n hn hnP
      apply hroughD n hn.ne'
      exact (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnP)).trans hwindow)
  exact hcount.trans (roughModulusBlock_power_budget hDpos hlarge)

/-- An unconditional power-saving bound for the actual bad-modulus blocks.
The common divisor list is the explicit logarithmic prime prefix, and the
restricted-divisor estimate has been discharged for every positive difference. -/
theorem eventually_roughModulusBadBlock_card_le :
    ∀ᶠ D : ℕ in atTop,
      ((roughModulusBadBlock D).card : ℝ) ≤ (D : ℝ) ^ (15 / 16 : ℝ) := by
  apply eventually_roughModulusBadBlock_card_le_of_divisor_subpower
  filter_upwards [eventually_card_rough_divisors_subpower
    (2 / Real.log 2 + 1) (1 / 32) (by positivity) (by norm_num)] with X hX
  intro n hn hsize
  exact hX n hn hsize (Real.log X) le_rfl

end Problem337

end

end OAI
