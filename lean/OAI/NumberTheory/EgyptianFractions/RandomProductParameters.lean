import Mathlib

namespace OAI
noncomputable section

namespace Problem337.RandomProducts

/-- The short fresh-product length, with the constants used in the random
residue construction. -/
def freshLength (S V : ℝ) : ℕ := ⌊(3 / 4 : ℝ) * V / (100 * Real.log S)⌋₊

def blockLength (S : ℝ) : ℕ := ⌊S / Real.log S⌋₊

theorem freshLength_bounds {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) :
    (74 / 100 : ℝ) * V / (100 * Real.log S) ≤ freshLength S V ∧
    (freshLength S V : ℝ) ≤ (3 / 4 : ℝ) * V / (100 * Real.log S) := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hVpos : 0 < V := by nlinarith
  have hx : 0 ≤ (3 / 4 : ℝ) * V / (100 * Real.log S) := by positivity
  constructor
  · have hfloor := Nat.sub_one_lt_floor ((3 / 4 : ℝ) * V / (100 * Real.log S))
    dsimp [freshLength]
    have hdiff : (74 / 100 : ℝ) * V / (100 * Real.log S) ≤
        (3 / 4 : ℝ) * V / (100 * Real.log S) - 1 := by
      apply (le_sub_iff_add_le).mpr
      apply (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mpr
      field_simp
      nlinarith
    linarith
  · exact Nat.floor_le hx

theorem freshLength_eight_le_blockLength {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    8 * freshLength S V ≤ blockLength S := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hSpos : 0 < S := by linarith
  have hb : 2 ≤ S / Real.log S := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith
  have hf := (freshLength_bounds hS hV).2
  have hfloor := Nat.sub_one_lt_floor (S / Real.log S)
  have hscale : (8 : ℝ) * freshLength S V ≤ (6 / 100 : ℝ) * (S / Real.log S) := by
    have := mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 8)
    have hdiv : V / Real.log S ≤ S / Real.log S := div_le_div_of_nonneg_right hVS hlog.le
    calc
      (8 : ℝ) * freshLength S V ≤ 8 * ((3 / 4 : ℝ) * V / (100 * Real.log S)) := this
      _ = (6 / 100 : ℝ) * (V / Real.log S) := by ring
      _ ≤ (6 / 100 : ℝ) * (S / Real.log S) := by gcongr
  have hreal : (8 : ℝ) * freshLength S V ≤ (blockLength S : ℝ) := by
    dsimp [blockLength]
    nlinarith
  exact_mod_cast hreal

/-- Every fresh product is shorter than the reduced modulus threshold. -/
theorem fresh_product_le_exp {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) :
    (2 * S ^ 100) ^ freshLength S V ≤ Real.exp ((4 / 5 : ℝ) * V) := by
  have hSone : 1 < S := by linarith
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hSone
  have hVpos : 0 < V := by nlinarith
  have hlogtwo : Real.log 2 ≤ Real.log S := Real.log_le_log (by norm_num) hS
  have hf := (freshLength_bounds hSone hV).2
  have hcross := (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hf
  apply (Real.log_le_iff_le_exp (by positivity : 0 < (2 * S ^ 100) ^ freshLength S V)).mp
  rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast
  have hs : (0 : ℝ) ≤ freshLength S V := Nat.cast_nonneg _
  have hlogscale := mul_le_mul_of_nonneg_left hlogtwo hs
  nlinarith

/-- The factorial multiplicity bound implies the required small atom bound. -/
theorem fresh_factorial_atom_le_exp {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    ((freshLength S V).factorial : ℝ) / (S ^ 99) ^ freshLength S V ≤
      Real.exp (-(7 / 10 : ℝ) * V) := by
  have hSone : 1 < S := by linarith
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hSone
  have hVpos : 0 < V := by nlinarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log S := by
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo
    exact htwo.trans (Real.log_le_log (by norm_num) hS)
  obtain ⟨hflower, hfupper⟩ := freshLength_bounds hSone hV
  have hlo := (div_le_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hflower
  have hhi := (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hfupper
  have hsnonneg : (0 : ℝ) ≤ freshLength S V := Nat.cast_nonneg _
  have hs : (freshLength S V : ℝ) ≤ S := by
    have := mul_le_mul_of_nonneg_left hloghalf hsnonneg
    nlinarith
  have hfact : ((freshLength S V).factorial : ℝ) ≤ S ^ freshLength S V := by
    calc
      ((freshLength S V).factorial : ℝ) ≤
          (freshLength S V : ℝ) ^ freshLength S V := by
        exact_mod_cast Nat.factorial_le_pow (freshLength S V)
      _ ≤ S ^ freshLength S V := pow_le_pow_left₀ hsnonneg hs _
  have hfactlog := Real.log_le_log (by positivity : (0 : ℝ) < (freshLength S V).factorial) hfact
  rw [Real.log_pow] at hfactlog
  apply (Real.log_le_iff_le_exp (by positivity :
    0 < ((freshLength S V).factorial : ℝ) / (S ^ 99) ^ freshLength S V)).mp
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

/-- The fresh tuple is nonempty throughout the construction's range. -/
theorem freshLength_pos {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) :
    1 ≤ freshLength S V := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hlo := (freshLength_bounds hS hV).1
  have hcross := (div_le_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hlo
  by_contra h
  have hz : freshLength S V = 0 := by omega
  rw [hz] at hcross
  norm_num at hcross
  nlinarith

/-- Atom estimate with the actual cardinality of the prime sampling set. -/
theorem fresh_factorial_atom_of_card {S V : ℝ} (P : ℕ) (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (hP : S ^ 99 ≤ (P : ℝ)) :
    ((freshLength S V).factorial : ℝ) / (P : ℝ) ^ freshLength S V ≤
      Real.exp (-(7 / 10 : ℝ) * V) := by
  calc
    ((freshLength S V).factorial : ℝ) / (P : ℝ) ^ freshLength S V ≤
        ((freshLength S V).factorial : ℝ) / (S ^ 99) ^ freshLength S V := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hP _
    _ ≤ Real.exp (-(7 / 10 : ℝ) * V) := fresh_factorial_atom_le_exp hS hV hVS

/-- Product estimate for individual prime samples, ready for an injective
reduction-modulo-modulus argument. -/
theorem fresh_samples_product_le_exp {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V)
    (p : Fin (freshLength S V) → ℕ)
    (hp : ∀ i, (p i : ℝ) ≤ 2 * S ^ 100) :
    ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp ((4 / 5 : ℝ) * V) := by
  calc
    ((∏ i, p i : ℕ) : ℝ) = ∏ i, (p i : ℝ) := by norm_cast
    _ ≤ ∏ _i : Fin (freshLength S V), (2 * S ^ 100) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun index _ => hp index)
    _ = (2 * S ^ 100) ^ freshLength S V := by simp
    _ ≤ Real.exp ((4 / 5 : ℝ) * V) := fresh_product_le_exp hS hV

/-- Hit threshold used when the exposed gcd makes the reduced modulus small. -/
def badGcdThreshold (S V : ℝ) : ℕ := ⌈(2 / 25 : ℝ) * V / (101 * Real.log S)⌉₊

theorem bad_gcd_implies_many_hits {S V G Q : ℝ} (B : ℕ)
    (hS : 1 < S) (hV : 0 ≤ V) (hG : 0 < G) (hQ : 0 < Q)
    (hproduct : G * Q = Real.exp V)
    (hsmall : Q < Real.exp ((9 / 10 : ℝ) * V))
    (hbound : G ≤ Real.exp (V / 200) * (S ^ 101) ^ B) :
    badGcdThreshold S V ≤ B := by
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hlogs : Real.log G + Real.log Q = V := by
    rw [← Real.log_mul hG.ne' hQ.ne', hproduct, Real.log_exp]
  have hQlog := Real.log_lt_log hQ hsmall
  rw [Real.log_exp] at hQlog
  have hGlog := Real.log_le_log hG hbound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_pow] at hGlog
  push_cast at hGlog
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by positivity : 0 < 101 * Real.log S)).mpr
  nlinarith

/-- The elementary union-bound expression is exponentially small with the
specific random-products parameters. -/
theorem hit_tail_parameter_bound {S V : ℝ} (hS : 1 < S) (hV : 0 ≤ V)
    (m H P k : ℕ) (hm : (m : ℝ) ≤ S) (hH : (H : ℝ) ≤ S)
    (hP : S ^ 99 ≤ (P : ℝ))
    (hk : badGcdThreshold S V ≤ k) :
    ((m : ℝ) * (H : ℝ) / (P : ℝ)) ^ k ≤ Real.exp (-(1 / 20 : ℝ) * V) := by
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hPpos : 0 < (P : ℝ) := lt_of_lt_of_le (by positivity) hP
  have hnum : (m : ℝ) * (H : ℝ) ≤ S ^ 2 := by
    nlinarith [mul_le_mul hm hH (Nat.cast_nonneg H) hSpos.le]
  have hbase : (m : ℝ) * (H : ℝ) / (P : ℝ) ≤ S ^ 2 / S ^ 99 := by
    calc
      (m : ℝ) * (H : ℝ) / (P : ℝ) ≤ S ^ 2 / (P : ℝ) :=
        div_le_div_of_nonneg_right hnum hPpos.le
      _ ≤ S ^ 2 / S ^ 99 := div_le_div_of_nonneg_left (by positivity) (by positivity) hP
  have hkreal : (2 / 25 : ℝ) * V / (101 * Real.log S) ≤ (k : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hcross := (div_le_iff₀ (by positivity : 0 < 101 * Real.log S)).mp hkreal
  calc
    ((m : ℝ) * (H : ℝ) / (P : ℝ)) ^ k ≤ (S ^ 2 / S ^ 99) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ ≤ Real.exp (-(1 / 20 : ℝ) * V) := by
      apply (Real.log_le_iff_le_exp (by positivity : 0 < (S ^ 2 / S ^ 99) ^ k)).mp
      rw [Real.log_pow, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      nlinarith

theorem blockLength_le_self {S : ℝ} (hS : Real.exp 1 ≤ S) :
    (blockLength S : ℝ) ≤ S := by
  have hSpos : 0 < S := lt_of_lt_of_le (Real.exp_pos _) hS
  have hlog : 1 ≤ Real.log S := by
    have := Real.log_le_log (Real.exp_pos 1) hS
    simpa using this
  calc
    (blockLength S : ℝ) ≤ S / Real.log S := Nat.floor_le (by positivity)
    _ ≤ S := div_le_self hSpos.le hlog

/-- Small fresh products remain distinct after reduction modulo any good
reduced modulus. -/
theorem fresh_samples_product_lt_modulus {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (q : ℕ)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ (q : ℝ))
    (p : Fin (freshLength S V) → ℕ)
    (hp : ∀ i, (p i : ℝ) ≤ 2 * S ^ 100) :
    (∏ i, p i) < q := by
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  have hVpos : 0 < V := by nlinarith
  have hreal : ((∏ i, p i : ℕ) : ℝ) < (q : ℝ) := by
    calc
      ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp ((4 / 5 : ℝ) * V) :=
        fresh_samples_product_le_exp hS hV p hp
      _ < Real.exp ((9 / 10 : ℝ) * V) := Real.exp_lt_exp.mpr (by nlinarith)
      _ ≤ (q : ℝ) := hq
  exact_mod_cast hreal

/-- Numerical endgame of the bilinear Fourier estimate. -/
theorem bilinear_atom_parameter_bound {S V : ℝ} (P q : ℕ) (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (hP : S ^ 99 ≤ (P : ℝ)) (hq : (q : ℝ) ≤ Real.exp V) :
    Real.sqrt (q : ℝ) * (((freshLength S V).factorial : ℝ) /
      (P : ℝ) ^ freshLength S V) ≤ Real.exp (-(1 / 5 : ℝ) * V) := by
  have hsqrt : Real.sqrt (q : ℝ) ≤ Real.exp (V / 2) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨(Real.exp_pos _).le, ?_⟩
    calc
      (q : ℝ) ≤ Real.exp V := hq
      _ = Real.exp (V / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    Real.sqrt (q : ℝ) * (((freshLength S V).factorial : ℝ) /
        (P : ℝ) ^ freshLength S V) ≤
        Real.exp (V / 2) * Real.exp (-(7 / 10 : ℝ) * V) :=
      mul_le_mul hsqrt (fresh_factorial_atom_of_card P hS hV hVS hP)
        (by positivity) (by positivity)
    _ = Real.exp (-(1 / 5 : ℝ) * V) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Combines Hamming exceptions, bad gcd exposures, and good-exposure
bilinear cancellation into the final second-moment scale. -/
theorem three_errors_le_final_scale {m V w : ℝ}
    (hwm : w ≤ m) (hwV : w ≤ V) (hw : 50 ≤ w) :
    Real.exp (-m / 16) + Real.exp (-V / 20) + Real.exp (-V / 5) ≤
      Real.exp (-w / 100) := by
  have h₁ : Real.exp (-m / 16) ≤ Real.exp (-w / 20) :=
    Real.exp_le_exp.mpr (by linarith)
  have h₂ : Real.exp (-V / 20) ≤ Real.exp (-w / 20) :=
    Real.exp_le_exp.mpr (by linarith)
  have h₃ : Real.exp (-V / 5) ≤ Real.exp (-w / 20) :=
    Real.exp_le_exp.mpr (by linarith)
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by
    convert Real.add_one_le_exp 2 using 1; norm_num
  calc
    Real.exp (-m / 16) + Real.exp (-V / 20) + Real.exp (-V / 5) ≤
        3 * Real.exp (-w / 20) := by linarith
    _ ≤ Real.exp 2 * Real.exp (-w / 20) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = Real.exp (2 - w / 20) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-w / 100) := Real.exp_le_exp.mpr (by linarith)

/-- A version independent of the constant in the prime sampling interval.
In particular it applies to `[S^100,4*S^100]` once `S≥4`. -/
theorem fresh_samples_powerBound_le_exp {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V)
    (p : Fin (freshLength S V) → ℕ)
    (hp : ∀ i, (p i : ℝ) ≤ S ^ 101) :
    ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp ((4 / 5 : ℝ) * V) := by
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hVpos : 0 < V := by nlinarith
  have hf := (freshLength_bounds hS hV).2
  have hcross := (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mp hf
  calc
    ((∏ i, p i : ℕ) : ℝ) = ∏ i, (p i : ℝ) := by norm_cast
    _ ≤ ∏ _i : Fin (freshLength S V), S ^ 101 :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun index _ => hp index)
    _ = (S ^ 101) ^ freshLength S V := by simp
    _ ≤ Real.exp ((4 / 5 : ℝ) * V) := by
      apply (Real.log_le_iff_le_exp (by positivity : 0 < (S ^ 101) ^ freshLength S V)).mp
      rw [Real.log_pow, Real.log_pow]
      push_cast
      nlinarith

theorem fresh_samples_powerBound_lt_modulus {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (q : ℕ)
    (hq : Real.exp ((9 / 10 : ℝ) * V) ≤ (q : ℝ))
    (p : Fin (freshLength S V) → ℕ)
    (hp : ∀ i, (p i : ℝ) ≤ S ^ 101) :
    (∏ i, p i) < q := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hVpos : 0 < V := by nlinarith
  have hreal : ((∏ i, p i : ℕ) : ℝ) < (q : ℝ) := by
    calc
      ((∏ i, p i : ℕ) : ℝ) ≤ Real.exp ((4 / 5 : ℝ) * V) :=
        fresh_samples_powerBound_le_exp hS hV p hp
      _ < Real.exp ((9 / 10 : ℝ) * V) := Real.exp_lt_exp.mpr (by nlinarith)
      _ ≤ (q : ℝ) := hq
  exact_mod_cast hreal

/-- The Hamming-distance condition supplies two disjoint fresh blocks. -/
theorem fresh_coordinates_fit {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S)
    (B : ℕ) (hB : blockLength S ≤ 4 * B) :
    2 * freshLength S V ≤ B := by
  have := freshLength_eight_le_blockLength hS hV hVS
  omega

theorem blockLength_large {S V : ℝ} (hS : 1 < S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    100000 ≤ blockLength S := by
  apply Nat.le_floor
  apply (le_div_iff₀ (Real.log_pos hS)).mpr
  norm_num
  linarith

/-- The range assumptions automatically make the final scale large enough
for absorption of all three error terms. -/
theorem random_errors_le_final_scale {S V : ℝ} (hS : 2 ≤ S)
    (hV : 100000 * Real.log S ≤ V) (hVS : V ≤ S) :
    Real.exp (-(blockLength S : ℝ) / 16) + Real.exp (-V / 20) +
      Real.exp (-V / 5) ≤ Real.exp (-min (blockLength S : ℝ) V / 100) := by
  apply three_errors_le_final_scale (min_le_left _ _) (min_le_right _ _)
  apply le_min
  · have := blockLength_large (by linarith : 1 < S) hV hVS
    have : (100000 : ℝ) ≤ blockLength S := by exact_mod_cast this
    linarith
  · have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo
    have hlog := htwo.trans (Real.log_le_log (by norm_num) hS)
    nlinarith

end Problem337.RandomProducts

end

end OAI
