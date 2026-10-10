import OAI.NumberTheory.EgyptianFractions.VaughanDyadicEstimate
import OAI.NumberTheory.EgyptianFractions.TypeIIBlockScalar
import OAI.NumberTheory.EgyptianFractions.HyperbolaDyadicBridge

namespace OAI
noncomputable section
open scoped BigOperators ArithmeticFunction
open Finset

namespace Problem337.Vaughan

def typeIILogScale (N : ℕ) : ℝ := 1 + Real.log (2 * (N : ℝ))

lemma one_le_typeIILogScale (N : ℕ) : 1 ≤ typeIILogScale N := by
  have h := Real.log_natCast_nonneg (2 * N)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  unfold typeIILogScale
  linarith

lemma log_nat_le_typeIILogScale (N T : ℕ) (hT : T ≤ N) :
    Real.log T ≤ typeIILogScale N := by
  by_cases h0 : T = 0
  · simp only [h0, Nat.cast_zero, Real.log_zero]
    exact zero_le_one.trans (one_le_typeIILogScale N)
  have ht : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero h0
  have htn : (T : ℝ) ≤ 2 * (N : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hT
    nlinarith [Nat.cast_nonneg N (α := ℝ)]
  have hlog := Real.log_le_log ht htn
  unfold typeIILogScale
  linarith

/-- Uniform logarithmic normalization of the coefficient block estimate. -/
theorem typeIIBlock_sq_le_normalized
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) (hqN : q ≤ N) (hM : 2 ^ j ≤ N) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      (2 * ((2 ^ j : ℕ) : ℝ) * (typeIILogScale N) ^ 3) *
        ((2 * ((N / 2 ^ j : ℕ) : ℝ) / q + 1) *
          (2 * ((2 ^ j : ℕ) : ℝ) + 4 * (q : ℝ) * typeIILogScale N)) *
            (((N / 2 ^ j : ℕ) : ℝ) * (typeIILogScale N) ^ 2) := by
  have hH0 : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hMR : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hqlog : 1 + Real.log (2 * (q : ℝ)) ≤ typeIILogScale N := by
    unfold typeIILogScale
    apply add_le_add le_rfl
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hqN)
  have hMlog : 1 + Real.log (2 ^ (j + 1) : ℕ) ≤ typeIILogScale N := by
    unfold typeIILogScale
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    have hMRN : ((2 ^ j : ℕ) : ℝ) ≤ N := by exact_mod_cast hM
    nlinarith
  have hTlog := log_nat_le_typeIILogScale N (N / 2 ^ j) (Nat.div_le_self _ _)
  have hraw := typeIIBlock_sq_le_raw θ a q hq hcop happrox N U V j
  refine hraw.trans ?_
  have hqlog0 : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have h := Real.log_natCast_nonneg (2 * q)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    linarith
  have hMlog0 : 0 ≤ 1 + Real.log (2 ^ (j + 1) : ℕ) := by
    linarith [Real.log_natCast_nonneg (2 ^ (j + 1))]
  have hTlog0 := Real.log_natCast_nonneg (N / 2 ^ j)
  have he : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * ((2 ^ j : ℕ) : ℝ) := by
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he] at hMlog hMlog0 ⊢
  gcongr

/-- Uniform actual Type II block bound, with no cancellation or energy premise. -/
theorem typeIIBlock_sq_le_uniform
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (N U V j : ℕ) (hqN : q ≤ N) (hU : 0 < U) (hV : 0 < V) :
    ‖typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k))‖ ^ 2 ≤
      32 * (N : ℝ) * (typeIILogScale N) ^ 6 *
        ((N : ℝ) / q + (N : ℝ) / U + (N : ℝ) / V + q) := by
  have hH : 0 ≤ typeIILogScale N := zero_le_one.trans (one_le_typeIILogScale N)
  by_cases hb : typeIIBlock N U V j (fun k => VaughanBilinear.phase (θ * k)) = 0
  · rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hs : (VaughanDyadic.shell U N j).Nonempty := by
    by_contra he
    have he' : VaughanDyadic.shell U N j = ∅ := not_nonempty_iff_eq_empty.mp he
    apply hb
    simp [typeIIBlock, VaughanDyadic.block, he']
  obtain ⟨m, hm⟩ := hs
  have hm' := VaughanDyadic.mem_shell.mp hm
  have hM : 2 ^ j ≤ N := hm'.2.2.1.trans hm'.2.1
  have hbase := VaughanDyadic.base_le_div_of_block_ne_zero N U V j
    (fun m n => (typeIICoefficient U m : ℂ) * (Λ n : ℂ) *
      VaughanBilinear.phase (θ * (m * n : ℕ))) hb
  have hMT : (((2 ^ j : ℕ) : ℝ) * ((N / 2 ^ j : ℕ) : ℝ)) ≤ N := by
    exact_mod_cast Nat.mul_div_le N (2 ^ j)
  have hU2M : (U : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
    have hnat : U ≤ 2 * 2 ^ j := by
      have hu := hm'.1
      have hmhi := hm'.2.2.2
      rw [pow_succ] at hmhi
      omega
    exact_mod_cast hnat
  have hTU : ((N / 2 ^ j : ℕ) : ℝ) ≤ 2 * (N : ℝ) / U := by
    apply (le_div_iff₀ (by exact_mod_cast hU : (0 : ℝ) < U)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hU2M
      (Nat.cast_nonneg (N / 2 ^ j) : (0 : ℝ) ≤ (N / 2 ^ j : ℕ))]
  have hMV : ((2 ^ j : ℕ) : ℝ) ≤ (N : ℝ) / V := by
    apply (le_div_iff₀ (by exact_mod_cast hV : (0 : ℝ) < V)).mpr
    have hn : 2 ^ j * V ≤ N :=
      (Nat.mul_le_mul_left (2 ^ j) (Nat.le_succ V)).trans
        ((Nat.le_div_iff_mul_le (Nat.succ_pos V)).mp hbase)
    exact_mod_cast hn
  exact (typeIIBlock_sq_le_normalized θ a q hq hcop happrox N U V j hqN hM).trans
    (TypeIIBlockScalar.block_bound N (2 ^ j : ℕ) (N / 2 ^ j : ℕ) q U V (typeIILogScale N)
      (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg _)
      (by exact_mod_cast hq) (by exact_mod_cast hU) (by exact_mod_cast hV)
      (one_le_typeIILogScale N) hMT hTU hMV)

end Problem337.Vaughan

end

end OAI
