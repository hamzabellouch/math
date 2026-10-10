import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRuntimeBound

namespace OAI

/-! # The correction probability absorbs the cost of finite tabulation -/

namespace ContingencyTables.RareBranchRuntime
open Polynomial ProfilePrograms

/-- The coefficient in a fixed exponential running-time bound need not be
smaller than the coefficient used in the sampler's precision schedule. -/
lemma linear_le_square_add (k s : ℕ) : k * s ≤ s ^ 2 + k ^ 2 := by
  have h := two_mul_le_add_sq (k : ℤ) (s : ℤ)
  have : (k : ℤ)*s≤(s : ℤ)^2+(k : ℤ)^2 := by nlinarith
  exact_mod_cast this

lemma dyadic_linear_bound (k s D : ℕ) (hD : s^2≤D) :
    (2:ℕ)^(k*s)≤2^D*2^(k^2) := by
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide) ((linear_le_square_add k s).trans
    (Nat.add_le_add_right hD _))

/-- A polynomial in an exponential tabulation size remains affordable
after multiplying by the rare-branch probability `2⁻ᴰ`. -/
theorem polynomial_tabulation_bound (p : Polynomial ℕ) (A s a D : ℕ)
    (hD : s^2≤D) :
    p.eval (A*2^(a*s))≤2^D*(p.eval A*2^((a*p.natDegree)^2)) := by
  calc
    p.eval (A*2^(a*s))≤p.eval A*2^((a*s)*p.natDegree) :=
      polynomial_scaled_power p A 2 (a*s) (by decide)
    _ = p.eval A*2^((a*p.natDegree)*s) := by
      rw [Nat.mul_right_comm a s p.natDegree]
    _ ≤ p.eval A*(2^D*2^((a*p.natDegree)^2)) :=
      Nat.mul_le_mul_left _ (dyadic_linear_bound (a*p.natDegree) s D hD)
    _ = 2^D*(p.eval A*2^((a*p.natDegree)^2)) := by ring

lemma square_le_precision (d b : ℕ) (hd : 1≤d) :
    (d*b)^2≤d^6*b^2 := by
  rw [mul_pow]
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hd (by decide : 2≤6))

/-- The manuscript's precision `d⁶ b²` absorbs any fixed polynomial of
the grid size `2^(10*d*b)`, up to a constant and a polynomial factor. -/
theorem correction_tabulation_bound (p : Polynomial ℕ) (A d b : ℕ)
    (hd : 1≤d) :
    p.eval (A*2^(10*(d*b)))≤
      2^(d^6*b^2)*(p.eval A*2^((10*p.natDegree)^2)) :=
  polynomial_tabulation_bound p A (d*b) 10 (d^6*b^2) (square_le_precision d b hd)

theorem expected_correction_cost (p : Polynomial ℕ) (A d b : ℕ)
    (hd : 1≤d) (T : ℕ) (hT : T≤p.eval (A*2^(10*(d*b)))) :
    (T : ℝ)/(2:ℝ)^(d^6*b^2)≤p.eval A*2^((10*p.natDegree)^2) := by
  have h := hT.trans (correction_tabulation_bound p A d b hd)
  have hr : (T : ℝ)≤(2:ℝ)^(d^6*b^2)*
      ((p.eval A*2^((10*p.natDegree)^2) : ℕ) : ℝ) := by exact_mod_cast h
  exact (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hr)

/-- A finite ordinary prefix followed by a rare correction adds only the
probability-weighted correction tail to the expected physical runtime. -/
theorem expected_branch_time (tail correction : ℕ → ℝ) (S : ℕ) (delta : ℝ)
    (h0 : ∀ n,0≤tail n) (h1 : ∀ n,tail n≤1)
    (hc : Summable correction)
    (hafter : ∀ n,tail (n+S)≤delta*correction n) :
    Summable tail ∧ (∑' n,tail n)≤(S:ℝ)+delta*(∑' n,correction n) := by
  have hm := hc.mul_left delta
  have hs : Summable (fun n => tail (n+S)) :=
    Summable.of_nonneg_of_le (fun n => h0 (n+S)) hafter hm
  have ht : Summable tail := (summable_nat_add_iff S).mp hs
  refine ⟨ht,?_⟩
  rw [←ht.sum_add_tsum_nat_add S]
  have hprefix : (∑ n ∈ Finset.range S,tail n)≤(S:ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range S,(1:ℝ) := Finset.sum_le_sum (fun n _ => h1 n)
      _ = (S:ℝ) := by simp
  have hrest : (∑' n,tail (n+S))≤delta*(∑' n,correction n) := by
    simpa only [tsum_mul_left] using hs.tsum_le_tsum hafter hm
  exact add_le_add hprefix hrest

end ContingencyTables.RareBranchRuntime

end OAI
