import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.BigOperators
import OAI.Analysis.Laughlin.Pair.Conjugation

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter

theorem modeFactor_sq_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range x, (1/1 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) 0 1 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range x,
      ((-(i : ℝ)+1*(Q : ℝ))/(0+1*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => (Q.descFactorial x : ℝ)/(Q : ℝ)^x) := by
    filter_upwards [eventually_ge_atTop x] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : (Q : ℝ)^x = ∏ _i ∈ Finset.range x, (Q : ℝ) := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ Q)]
      congr 1 <;> ring
  simpa using hp.congr' he

theorem pairFactor_inv_sq_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => ((2*Q-2).descFactorial p : ℝ)/((2 : ℝ)*Q)^p)
      atTop (𝓝 1) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range p,
      ((-(2+(i : ℝ))+2*(Q : ℝ))/(0+2*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range p, (2/2 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(2+(i : ℝ))) 0 2 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range p,
      ((-(2+(i : ℝ))+2*(Q : ℝ))/(0+2*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => ((2*Q-2).descFactorial p : ℝ)/((2 : ℝ)*Q)^p) := by
    filter_upwards [eventually_ge_atTop (p+2)] with Q hQ
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : ((2 : ℝ)*Q)^p = ∏ _i ∈ Finset.range p, (2 : ℝ)*Q := by simp
    rw [hd, ← Finset.prod_div_distrib]
    · apply Finset.prod_congr rfl
      intro i hi
      have hi := Finset.mem_range.mp hi
      rw [Nat.cast_sub (by omega : i ≤ 2*Q-2), Nat.cast_sub (by omega : 2 ≤ 2*Q)]
      push_cast
      congr 1 <;> ring
  simpa using hp.congr' he

theorem modeFactor_tendsto (x : ℕ) :
    Tendsto (fun Q : ℕ => modeFactor Q x) atTop (𝓝 1) := by
  simpa [modeFactor] using (modeFactor_sq_tendsto x).sqrt

theorem pairFactor_tendsto (p : ℕ) :
    Tendsto (fun Q : ℕ => pairFactor Q p) atTop (𝓝 1) := by
  have h := ((pairFactor_inv_sq_tendsto p).inv₀ (by norm_num)).sqrt
  simpa [pairFactor, inv_div] using h

end Laughlin

end OAI
