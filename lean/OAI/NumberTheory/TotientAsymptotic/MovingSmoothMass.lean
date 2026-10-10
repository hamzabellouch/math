import OAI.NumberTheory.TotientAsymptotic.MovingSmoothDyadic
import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicLogTail

namespace OAI

/-! Reciprocal tail mass of values with very smooth preimages. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem moving_smooth_reciprocal_mass : ∃ C : ℝ,0 < C ∧ ∀ U : ℝ,
    512 ≤ U → Real.exp (Real.exp 1) ≤ U → 10000 ≤ B U → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,U ≤ (v:ℝ) ∧ ∃ n : ℕ,0 < n ∧ n.totient=v ∧
      (largestPrimeFactor n:ℝ) ≤ Real.exp (Real.log v/(1000*B v))) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤ C/(Real.log U)^2 := by
  classical
  obtain ⟨C,hC,hcount⟩ := moving_smooth_totient_count
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨8*C/Real.log 2,by positivity,?_⟩
  intro U hU hUexp hBU Q hQ
  have hU1 : 1 < U := by linarith only [hU]
  have hA : 0 ≤ C/(Real.log 2)^3 := by positivity
  have hslices (j : ℕ) (hj : 1 ≤ j) :
      ((Q.filter (fun v => Nat.clog 2 v=j)).card:ℝ) ≤
        (C/(Real.log 2)^3)*(2:ℝ)^j/(j:ℝ)^3 := by
    let R := Q.filter (fun v => Nat.clog 2 v=j)
    change (R.card:ℝ) ≤ _
    by_cases hR : R.Nonempty
    · obtain ⟨v,hv⟩ := hR
      obtain ⟨hvQ,hvj⟩ := Finset.mem_filter.mp hv
      have hvU := (hQ v hvQ).1
      have hv2 : 2 ≤ v := by exact_mod_cast (show (2:ℝ) ≤ v by linarith only [hvU,hU])
      have hd := dyadic_nat_bounds (show 1 < v by omega)
      rw [hvj] at hd
      have hUx : U ≤ (2:ℝ)^j := hvU.trans hd.2.2
      have hcountR := hcount ((2:ℝ)^j) (hUexp.trans hUx)
        (hBU.trans (B_mono hU1 hUx)) R (by
          intro q hq
          obtain ⟨hqQ,hqj⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqU,n,hn,hφ,hsmooth⟩ := hQ q hqQ
          have hq2 : 2 ≤ q := by exact_mod_cast (show (2:ℝ) ≤ q by linarith only [hqU,hU])
          have hBq : 1 ≤ B (q:ℝ) := (show (1:ℝ) ≤ B U by linarith only [hBU]).trans (B_mono hU1 hqU)
          have hqd := dyadic_nat_bounds (show 1 < q by omega)
          rw [hqj] at hqd
          refine ⟨n,hn,hφ,hqd.2.2,?_⟩
          simpa only [hqj] using relative_smooth_at_dyadic hq2 hBq hsmooth)
      apply hcountR.trans_eq
      rw [dyadic_endpoint_log,mul_pow]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR,Finset.card_empty,Nat.cast_zero]
      positivity
  have hm := finite_dyadic_log_cube_tail Q hU1 hA (fun v hv => (hQ v hv).1) hslices
  apply hm.trans_eq
  have hlogU : 0 < Real.log U := Real.log_pos hU1
  field_simp

end TotientAsymptotic

end

end OAI
