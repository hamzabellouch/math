import OAI.NumberTheory.TotientAsymptotic.DyadicCoordinateRow
import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicPowerMass

namespace OAI

/-! Finite reciprocal mass of totients with a relative coordinate-row failure. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem exceptional_row_reciprocal_mass : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ k : ℕ,∀ ω U : ℝ,0 < ω → ω ≤ 1 → 512 ≤ U → 2*Real.exp (Real.exp 1) ≤ U →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/2) k)^(4/3:ℝ)) ≤ B U-1 →
    4 ≤ ω*B U → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,U ≤ (v:ℝ) ∧ IsTotient v ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B v < ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1)) →
    (∑ v ∈ Q,(v:ℝ)⁻¹) ≤
      4*C*(Real.log 2)^(-1-coordinateDecay (ω/2) k)*(1+(coordinateDecay (ω/2) k)⁻¹)*
        Real.exp (-coordinateDecay (ω/2) k*B U) := by
  classical
  obtain ⟨C,F,hC,hF,hcount⟩ := real_coordinate_deviation
  refine ⟨C,F,hC,hF,?_⟩
  intro k ω U hω hω1 hU hUexp hthreshold hlarge Q hQ
  let δ := coordinateDecay (ω/2) k
  have hδ : 0 < δ := coordinate_decay_pos (by linarith) k
  have hU1 : 1 < U := by linarith
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hA : 0 ≤ C*(Real.log 2)^(-1-δ) := by positivity
  have hslices (j : ℕ) (hj : 1 ≤ j) :
      ((Q.filter (fun v => Nat.clog 2 v=j)).card:ℝ) ≤
        (C*(Real.log 2)^(-1-δ))*(2:ℝ)^j*(j:ℝ)^(-1-δ) := by
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
      have hx1 : (1:ℝ) < (2:ℝ)^j := hU1.trans_le hUx
      have hBU : B U ≤ B ((2:ℝ)^j) :=
        Real.log_le_log (Real.log_pos hU1)
          (Real.log_le_log (by linarith) hUx)
      have hsize : 4 ≤ ω*B ((2:ℝ)^j) :=
        hlarge.trans (mul_le_mul_of_nonneg_left hBU hω.le)
      have hc := hcount ((2:ℝ)^j) (hU.trans hUx) (hUexp.trans hUx) k (ω/2)
        (by linarith) (by linarith) (by linarith only [hthreshold,hBU]) R (by
          intro q hq
          obtain ⟨hqQ,hqj⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqU,hqt,n,hn,hφ,hrow⟩ := hQ q hqQ
          have hq2 : 2 ≤ q := by exact_mod_cast (show (2:ℝ) ≤ q by linarith only [hqU,hU])
          have hqd := dyadic_nat_bounds (show 1 < q by omega)
          rw [hqj] at hqd
          refine ⟨hqt,hqd.2.2,n,hn,hφ,?_⟩
          have hh := relative_row_at_dyadic hq2 hω.le hω1 (by simpa only [hqj] using hsize) hrow
          simpa only [hqj] using hh)
      calc
        _ ≤ C*(2:ℝ)^j/Real.log ((2:ℝ)^j)*Real.exp (-δ*B ((2:ℝ)^j)) := hc
        _ = C*(2:ℝ)^j*dyadicSuffixWeight δ j := by
          rw [dyadic_endpoint_log,dyadic_endpoint_B,dyadicSuffixWeight]
          ring
        _ = _ := by rw [dyadicSuffixWeight_eq hj]; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hR,Finset.card_empty,Nat.cast_zero]
      positivity
  have hm := finite_dyadic_log_power_tail Q hU1 hA hδ (fun v hv => (hQ v hv).1) hslices
  have he : (Real.log U)^(-δ)=Real.exp (-δ*B U) := by
    rw [Real.rpow_def_of_pos (Real.log_pos hU1)]
    unfold B
    congr 1
    ring
  rw [he] at hm
  convert hm using 1
  ring

end TotientAsymptotic

end

end OAI
