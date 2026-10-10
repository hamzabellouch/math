import OAI.NumberTheory.TotientAsymptotic.UnbandedPrimeGrid
import OAI.NumberTheory.TotientAsymptotic.PrimeBoxInput

namespace OAI

/-! Positive prime mass in grids with a large reverse linear lower envelope. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

lemma sum_exp_neg_linear_prefix_sharp {N : ℕ} {c : ℝ} (hc : 0 < c)
    (b : Fin N → ℕ) (hb : ∀ i,c*(N-i.val:ℕ) ≤ (b i:ℝ)) :
    (∑ i,Real.exp (-(b i:ℝ))) ≤ Real.exp (-c)/(1-Real.exp (-c)) := by
  let q := Real.exp (-c)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs := summable_geometric_of_lt_one hq0 hq1
  calc
    _ ≤ ∑ i : Fin N,q^(N-i.val) := by
      apply Finset.sum_le_sum
      intro i _
      dsimp [q]
      rw [←Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by nlinarith only [hb i])
    _ = ∑ j ∈ Finset.range N,q^(j+1) := by
      apply Finset.sum_bij (fun i _ => N-i.val-1)
      · intro i _
        exact Finset.mem_range.mpr (by omega)
      · intro i _ j _ hij
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        omega
      · intro j hj
        have hj := Finset.mem_range.mp hj
        exact ⟨⟨N-j-1,by omega⟩,Finset.mem_univ _,by simp only; omega⟩
      · intro i _
        congr 1
        have := i.isLt
        omega
    _ = q*(∑ j ∈ Finset.range N,q^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ,mul_comm]
    _ ≤ q*(∑' j : ℕ,q^j) :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)) hq0
    _ = _ := by rw [tsum_geometric_of_lt_one hq0 hq1]; rfl

theorem grid_prime_mass_lower : ∃ c₀ : ℝ,0 < c₀ ∧
    ∀ {N : ℕ} (K : Finset (Fin N → ℕ)),
      (∀ b ∈ K,∀ i,1 ≤ b i ∧ c₀*(N-i.val:ℕ) ≤ (b i:ℝ)) →
      (K.card:ℝ)/2 ≤ gridPrimeMass K := by
  obtain ⟨C,hC,hgrid⟩ := grid_prime_mass_error_of_sum fordUnitPrimeBoxInput
  let c₀ := Real.log (1+4*C)
  have hc : 0 < c₀ := Real.log_pos (by linarith)
  have hq : Real.exp (-c₀)=1/(1+4*C) := by
    rw [Real.exp_neg,Real.exp_log (by linarith : 0 < 1+4*C)]
    exact (one_div _).symm
  have hbudget : C*(Real.exp (-c₀)/(1-Real.exp (-c₀)))=1/4 := by
    rw [hq]
    field_simp [hC.ne']
    ring
  have hexp : Real.exp (C*(Real.exp (-c₀)/(1-Real.exp (-c₀))))-1 ≤ 1/2 := by
    rw [hbudget]
    have he := Real.exp_bound_div_one_sub_of_interval (x:=1/4) (by norm_num) (by norm_num)
    norm_num at he
    linarith only [he]
  refine ⟨c₀,hc,?_⟩
  intro N K hK
  have he := hgrid K (Real.exp (-c₀)/(1-Real.exp (-c₀)))
    (fun b hb i => (hK b hb i).1)
    (fun b hb => sum_exp_neg_linear_prefix_sharp hc b (fun i => (hK b hb i).2))
  have hlo := (abs_le.mp he).1
  have hh := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg K.card)
  linarith only [hlo,hh]

end TotientAsymptotic

end

end OAI
