import Mathlib
import OAI.Analysis.LaughlinFock.FiniteComparison

namespace OAI

/-! Square Splitting. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 

def tailThreeTarget (Q : ℕ) : FockMatrix Q :=
  exteriorLift Q 3 (threeWedgeMatrix Q *
    (∑ z ∈ Finset.Ico 16 (Q+1), (gramShift Q z : ℂ) • threeSpinProjection Q z) *
      (threeWedgeMatrix Q)ᴴ)

 
theorem fullThreeTarget_split {Q : ℕ} (hQ : 16 ≤ Q+1) :
    fullThreeTarget Q = finiteThreeTarget Q + tailThreeTarget Q := by
  unfold fullThreeTarget finiteThreeTarget tailThreeTarget
  rw [← Finset.sum_range_add_sum_Ico _ hQ, Matrix.mul_add, Matrix.add_mul, exteriorLift_add]

 

theorem normal_ordered_square_split {Q : ℕ} (hQ : 16 ≤ Q) :
    hamiltonian Q * hamiltonian Q = hamiltonian Q +
      finiteThreeTarget Q + tailThreeTarget Q +
        exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) := by
  have h := normal_ordered_square_spectral Q (by omega)
  change _ = hamiltonian Q + fullThreeTarget Q + _ at h
  rw [fullThreeTarget_split (by omega), ← add_assoc] at h
  exact h

 

theorem threeSpinProjection_lift_posSemidef (Q z : ℕ) :
    (exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z *
      (threeWedgeMatrix Q)ᴴ)).PosSemidef :=
  exteriorLift_posSemidef Q 3 _
    ((threeSpinProjection_posSemidef Q z).mul_mul_conjTranspose_same _)

 

theorem threeSpinProjection_lift (Q z : ℕ) :
    exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z *
      (threeWedgeMatrix Q)ᴴ) =
      ∑ c : CoupledIndex (2*Q-2) Q, if c.1.val=z then
        (wedgeAnnihilator Q 3 (threeWedgeMatrix Q *ᵥ
          threeCoupledColumn Q c.1.val c.2.val))ᴴ *
          wedgeAnnihilator Q 3 (threeWedgeMatrix Q *ᵥ
            threeCoupledColumn Q c.1.val c.2.val) else 0 := by
  classical
  unfold threeSpinProjection
  have he : threeWedgeMatrix Q *
      (threeCouplingMatrix Q * Matrix.diagonal
        (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) *
        (threeCouplingMatrix Q)ᴴ) * (threeWedgeMatrix Q)ᴴ =
      (threeWedgeMatrix Q * threeCouplingMatrix Q) * Matrix.diagonal
        (fun c : CoupledIndex (2*Q-2) Q => if c.1.val=z then (1:ℂ) else 0) *
        (threeWedgeMatrix Q * threeCouplingMatrix Q)ᴴ := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [he, exteriorLift_congruence]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Matrix.diagonal_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ c)]
  split_ifs <;> simp only [one_smul]
  rfl

 

theorem FockInequality.mono {Q : ℕ} {a b : ℝ} (h : FockInequality Q b)
    (hab : a ≤ b) : FockInequality Q a := by
  have h' := h.add ((hamiltonian_posSemidef Q).smul (sub_nonneg.mpr hab))
  unfold FockInequality at *
  convert h' using 1
  simp only [sub_smul]
  abel

 

theorem fockInequality_of_finite_comparisons {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) {Q : ℕ} (hQ : 16 ≤ Q)
    (A4 : FockMatrix Q) (δ e : ℝ)
    (hK : (rowsEta rows • hamiltonian Q + threeTraceForm rows Q + A4).PosSemidef)
    (h3 : (finiteThreeTarget Q - threeTraceForm rows Q).PosSemidef)
    (h4 : (exteriorLift Q 4 (fourWedgeMatrix Q * (fourWedgeMatrix Q)ᴴ) +
      e • hamiltonian Q - A4).PosSemidef)
    (htail : (tailThreeTarget Q + δ • hamiltonian Q).PosSemidef) :
    FockInequality Q (1-rowsEta rows-δ-e) := by
  have h := ((hK.add h3).add h4).add htail
  unfold FockInequality
  rw [normal_ordered_square_split hQ]
  convert h using 1
  simp only [sub_smul, one_smul]
  abel

 

theorem uniform_integer_threshold_of_eventual_bound (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 gammaStar))
    (hbound : ∀ᶠ Q in atTop, FockInequality Q (a Q))
    (γ : ℝ) (hγ : γ < gammaStar) :
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ := by
  have he : ∀ᶠ Q in atTop, γ < a Q := ha.eventually (eventually_gt_nhds hγ)
  obtain ⟨q, hq⟩ := eventually_atTop.mp (hbound.and he)
  refine ⟨(max 1 q : ℕ), ?_, ?_⟩
  · exact_mod_cast (le_max_left 1 q)
  · intro Q hQ
    have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
    have hqn : max 1 q ≤ Q.toNat := by exact_mod_cast (show (max 1 q : ℤ) ≤ (Q.toNat : ℤ) by simpa [Int.toNat_of_nonneg hQ0] using hQ)
    exact (hq Q.toNat (le_trans (le_max_right 1 q) hqn)).1.mono
      (hq Q.toNat (le_trans (le_max_right 1 q) hqn)).2.le

 

theorem final_coefficient_tendsto {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow)
    (hEta : rowsEta rows = 93527408868499 / 10^14)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun Q => 1-rowsEta rows-tailCoefficient Q-1222*(3/10^6)-e Q)
      atTop (𝓝 gammaStar) := by
  have h := (((tendsto_const_nhds (x := 1-rowsEta rows)).sub
    tailCoefficient_tendsto).sub_const (1222*(3/10^6))).sub he
  simpa only [hEta, sub_zero, final_margin_arithmetic] using h

end LaughlinFock
end

end OAI
