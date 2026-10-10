import OAI.NumberTheory.TotientAsymptotic.FailedRowValueCount
import OAI.NumberTheory.TotientAsymptotic.FailedRowCofactor
import OAI.NumberTheory.TotientAsymptotic.FailedRowTotalMass

namespace OAI

/-! First-failed-row value counts with the residual mass fully bounded. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def FailedRowMassBudget (F ω U : ℝ) (k : ℕ) : Prop :=
  0 < ω ∧ ω ≤ 1 ∧ 512 ≤ U ∧ 2*Real.exp (Real.exp 1) ≤ U ∧
  10000 ≤ B U ∧ (8000/ω)^2 ≤ B U ∧
  max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/4) k)^(4/3:ℝ)) ≤ B U-1 ∧
  4 ≤ (ω/2)*B U ∧ (coordinateDecay (ω/4) k)⁻¹ ≤ Real.exp (coordinateDecay (ω/4) k*B U)

theorem failed_row_count_bound : ∃ C F : ℝ, 0 < C ∧ 0 < F ∧
    ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ m x →
    ∀ ω U : ℝ, xi x j=1+ω → FailedRowMassBudget F ω U (m x-j) →
    ∀ Q : Finset ℕ, ∀ n : ℕ → ℕ,
      (∀ v ∈ Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        (∀ i < j, fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
          xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i)) ∧
        xi x j*fordPrimeCoordinate (n v) j <
          fordRowSum (m x) (fordPrimeCoordinate (n v)) j) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (j-1)*
        Real.exp (10*(Real.log (B U+4))^2) := by
  classical
  obtain ⟨A,hA,hcount⟩ := failed_row_value_count
  obtain ⟨D,F,hD,hF,hmass⟩ := failed_row_total_mass
  refine ⟨A*D,F,mul_pos hA hD,hF,?_⟩
  filter_upwards [hcount,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro j hj hjm ω U hxi hbudget Q n hQ
  obtain ⟨hω,hω1,hU,hUexp,hBU,hhead,hthreshold,hlarge,hinv⟩ := hbudget
  let R := Q.image (fun v => (fordCofactor (n v) j).totient)
  have hR := hmass (m x-j) ω U hω hω1 hU hUexp hBU hhead hthreshold hlarge hinv R (by
    intro d hd
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hd
    refine ⟨fordCofactor (n v) j,fordCofactor_pos _ _,rfl,?_⟩
    exact failed_row_cofactor hjm hxi (hQ v hv).2.2.2.2.2)
  have hc := hx j hj hjm Q n hQ
  have hfac : 0 ≤ A*(x/Real.log x)*G x (j-1) :=
    mul_nonneg (mul_nonneg hA.le (div_nonneg (by linarith) (Real.log_pos hx1).le)) (G_pos hB _).le
  apply hc.trans
  have hh := mul_le_mul_of_nonneg_left hR hfac
  convert hh using 1
  ring

end TotientAsymptotic

end

end OAI
