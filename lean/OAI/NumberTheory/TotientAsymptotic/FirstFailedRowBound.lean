import OAI.NumberTheory.TotientAsymptotic.FailedRowCutoff
import OAI.NumberTheory.TotientAsymptotic.ProjectedGaussian
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor
import OAI.NumberTheory.TotientAsymptotic.CollisionScale
import OAI.NumberTheory.TotientAsymptotic.RenewalInput

namespace OAI

/-! The complete Gaussian count for any fixed first failed row after the head. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem first_failed_row_bound : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ m x →
    ∀ Q : Finset ℕ, ∀ n : ℕ → ℕ,
      (∀ v ∈ Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        (∀ i < j, fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
          xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i)) ∧
        xi x j*fordPrimeCoordinate (n v) j <
          fordRowSum (m x) (fordPrimeCoordinate (n v)) j) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*
        Real.exp (-((m x-j:ℕ):ℝ)^2/4) := by
  obtain ⟨A,F,hA,hF,hcount⟩ := failed_row_count_bound
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  let C := A*Real.exp (210*(rowModelConstant F)^2+105*(Real.log J)^2+Real.log J)
  refine ⟨C,mul_pos hA (Real.exp_pos _),?_⟩
  filter_upwards [hcount,hproj,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hp hx1 hB
  intro j hj hjm Q n hQ
  let k := m x-j
  let ω : ℝ := Real.exp (-(k:ℝ)/40)/10000
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hω1 : ω ≤ 1 := by
    have he : Real.exp (-(k:ℝ)/40) ≤ 1 := Real.exp_le_one_iff.mpr (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
    dsimp [ω]
    linarith only [he]
  have hxi : xi x j=1+ω := by dsimp [xi,ω,k]; ring
  have hcut := failed_row_cutoff_budget hF.le hω hω1 k
  have hc := hx j hj hjm ω (failedRowCutoff F ω k) hxi hcut Q n hQ
  have hmodel : coordinateDecay (ω/4) k=rowModelDecay k := by
    dsimp [coordinateDecay,rowModelDecay,ω]
    ring
  have hBcut : B (failedRowCutoff F ω k)=rowMassCutoffHeight F (rowModelDecay k) := by
    rw [failed_row_cutoff_loglog,hmodel]
  rw [hBcut] at hc
  have hkm : k+1 ≤ m x := by dsimp [k]; omega
  have hg := (div_le_iff₀ (G_pos hB (m x))).mp (hp (k+1) hkm)
  rw [show m x-(k+1)=j-1 by dsimp [k]; omega] at hg
  have hrho : rho ≤ Real.exp (-3/5:ℝ) := by
    have he : rho=Real.exp (-lam) := by
      simp only [lam,one_div,Real.log_inv,neg_neg,Real.exp_log rho_pos]
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith only [collision_lambda_bounds.1])
  have hmass := projected_row_mass_bound hJ rho_pos hrho hF.le k
  have hbase : 0 ≤ A*(x/Real.log x)*G x (m x) :=
    mul_nonneg (mul_nonneg hA.le (div_nonneg (by linarith) (Real.log_pos hx1).le))
      (G_pos hB _).le
  calc
    _ ≤ A*(x/Real.log x)*G x (j-1)*
        Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2) := hc
    _ = (A*(x/Real.log x)*
        Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2))*G x (j-1) := by ring
    _ ≤ (A*(x/Real.log x)*
        Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2))*
        (J^(k+1)*rho^((k+1)*k/2)*G x (m x)) :=
      mul_le_mul_of_nonneg_left hg (mul_nonneg
        (mul_nonneg hA.le (div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le))
        (Real.exp_pos _).le)
    _ = (A*(x/Real.log x)*G x (m x))*
        (J^(k+1)*rho^((k+1)*k/2)*
          Real.exp (10*(Real.log (rowMassCutoffHeight F (rowModelDecay k)+4))^2)) := by ring
    _ ≤ (A*(x/Real.log x)*G x (m x))*
        (Real.exp (210*(rowModelConstant F)^2+105*(Real.log J)^2+Real.log J)*
          Real.exp (-(k:ℝ)^2/4)) := mul_le_mul_of_nonneg_left hmass hbase
    _ = _ := by dsimp [C,k]; ring

end TotientAsymptotic

end

end OAI
