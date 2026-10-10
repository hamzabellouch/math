import OAI.NumberTheory.TotientAsymptotic.PrefixResidualCount
import OAI.NumberTheory.TotientAsymptotic.SmallTerminalPrefix
import OAI.NumberTheory.TotientAsymptotic.ProjectedGaussian
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor
import OAI.NumberTheory.TotientAsymptotic.RenewalInput
import OAI.NumberTheory.TotientAsymptotic.CollisionScale

namespace OAI

/-! Gaussian counting at the first coordinate below the fixed terminal cutoff. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem small_terminal_row_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ j : ℕ,1 ≤ j → j ≤ m x →
    ∀ Q : Finset ℕ,∀ n : ℕ → ℕ,
    (∀ v ∈ Q,0 < n v ∧ (n v).totient=v ∧ x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧
      (v:ℝ) ≤ x ∧ 2 < fordPrimeCoordinate (n v) (j-1) ∧
      fordPrimeCoordinate (n v) j ≤ 2 ∧
      (∀ i < j,fordRowSum (m x) (fordPrimeCoordinate (n v)) i ≤
        xi x i*(if i=0 then B x else fordPrimeCoordinate (n v) i))) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-((m x-j:ℕ):ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hcount⟩ := prefix_residual_value_count
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound fordRenewalInput
  let N : ℕ := ⌊Real.exp (Real.exp 2)⌋₊
  let E := primeEulerProduct N
  let C := A*E*Real.exp (105*(Real.log J)^2+Real.log J)
  have hE : 0 < E := primeEulerProduct_pos N
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hcount,hproj,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hp hx1 hB
  intro j hj hjm Q n hQ
  let D := Q.image (fun v => (fordCofactor (n v) j).totient)
  have hmass : (∑ d ∈ D,(d:ℝ)⁻¹) ≤ E := by
    apply smooth_residual_reciprocal_mass
    intro d hd
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hd
    refine ⟨Nat.totient_pos.mpr (fordCofactor_pos _ _),Nat.le_floor ?_⟩
    exact small_terminal_smooth (by norm_num) (hQ v hv).2.2.2.2.2.1
  have hc := hx j hj hjm Q n (by
    intro v hv
    obtain ⟨hn,hφ,hhead,hvx,hprev,hcur,_⟩ := hQ v hv
    exact ⟨hn,hφ,hhead,hvx,small_terminal_index (by omega) (by norm_num) hprev,
      small_terminal_gap (by omega) hprev hcur⟩) (by
    intro v hv
    by_cases hj1 : j=1
    · exact Or.inl hj1
    · exact Or.inr (terminal_prefix_conditions (by omega) hjm (by norm_num)
        (hQ v hv).2.2.2.2.1 (hQ v hv).2.2.2.2.2.2))
  have hfac : 0 ≤ A*(x/Real.log x)*G x (j-1) := by
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hG := G_pos hB (j-1)
    positivity
  have hc' : (Q.card:ℝ) ≤ (A*E)*(x/Real.log x)*G x (j-1) := by
    apply hc.trans
    have hh := mul_le_mul_of_nonneg_left hmass hfac
    convert hh using 1
    ring
  let k := m x-j
  have hkm : k+1 ≤ m x := by dsimp [k]; omega
  have hg := (div_le_iff₀ (G_pos hB (m x))).mp (hp (k+1) hkm)
  rw [show m x-(k+1)=j-1 by dsimp [k]; omega] at hg
  have hrho : rho ≤ Real.exp (-3/5:ℝ) := by
    have he : rho=Real.exp (-lam) := by
      simp only [lam,one_div,Real.log_inv,neg_neg,Real.exp_log rho_pos]
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith only [collision_lambda_bounds.1])
  have hfactor : J^(k+1)*rho^((k+1)*k/2) ≤
      Real.exp (105*(Real.log J)^2+Real.log J)*Real.exp (-(k:ℝ)^2/4) := by
    have hm := projected_gaussian_bound hJ rho_pos hrho k
    have he : 1 ≤ Real.exp ((k:ℝ)^2/21) := Real.one_le_exp (by positivity)
    have hn : 0 ≤ J^(k+1)*rho^((k+1)*k/2) := by
      have hr := rho_pos
      positivity
    have hh : J^(k+1)*rho^((k+1)*k/2) ≤
        J^(k+1)*rho^((k+1)*k/2)*Real.exp ((k:ℝ)^2/21) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he hn
    exact hh.trans hm
  have hbase : 0 ≤ (A*E)*(x/Real.log x)*G x (m x) := by
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hG := G_pos hB (m x)
    positivity
  calc
    _ ≤ (A*E)*(x/Real.log x)*G x (j-1) := hc'
    _ ≤ (A*E)*(x/Real.log x)*(J^(k+1)*rho^((k+1)*k/2)*G x (m x)) :=
      mul_le_mul_of_nonneg_left hg (by
        have hlog : 0 < Real.log x := Real.log_pos hx1
        positivity)
    _ = ((A*E)*(x/Real.log x)*G x (m x))*(J^(k+1)*rho^((k+1)*k/2)) := by ring
    _ ≤ ((A*E)*(x/Real.log x)*G x (m x))*
        (Real.exp (105*(Real.log J)^2+Real.log J)*Real.exp (-(k:ℝ)^2/4)) :=
      mul_le_mul_of_nonneg_left hfactor hbase
    _ = _ := by dsimp [C,k]; ring

end TotientAsymptotic

end

end OAI
