import OAI.NumberTheory.TotientAsymptotic.FailedRowCutoff
import OAI.NumberTheory.TotientAsymptotic.FordDimensionScale

namespace OAI

/-! Failure of the initial Ford simplex row has a uniform Gaussian saving. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem top_row_failure_count : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ Ψ : ℕ, Ψ ≤ m x → ∀ Q : Finset ℕ,
      (∀ v ∈ Q,∃ n : ℕ,0 < n ∧ n.totient=v ∧ (v:ℝ) ≤ x ∧
        xi x 0*B x < fordRowSum (m x) (fordPrimeCoordinate n) 0) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  obtain ⟨C,F,hC,hF,hcount⟩ := real_coordinate_deviation
  refine ⟨C,hC,?_⟩
  filter_upwards [dimension_row_model_budget hF.le,central_volume_one_le,
    eventually_ge_atTop (512:ℝ),eventually_ge_atTop (2*Real.exp (Real.exp 1)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hb hG hx hxexp hB
  intro Ψ hΨ Q hQ
  let k := m x
  let ω : ℝ := Real.exp (-(k:ℝ)/40)/10000
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hω1 : ω ≤ 1 := by
    have he : Real.exp (-(k:ℝ)/40) ≤ 1 := Real.exp_le_one_iff.mpr
      (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
    dsimp [ω]
    linarith only [he]
  have hmodel : coordinateDecay (ω/4) k=rowModelDecay k := by
    dsimp [coordinateDecay,rowModelDecay,ω]
    ring
  have hbudget := failed_row_cutoff_budget hF.le hω hω1 k
  obtain ⟨_,_,_,_,_,_,hthreshold,_,_⟩ := hbudget
  rw [failed_row_cutoff_loglog,hmodel] at hthreshold
  have hthreshold' : max 300000000 ((coordinateBudgetConstant F/coordinateDecay (ω/4) k)^(4/3:ℝ)) ≤ B x-1 := by
    rw [hmodel]
    exact hthreshold.trans (by dsimp [k] at *; linarith only [hb.1])
  have hc := hcount x hx hxexp k (ω/4) (by linarith) (by linarith) hthreshold' Q (by
    intro v hv
    obtain ⟨n,hn,hφ,hvx,hrow⟩ := hQ v hv
    refine ⟨⟨n,hn,hφ⟩,hvx,n,hn,hφ,?_⟩
    have hxi : xi x 0=1+ω := by dsimp [xi,ω,k]; ring
    rw [hxi] at hrow
    have hsum : fordRowSum (m x) (fordPrimeCoordinate n) 0 =
        ∑ i : Fin k,a (i.val+1)*fordPrimeCoordinate n (i.val+1) := by
      simpa only [Nat.sub_zero,fordCofactor_zero hn] using
        (fordRowSum_cofactor (n:=n) (L:=m x) (j:=0) (Nat.zero_le _))
    rw [hsum] at hrow
    have hh := mul_le_mul_of_nonneg_right (show 1+ω/4 ≤ 1+ω by linarith) hB.le
    exact hh.trans hrow.le)
  have hΨsq : (Ψ:ℝ)^2 ≤ (m x:ℝ)^2 := by
    have hle : (Ψ:ℝ) ≤ m x := by exact_mod_cast hΨ
    nlinarith only [hle,Nat.cast_nonneg (α:=ℝ) Ψ,Nat.cast_nonneg (α:=ℝ) (m x)]
  have hsave : Real.exp (-coordinateDecay (ω/4) k*B x) ≤ Real.exp (-(Ψ:ℝ)^2/4) := by
    apply Real.exp_le_exp.mpr
    rw [hmodel]
    dsimp [k]
    linarith only [hb.2,hΨsq]
  have hx1 : 1 < x := by linarith only [hx]
  have hfac : 0 ≤ C*(x/Real.log x) := mul_nonneg hC.le
    (div_nonneg (by linarith only [hx]) (Real.log_pos hx1).le)
  calc
    _ ≤ C*(x/Real.log x)*Real.exp (-coordinateDecay (ω/4) k*B x) := by
      simpa only [div_eq_mul_inv,mul_assoc] using hc
    _ ≤ C*(x/Real.log x)*Real.exp (-(Ψ:ℝ)^2/4) := mul_le_mul_of_nonneg_left hsave hfac
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hG hfac
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
