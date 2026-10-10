import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourceScaleComparisons

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

lemma eventually_uniform_L {η : ℝ} (hη : 0<η) {Q : ℝ→Prop}
    (hQ : ∀ᶠ L : ℝ in atTop,Q L) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R → Q (scaleL σ η D) := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp hQ
  have ht := (tendsto_rpow_atTop (show 0<9*beta η by have := beta_pos hη; positivity)).eventually
    (eventually_ge_atTop a)
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with σ hσ hσ1 D R had
  exact ha _ (hσ.trans (scale_bounds hσ1 hη had).1)

lemma eventually_uniform_R {η : ℝ} (hη : 0<η) (a : ℝ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R → a≤(R:ℝ) := by
  have ht := (tendsto_rpow_atTop (beta_pos hη)).eventually (eventually_ge_atTop a)
  filter_upwards [ht] with σ hσ D R had
  exact hσ.trans had.R_lower

lemma two_pow_le_exp (R : ℕ) : (2:ℝ)^R≤Real.exp (R:ℝ) := by
  have ht : (2:ℝ)≤Real.exp 1 := by
    have hh := Real.add_one_le_exp (1:ℝ)
    norm_num at hh ⊢
    exact hh
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) ht R
  simpa only [←Real.exp_nat_mul,mul_one] using hh

theorem eventually_pencil_scalar_budgets {η : ℝ} (hη : 0<η) (C : ℝ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R N : ℕ),Admissible σ η D R → (N:ℝ)≤σ^2 →
      let L := scaleL σ η D
      let P := scaleP σ η D R
      C*2^R≤Real.exp (P/20) ∧
      (2*L^2)^R≤Real.exp (P/25) ∧
      C^2*Real.exp (L/50)+(N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/20) ∧
      2≤Real.exp (P/20) ∧
      400000*Real.exp (L/1000)≤Real.exp (P/100) := by
  have hconst : ∀ᶠ L : ℝ in atTop,C≤Real.exp (L/1000) ∧ C^2≤Real.exp (L/1000) := by
    have ht : Tendsto (fun L : ℝ => Real.exp (L/1000)) atTop atTop :=
      tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<1000))
    exact (ht.eventually (eventually_ge_atTop C)).and (ht.eventually (eventually_ge_atTop (C^2)))
  have hpoly : ∀ᶠ L : ℝ in atTop,2*L^2≤Real.exp (L/25) := by
    have hh := ScaleSelection.eventually_polynomial_le_exp_rpow 2 2 1 (1/25)
      (by norm_num) (by norm_num)
    simpa only [Real.rpow_one,Real.rpow_ofNat,div_eq_mul_inv,mul_comm,one_mul] using hh
  have hgrid := ScaleSelection.eventually_polynomial_le_exp_rpow 1 2 (9*beta η) (1/1000)
    (by have := beta_pos hη; positivity) (by norm_num)
  have hlarge : ∀ᶠ L : ℝ in atTop,1000000000≤L := eventually_ge_atTop _
  filter_upwards [eventually_uniform_L hη hconst,eventually_uniform_L hη hpoly,
    eventually_uniform_L hη hlarge,eventually_uniform_R hη 400,hgrid,
    eventually_ge_atTop (1:ℝ)] with σ hc hp hl hr hg hσ D R N had hN
  let L := scaleL σ η D
  let P := scaleP σ η D R
  have hL : 1000000000≤L := hl D R had
  have hR : (400:ℝ)≤R := hr D R had
  have hL0 : 0≤L := by linarith
  have hR1 : (1:ℝ)≤R := by linarith
  have hP : P=L*R := rfl
  have hPL : 400*L≤P := by rw [hP]; nlinarith
  have hPR : 1000000000*(R:ℝ)≤P := by rw [hP]; nlinarith
  have hP0 : 0≤P := by linarith
  have hcc := hc D R had
  change C≤Real.exp (L/1000) ∧ C^2≤Real.exp (L/1000) at hcc
  have hNN : (N:ℝ)≤Real.exp (L/1000) := by
    apply hN.trans
    calc
      σ^2≤Real.exp ((1/1000)*σ^(9*beta η)) := by simpa only [one_mul,Real.rpow_ofNat] using hg
      _ ≤ Real.exp (L/1000) := Real.exp_le_exp.mpr (by linarith [(scale_bounds hσ hη had).1])
  have ht := two_pow_le_exp R
  have h2 : (2:ℝ)≤Real.exp (P/40) := by
    have hh := Real.add_one_le_exp (P/40)
    linarith
  dsimp only
  change C*2^R≤Real.exp (P/20) ∧ (2*L^2)^R≤Real.exp (P/25) ∧
    C^2*Real.exp (L/50)+(N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/20) ∧
    2≤Real.exp (P/20) ∧ 400000*Real.exp (L/1000)≤Real.exp (P/100)
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      C*2^R≤Real.exp (L/1000)*Real.exp (R:ℝ) := mul_le_mul hcc.1 ht (by positivity) (Real.exp_pos _).le
      _ = Real.exp (L/1000+R) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (P/20) := Real.exp_le_exp.mpr (by linarith)
  · have hh := pow_le_pow_left₀ (show 0≤2*L^2 by positivity) (hp D R had) R
    apply hh.trans_eq
    rw [←Real.exp_nat_mul]
    congr 1
    rw [hP]
    ring
  · have hfirst : C^2*Real.exp (L/50)≤Real.exp (P/40) := by
      calc
        _ ≤ Real.exp (L/1000)*Real.exp (L/50) := mul_le_mul_of_nonneg_right hcc.2 (Real.exp_pos _).le
        _ = Real.exp (L/1000+L/50) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have hsecond : (N:ℝ)*2^R*Real.exp (P/50)≤Real.exp (P/40) := by
      calc
        _ ≤ (Real.exp (L/1000)*Real.exp (R:ℝ))*Real.exp (P/50) := by gcongr
        _ = Real.exp (L/1000+R+P/50) := by rw [←Real.exp_add,←Real.exp_add]
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ 2*Real.exp (P/40) := by linarith
      _ ≤ Real.exp (P/40)*Real.exp (P/40) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (P/20) := by rw [←Real.exp_add]; congr 1; ring
  · exact h2.trans (Real.exp_le_exp.mpr (by linarith))
  · have hnum : (400000:ℝ)≤Real.exp (L/1000) := by
      have hh := Real.add_one_le_exp (L/1000)
      linarith
    calc
      _ ≤ Real.exp (L/1000)*Real.exp (L/1000) := mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le
      _ = Real.exp (L/500) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end
end SharpLogRamsey.SourceScales

end

end OAI
