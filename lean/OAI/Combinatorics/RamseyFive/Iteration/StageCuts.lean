import Mathlib

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section
lemma stage_cuts (n : ℕ) (hn : 40000≤n) :
    8≤n/100 ∧ (n:ℝ)≤200*(n/100:ℕ) ∧
    (100:ℝ)*(n/100:ℕ)≤n ∧ (n/20000:ℕ)≤n/100 ∧
    ((n/20000:ℕ):ℝ)≤(n/100:ℕ)/100 ∧ (n:ℝ)≤40000*(n/20000:ℕ) := by
  have h1 : 8≤n/100 := by omega
  have h2 : n≤200*(n/100) := by omega
  have h3 : 100*(n/100)≤n := by omega
  have h4 : n/20000≤n/100 := by omega
  have h5 : 100*(n/20000)≤n/100 := by omega
  have h6 : n≤40000*(n/20000) := by omega
  refine ⟨h1,?_,?_,h4,?_,?_⟩
  · exact_mod_cast h2
  · exact_mod_cast h3
  · have hh : (100:ℝ)*(n/20000:ℕ)≤(n/100:ℕ) := by exact_mod_cast h5
    linarith
  · exact_mod_cast h6

theorem eventually_marking_small {η : ℝ} (hη : 0<η) (c : ℝ) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀n : ℕ,c*Real.exp σ*σ^(1+η)≤n→
      40000≤n ∧ 19200*Real.exp σ*σ≤n := by
  have ht : Tendsto (fun σ : ℝ=>c*Real.exp σ) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  have hp : Tendsto (fun σ : ℝ=>c*σ^η) atTop atTop :=
    (tendsto_rpow_atTop hη).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_ge_atTop 40000,hp.eventually_ge_atTop 19200]
    with σ hσ he hp
  intro n hn
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hpow : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
  have hm:=mul_le_mul_of_nonneg_left hpow (by positivity : 0≤c*Real.exp σ)
  have hnreal : (40000:ℝ)≤n := by nlinarith
  have hh:=mul_le_mul_of_nonneg_right hp (by positivity : 0≤Real.exp σ*σ)
  have hid : c*Real.exp σ*σ^(1+η)=(c*σ^η)*(Real.exp σ*σ) := by
    rw [Real.rpow_add hs,Real.rpow_one];ring
  exact ⟨by exact_mod_cast hnreal,by rw [hid] at hn;nlinarith⟩
end
end SharpRamseyFive.ParameterHierarchy

end OAI
