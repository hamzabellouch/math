import OAI.MeasureTheory.Falconer.Estimates.PolicyRootApplication

namespace OAI

/-! # The fixed branch factor and the root error in the outer assembly -/

namespace Falconer
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

noncomputable def PolicyJetData.rootExponent {m : ℕ} (P : PolicyJetData m) (σ κ η : ℝ) : ℝ :=
  2*P.policy P.a-PlanarFalconer.potential P.policy P.a P.t (10*sourcePolicyBlock P.N κ)+
    500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) P.lam σ+σ)/κ+η

theorem PolicyJetData.rootExponent_nonneg {m : ℕ} (P : PolicyJetData m)
    {σ κ η : ℝ} (hσ : 0 ≤ σ) (hκ : 0 < κ) (hη : 0 ≤ η) (hlam : 0 ≤ P.lam)
    (hq : P.q = sourcePolicyBlock P.N κ)
    (hwide : P.a+100*P.q < P.t)
    (hratio : (sourcePolicyBlock P.N κ:ℝ)/P.N ≤ 2*κ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    0 ≤ P.rootExponent σ κ η := by
  have hA : DimensionalProfileLipschitz (m+3) P.policy P.N := by
    rw [hprofile]
    exact profileExcess_dimensional_lipschitz P.regular P.N_pos
  have hqpos := P.q_pos
  have hpot := dimensional_potential_le_final_start P.N_pos hA
    (show 0 < 10*sourcePolicyBlock P.N κ by rw [← hq]; omega)
    (show P.a+10*sourcePolicyBlock P.N κ ≤ P.t by rw [← hq]; omega)
    (P.base_right.trans P.base_N) (le_refl P.a) (show P.a ≤ P.t by omega)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hpot
  have hcost : 20*((m+3:ℕ):ℝ)*(sourcePolicyBlock P.N κ:ℝ)/P.N ≤
      500*((m+3:ℕ):ℝ)*κ := by
    calc
      _ = (20*((m+3:ℕ):ℝ))*((sourcePolicyBlock P.N κ:ℝ)/P.N) := by ring
      _ ≤ (20*((m+3:ℕ):ℝ))*(2*κ) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (m+3)) hκ.le]
  have hloss : 0 ≤ 10^6*(dimensionalBranchReserve (m+3) P.lam σ+σ)/κ := by
    have hh := dimensionalBranchReserve_nonneg (m+3) hlam hσ
    positivity
  have hpot' : PlanarFalconer.potential P.policy P.a P.t (10*sourcePolicyBlock P.N κ) ≤
      2*P.policy P.a+20*((m+3:ℕ):ℝ)*(sourcePolicyBlock P.N κ:ℝ)/P.N := by
    convert hpot using 1
    ring
  have hpaid := hpot'.trans (add_le_add_right hcost (2*P.policy P.a))
  unfold rootExponent
  linarith only [hpaid,hloss,hη]

theorem PolicyJetData.rootBound_le_single_power {m : ℕ} (P : PolicyJetData m)
    (σ κ η : ℝ) (he : 0 ≤ P.rootExponent σ κ η) :
    P.rootBound σ κ η ≤ (2*4^(sourceSmoothingLevels σ κ+1))*
      ((2:ℝ)^P.N)^(P.rootExponent σ κ η) := by
  have herr : ((2:ℝ)^P.N)^(-10:ℝ) ≤ ((2:ℝ)^P.N)^(P.rootExponent σ κ η) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  change 4^(sourceSmoothingLevels σ κ+1)*
    (((2:ℝ)^P.N)^(P.rootExponent σ κ η)+((2:ℝ)^P.N)^(-10:ℝ)) ≤ _
  calc
    _ ≤ 4^(sourceSmoothingLevels σ κ+1)*
        (((2:ℝ)^P.N)^(P.rootExponent σ κ η)+((2:ℝ)^P.N)^(P.rootExponent σ κ η)) := by gcongr
    _ = _ := by ring

theorem eventual_policy_root_coefficient (σ κ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (m : ℕ) (P : PolicyJetData m), N₀ ≤ P.N → ∀ η : ℝ,
      0 ≤ P.rootExponent σ κ η →
      P.rootBound σ κ η ≤ ((2:ℝ)^P.N)^(P.rootExponent σ κ η+ε) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hε
    (2*4^(sourceSmoothingLevels σ κ+1))
  refine ⟨N₀,?_⟩
  intro m P hN η he
  apply (P.rootBound_le_single_power σ κ η he).trans
  calc
    _ ≤ ((2:ℝ)^P.N)^ε*((2:ℝ)^P.N)^(P.rootExponent σ κ η) :=
      mul_le_mul_of_nonneg_right (hN₀ P.N hN) (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by positivity),add_comm]

end Falconer

end OAI
