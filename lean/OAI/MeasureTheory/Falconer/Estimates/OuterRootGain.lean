import OAI.MeasureTheory.Falconer.Graphs.FlexibleGraphChild
import OAI.MeasureTheory.Falconer.Graphs.OuterGraphStep
import OAI.MeasureTheory.Falconer.Recursion.TwoRootGain

namespace OAI

/-! # The actual outer graph coefficient combined with the two recursive roots -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (sourcePolicyBlock sourceSmoothingLevels)

noncomputable def PolicyJetData.rootExponentAt {m : ℕ} (P : PolicyJetData m)
    (c : ℕ) (σ κ η : ℝ) : ℝ :=
  2*P.policy c-PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ)+
    500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) P.lam σ+σ)/κ+η

theorem PolicyJetData.rootExponentAt_nonneg {m : ℕ} (P : PolicyJetData m) (c : ℕ)
    {σ κ η : ℝ} (hσ : 0 ≤ σ) (hκ : 0 < κ) (hη : 0 ≤ η) (hlam : 0 ≤ P.lam)
    (hq : P.q = sourcePolicyBlock P.N κ)
    (hwide : c+100*P.q < P.t)
    (hratio : (sourcePolicyBlock P.N κ:ℝ)/P.N ≤ 2*κ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    0 ≤ P.rootExponentAt c σ κ η := by
  have hA : DimensionalProfileLipschitz (m+3) P.policy P.N := by
    rw [hprofile]
    exact profileExcess_dimensional_lipschitz P.regular P.N_pos
  have hqpos := P.q_pos
  have hpot := dimensional_potential_le_final_start P.N_pos hA
    (show 0 < 10*sourcePolicyBlock P.N κ by rw [← hq]; omega)
    (show c+10*sourcePolicyBlock P.N κ ≤ P.t by rw [← hq]; omega)
    (P.base_right.trans P.base_N) (le_refl c) (show c ≤ P.t by omega)
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
  have hpot' : PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ) ≤
      2*P.policy c+20*((m+3:ℕ):ℝ)*(sourcePolicyBlock P.N κ:ℝ)/P.N := by
    convert hpot using 1
    ring
  have hpaid := hpot'.trans (add_le_add_right hcost (2*P.policy c))
  unfold PolicyJetData.rootExponentAt
  linarith only [hpaid,hloss,hη]

theorem PolicyJetData.rootBoundAt_le_single_power {m : ℕ} (P : PolicyJetData m) (c : ℕ)
    (σ κ η : ℝ) (he : 0 ≤ P.rootExponentAt c σ κ η) :
    P.rootBoundAt c σ κ η ≤ (2*4^(sourceSmoothingLevels σ κ+1))*
      ((2:ℝ)^P.N)^(P.rootExponentAt c σ κ η) := by
  have herr : ((2:ℝ)^P.N)^(-10:ℝ) ≤ ((2:ℝ)^P.N)^(P.rootExponentAt c σ κ η) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  change 4^(sourceSmoothingLevels σ κ+1)*
    (((2:ℝ)^P.N)^(P.rootExponentAt c σ κ η)+((2:ℝ)^P.N)^(-10:ℝ)) ≤ _
  calc
    _ ≤ 4^(sourceSmoothingLevels σ κ+1)*
        (((2:ℝ)^P.N)^(P.rootExponentAt c σ κ η)+((2:ℝ)^P.N)^(P.rootExponentAt c σ κ η)) := by gcongr
    _ = _ := by ring


noncomputable def outerRootLoss (m : ℕ) (lam σ κ η : ℝ) : ℝ :=
  500*((m+3:ℕ):ℝ)*κ+10^6*(dimensionalBranchReserve (m+3) lam σ+σ)/κ+η

noncomputable def outerGraphLoss (m : ℕ) (lam σ : ℝ) : ℝ :=
  (1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*σ+4*(((m+3:ℕ):ℝ)+1)*lam

theorem outer_coefficient_two_root_gain {m K : ℕ} (P Q : PolicyJetData m)
    (hN : P.N = Q.N) (hLam : P.lam = Q.lam)
    (haP : P.a = 0) (haQ : Q.a = 0)
    (hprofileP : P.policy = profileExcess (d := m+3) P.profile P.N)
    (hprofileQ : Q.policy = profileExcess (d := m+3) Q.profile Q.N)
    (c : ℕ) (σ κ η β error C x y : ℝ) (hσP : P.σ = σ)
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxbound : x ≤ C*((2:ℝ)^P.N)^(P.rootExponentAt c σ κ η))
    (hybound : y ≤ C*((2:ℝ)^Q.N)^(Q.rootExponentAt c σ κ η))
    (hentry : min (PlanarFalconer.height P.policy 0 c) (PlanarFalconer.height Q.policy 0 c)-
      (PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ)+
        PlanarFalconer.potential Q.policy c Q.t (10*sourcePolicyBlock Q.N κ))/2 ≤ -β+error) :
    P.outerCoefficient Q c*
      (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*Real.sqrt (x*y)) ≤
    (2*11^(m+3)*(((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2)*C)*
      ((2:ℝ)^P.N)^(-β+error+outerRootLoss m P.lam σ κ η+outerGraphLoss m P.lam σ) := by
  let R : ℝ := (2:ℝ)^P.N
  let H := min (PlanarFalconer.height P.policy 0 c) (PlanarFalconer.height Q.policy 0 c)
  let D : ℝ := ((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hx' : x ≤ C*R^(2*P.policy c-
      PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ)+outerRootLoss m P.lam σ κ η) := by
    simpa only [PolicyJetData.rootExponentAt,outerRootLoss,R,add_assoc] using hxbound
  have hy' : y ≤ C*R^(2*Q.policy c-
      PlanarFalconer.potential Q.policy c Q.t (10*sourcePolicyBlock Q.N κ)+outerRootLoss m P.lam σ κ η) := by
    simpa only [PolicyJetData.rootExponentAt,← hN,← hLam,outerRootLoss,R,add_assoc] using hybound
  have hg := two_root_gain_at_entry hR hC hx hy (P.policy c) (Q.policy c)
    (PlanarFalconer.potential P.policy c P.t (10*sourcePolicyBlock P.N κ))
    (PlanarFalconer.potential Q.policy c Q.t (10*sourcePolicyBlock Q.N κ))
    H (outerRootLoss m P.lam σ κ η) β error hx' hy' hentry
  have hp0 : P.policy 0 = 0 := by rw [hprofileP]; exact profileExcess_zero P.Q P.ρ P.regular
  have hq0 : Q.policy 0 = 0 := by rw [hprofileQ]; exact profileExcess_zero Q.Q Q.ρ Q.regular
  have hcoeff : P.outerCoefficient Q c =
      2*11^(m+3)*(R^(outerGraphLoss m P.lam σ)*R^(-P.policy c-Q.policy c+H)) := by
    unfold PolicyJetData.outerCoefficient outerGraphLoss
    rw [haP,haQ,← hprofileP,← hprofileQ,hp0,hq0,hσP]
    rw [← Real.rpow_add (zero_lt_one.trans_le hR)]
    congr 2
    dsimp [H]
    ring
  rw [hcoeff]
  change (2*11^(m+3)*(R^(outerGraphLoss m P.lam σ)*R^(-P.policy c-Q.policy c+H)))*
    (D*Real.sqrt (x*y)) ≤ _
  calc
    _ = (2*11^(m+3)*D)*R^(outerGraphLoss m P.lam σ)*
      (R^(-P.policy c-Q.policy c+H)*Real.sqrt (x*y)) := by ring
    _ ≤ (2*11^(m+3)*D)*R^(outerGraphLoss m P.lam σ)*
      (C*R^(-β+error+outerRootLoss m P.lam σ κ η)) := by
      apply mul_le_mul_of_nonneg_left hg
      dsimp [D]
      positivity
    _ = (2*11^(m+3)*D*C)*(R^(outerGraphLoss m P.lam σ)*
        R^(-β+error+outerRootLoss m P.lam σ κ η)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hR)]
      congr 2
      ring

end Falconer

end OAI
