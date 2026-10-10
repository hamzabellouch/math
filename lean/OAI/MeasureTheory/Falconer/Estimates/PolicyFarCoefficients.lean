import OAI.MeasureTheory.Falconer.Recursion.PolicyBranchCoefficients

namespace OAI

/-! # Exact collision coefficients and their branch payments -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace PolicyJetData
variable {m : ℕ}

noncomputable def farWeight (P : PolicyJetData m) (b : ℕ) (lam σ ε : ℝ) : ℝ :=
  ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
    profileExcess (d := m+3) P.profile P.N P.a)+
    4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε)

noncomputable def collisionCoefficient (P : PolicyJetData m) (K : ℕ) (B C : ℝ) (b : ℕ) : ℝ :=
  C*(B^K*P.Z⁻¹)^4*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    PlanarFalconer.binKernelConstant.toReal*
    ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
      profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)

theorem collisionTerm_eq (P : PolicyJetData m) (K : ℕ) (B : ℝ) {C : ℝ}
    (hC : 0 ≤ C) (w₀ : Sphere (m+3)) (b : ℕ) :
    P.collisionTerm w₀ (C*(B^K*P.Z⁻¹)^4) b =
      ENNReal.ofReal (P.collisionCoefficient K B C b)*
        farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
          P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a) := by
  unfold collisionTerm collisionCoefficient
  rw [← ENNReal.ofReal_toReal PlanarFalconer.binKernelConstant_ne_top,← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 2
  ac_rfl

end PolicyJetData

theorem eventual_policy_far_coefficient (m K : ℕ) {B C lam σ ε : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (P : PolicyJetData m), P.lam = lam → 1 ≤ P.Z → N₀ ≤ P.N →
      ∀ b : ℕ, P.collisionCoefficient K B C b ≤ P.farWeight b lam σ ε := by
  let A : ℝ := C*(B^K)^4*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    PlanarFalconer.binKernelConstant.toReal
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hε A
  refine ⟨N₀,?_⟩
  intro P hLam hZ hN b
  have hz : P.Z⁻¹ ≤ 1 := (inv_le_one₀ P.Z_pos).mpr hZ
  have hb : 0 ≤ B^K := pow_nonneg (zero_le_one.trans hB) K
  have hpower : (B^K*P.Z⁻¹)^4 ≤ (B^K)^4 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hb
  have hA : C*(B^K*P.Z⁻¹)^4*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
      PlanarFalconer.binKernelConstant.toReal ≤ A := by
    dsimp [A]
    gcongr
  have hloss := near_loss_le_branch_reserve (m+3) hlam hσ
  unfold PolicyJetData.collisionCoefficient PolicyJetData.farWeight
  rw [hLam]
  calc
    _ ≤ A*((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
        profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ ((2:ℝ)^P.N)^ε*((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
        profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right (hN₀ P.N hN) (by positivity)
    _ = ((2:ℝ)^P.N)^(ε+(-2*(profileExcess (d := m+3) P.profile P.N b-
        profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*lam)) :=
      (Real.rpow_add (by positivity) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

theorem eventual_policy_collisionTerm_payment (m K : ℕ) {B C lam σ ε : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (P : PolicyJetData m), P.lam = lam → 1 ≤ P.Z → N₀ ≤ P.N →
      ∀ (w₀ : Sphere (m+3)) (b : ℕ),
      P.collisionTerm w₀ (C*(B^K*P.Z⁻¹)^4) b ≤
        ENNReal.ofReal (((2:ℝ)^P.N)^(-ε/2)) *
          (ENNReal.ofReal (P.farWeight b lam σ ε)*
            farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
              P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a)) := by
  obtain ⟨N₀,hN₀⟩ := eventual_policy_far_coefficient m K hB hC hlam hσ (half_pos hε)
  refine ⟨N₀,?_⟩
  intro P hLam hZ hN w₀ b
  rw [P.collisionTerm_eq K B hC w₀ b,← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply (hN₀ P hLam hZ hN b).trans_eq
  unfold PolicyJetData.farWeight
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]
  congr 1
  ring

end Falconer

end OAI
