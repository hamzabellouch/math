import OAI.MeasureTheory.Falconer.Fourier.PolicyJetChildren
import OAI.MeasureTheory.Falconer.Fourier.JetStateNear

namespace OAI

/-! # Uniform stopping bound for actual angular policy states -/

namespace Falconer
open Set MeasureTheory

theorem eventual_policy_angular_terminal (m K : ℕ) {ε W : ℝ}
    (hε : 0 < ε) (hW : 0 ≤ W) (Ψ : ℝ → ℝ)
    (hΨW : ∀ u, Ψ u ≤ W) (hsupp : ∀ u, 4 < u → Ψ u = 0) :
    ∃ N₀ : ℕ, ∀ (P : PolicyJetData m) (L : ℕ), N₀ ≤ P.N →
      P.a ≤ P.N → P.t ≤ P.a+100*P.q → 1 ≤ P.Z →
      P.envelope K L Ψ ≤
        ((2:ℝ)^P.N)^(100*((m+3:ℕ):ℝ)*P.q/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam+ε) := by
  let C : ℝ := 4*W*((descriptorJetBound (m+3) K)^K)^4*
    (sphereMeasure (m+3)).real univ^2
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hε C
  refine ⟨N₀,?_⟩
  intro P L hN ha ht hZ
  have hz : P.Z⁻¹ ≤ 1 := (inv_le_one₀ P.Z_pos).mpr hZ
  have hJ : 0 ≤ (descriptorJetBound (m+3) K)^K :=
    pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) K
  have hpower : ((descriptorJetBound (m+3) K)^K*P.Z⁻¹)^4 ≤
      ((descriptorJetBound (m+3) K)^K)^4 := by
    apply pow_le_pow_left₀ (mul_nonneg hJ (inv_nonneg.mpr P.Z_pos.le))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hJ
  have hcost : 4*W*((descriptorJetBound (m+3) K)^K*P.Z⁻¹)^4*
      (sphereMeasure (m+3)).real univ^2 ≤ C := by
    dsimp [C]
    gcongr
  have htR : (P.t:ℝ) ≤ (P.a:ℝ)+100*P.q := by exact_mod_cast ht
  have hterm := profile_jetState_terminal (K := K) (L := L) (D := 1) P.list
    P.Q P.ρ P.regular P.N_pos P.σ P.J P.i P.masks P.separated P.Z_pos ha
    P.X P.Y P.X_length P.Y_length (P.t:ℝ) htR Ψ hW hΨW hsupp
  apply hterm.trans
  calc
    _ ≤ C*((2:ℝ)^P.N)^(100*((m+3:ℕ):ℝ)*P.q/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ ≤ ((2:ℝ)^P.N)^ε*
        ((2:ℝ)^P.N)^(100*((m+3:ℕ):ℝ)*P.q/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam) :=
      mul_le_mul_of_nonneg_right (hN₀ P.N hN) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]; congr 1; ring

end Falconer

end OAI
