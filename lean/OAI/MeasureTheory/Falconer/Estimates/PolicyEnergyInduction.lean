import OAI.MeasureTheory.Falconer.Estimates.PolicyEnergySteps
import OAI.MeasureTheory.Falconer.Recursion.PolicyTerminal
import OAI.MeasureTheory.Falconer.Recursion.DimensionalBranchBounds
import OAI.MeasureTheory.Falconer.Recursion.WeightedBranchInduction

namespace OAI

/-! # The actual energies satisfy the scalar branch induction hypotheses -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep branchExponent)

theorem PolicyEnergy.recursion_step {m K L N₀ : ℕ} {ε T : ℝ} {Ψ : ℝ → ℝ}
    (w₀ : Sphere (m+3)) (Γ : PolicyContext m)
    (hrec : PolicyRecursionBounds m K L Γ.J Γ.lam Γ.σ ε T Γ.Z N₀ Ψ)
    (hN : N₀ ≤ Γ.N) (hσ : 0 < Γ.σ) (hZ : 1 ≤ Γ.Z)
    (hprofile : Γ.policy = profileExcess (d := m+3) Γ.profile Γ.N)
    (hcover : ∀ b, ∀ w : Sphere (m+3), ∃ c ∈ Γ.masks b,
      dist w c ≤ descriptorMaskRadius Γ.N Γ.σ b/2)
    (hq : Γ.σ*(Γ.N:ℝ) ≤ Γ.q)
    (hceil : ⌈10*Γ.σ*(Γ.N:ℝ)⌉₊ < Γ.q) (hq10 : 10*Γ.σ*(Γ.N:ℝ) ≤ Γ.q)
    (s : BranchState) (hs : s.Valid Γ.N Γ.σ) (hi : s.index+1 ≤ Γ.J)
    (hwide : s.start+100*Γ.q < s.finish) (M : ℝ) (hM : 0 ≤ M)
    (hfloor : ((2:ℝ)^Γ.N)^(4*(((m+3:ℕ):ℝ)+1)*Γ.lam+ε) ≤ M)
    (hchildren : ∀ u l, BranchStep Γ.policy Γ.N Γ.q Γ.σ s l u →
      ∀ x, PolicyEnergy K L Ψ w₀ Γ u x →
        ((2:ℝ)^Γ.N)^(branchExponent Γ.policy
          (dimensionalBranchReserve (m+3) Γ.lam Γ.σ) Γ.σ ε s l u)*x ≤ M)
    (x : ℝ) (hx : PolicyEnergy K L Ψ w₀ Γ s x) :
    x ≤ 3*M+((2:ℝ)^Γ.N)^(-T) := by
  cases hx with
  | positive P hleft hright hlo hhi =>
    exact P.positive_energy_step w₀ hrec hN hi hprofile hleft hright hwide hq
      (fun b _ => hcover b) hlo hhi M hM hfloor hchildren
  | angular P =>
    exact P.angular_energy_step w₀ hrec hN hi hσ hZ hprofile hs.2.2.2.2
      hwide hq hceil hq10 M hM hchildren

theorem eventual_policyEnergy_terminal (m K : ℕ) {ε W : ℝ}
    (hε : 0 < ε) (hW : 0 ≤ W) (Ψ : ℝ → ℝ)
    (hΨW : ∀ u, Ψ u ≤ W) (hsupp : ∀ u, 4 < u → Ψ u = 0) :
    ∃ N₀ : ℕ, ∀ (Γ : PolicyContext m) (L : ℕ), N₀ ≤ Γ.N → 1 ≤ Γ.Z →
      ∀ (w₀ : Sphere (m+3)) (s : BranchState), s.Valid Γ.N Γ.σ →
      s.finish ≤ s.start+100*Γ.q → ∀ x, PolicyEnergy K L Ψ w₀ Γ s x →
      x ≤ ((2:ℝ)^Γ.N)^(100*((m+3:ℕ):ℝ)*Γ.q/Γ.N+4*(((m+3:ℕ):ℝ)+1)*Γ.lam+ε) := by
  obtain ⟨N₀,hterm⟩ := eventual_policy_angular_terminal m K hε hW Ψ hΨW hsupp
  refine ⟨N₀,?_⟩
  intro Γ L hN hZ w₀ s hs hw x hx
  cases hx with
  | positive P hleft hright hlo hhi =>
    let := P.regular.probability
    have hp := positiveCollisionCount_terminal w₀ P.Q P.ρ P.regular P.N_pos P.policy
      P.σ P.J P.i P.q (hs.1.trans hs.2) hs.1 hw P.X P.Y P.X_length P.Y_length
    have hpr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    rw [ENNReal.toReal_ofReal (by positivity)] at hpr
    apply hpr.trans
    apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
    change 100*(P.q:ℝ)/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam ≤
      100*((m+3:ℕ):ℝ)*P.q/P.N+4*(((m+3:ℕ):ℝ)+1)*P.lam+ε
    have hd : (1:ℝ) ≤ (m+3:ℕ) := by exact_mod_cast (show 1 ≤ m+3 by omega)
    have hm : (100:ℝ)*P.q/P.N ≤ 100*((m+3:ℕ):ℝ)*P.q/P.N := by
      calc
        _ = 100*1*(P.q:ℝ)/P.N := by ring
        _ ≤ _ := by gcongr
    linarith
  | angular P =>
    exact hterm P L hN ((hs.2.1.trans hs.2.2.1).trans hs.2.2.2.1) hw hZ

end Falconer

end OAI
