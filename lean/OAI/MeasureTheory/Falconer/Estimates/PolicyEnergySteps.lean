import OAI.MeasureTheory.Falconer.Estimates.PolicyEnergy
import OAI.MeasureTheory.Falconer.Recursion.PolicyRecursionBounds

namespace OAI

/-! # Applying the analytic recurrences to actual branch energies -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (BranchState BranchStep BranchLabel branchExponent policyDepth)

namespace PolicyJetData
variable {m : ℕ}

def ChildrenBound (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ)
    (w₀ : Sphere (m+3)) (s : BranchState) (ε M : ℝ) : Prop :=
  ∀ u l, BranchStep P.policy P.N P.q P.σ s l u →
    ∀ x, PolicyEnergy K L Ψ w₀ P.context u x →
      ((2:ℝ)^P.N)^(branchExponent P.policy
        (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε s l u)*x ≤ M

theorem positive_energy_step (P : PolicyJetData m) {K L N₀ : ℕ} {ε T : ℝ}
    {Ψ : ℝ → ℝ} (w₀ : Sphere (m+3))
    (hrec : PolicyRecursionBounds m K L P.J P.lam P.σ ε T P.Z N₀ Ψ)
    (hN : N₀ ≤ P.N) (hi : P.i+1 ≤ P.J)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N)
    (hleft : P.a₀ = P.a) (hright : P.t₀ = P.t)
    (hwide : P.a+100*P.q < P.t) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hcover : ∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
      dist w c ≤ descriptorMaskRadius P.N P.σ b/2)
    (hlo : 125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖)
    (hhi : ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
      2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side)
    (M : ℝ) (hM : 0 ≤ M) (hfloor : ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*P.lam+ε) ≤ M)
    (hchildren : P.ChildrenBound K L Ψ w₀ P.positiveBranchState ε M) :
    P.positiveCount w₀ ≤ 3*M+((2:ℝ)^P.N)^(-T) := by
  by_cases hside : 2*policyDepth P.policy P.N P.q P.a P.t ≤ P.a+P.t
  · apply hrec.positive P rfl rfl rfl rfl hN hi hleft hright hwide hq hside hcover
      hlo hhi w₀ M hM hfloor
    · intro v hv hgap
      have hb := hchildren _ _ (P.positive_low_branch hwide hv hgap) _
        (P.energy_positiveSuccessor K L Ψ w₀ v
          ((Finset.mem_Ioc.mp hv).2.trans P.base_right) (P.i+1) hlo hhi)
      change ((2:ℝ)^P.N)^(branchExponent P.policy
        (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε P.positiveBranchState .low
        (.D P.a v (P.i+1)))*_ ≤ M at hb
      rw [P.low_branchExponent] at hb
      exact hb
    · intro v hv hgap p hp hap row hrow
      subst p
      have hb := hchildren _ _ (P.positive_high_branch hwide hside hleft hright hv hgap hap row hrow) _
        (PolicyEnergy.angular
          ((P.atFrequency v ((Finset.mem_Ioc.mp hv).2.trans P.base_right)).child
            (policyDepth P.policy P.N P.q P.a P.t) hap row hrow))
      change ((2:ℝ)^P.N)^(branchExponent P.policy
        (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε P.positiveBranchState .high
        (.H P.a₀ P.t₀ (policyDepth P.policy P.N P.q P.a P.t) v P.i))*_ ≤ M at hb
      have he : branchExponent P.policy (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε
          P.positiveBranchState .high (.H P.a₀ P.t₀ (policyDepth P.policy P.N P.q P.a P.t) v P.i) =
          branchExponent P.policy (dimensionalBranchReserve (m+3) P.lam P.σ) P.σ ε
          P.positiveBranchState .high (.H P.a P.t (policyDepth P.policy P.N P.q P.a P.t) v P.i) := by
        rw [hleft,hright]
      rw [he,← P.directWeight_eq_high_branchExponent _ _ _ _ _ hprofile] at hb
      exact hb
  · have hp := (PlanarFalconer.policyDepth_interior P.policy P.q_pos
      (PlanarFalconer.policyBlocks_nonempty P.q_pos (P.base_right.trans P.base_N) hwide)).2
    have hs := P.positive_suffix_branch hwide (by omega)
    have hb := hchildren _ _ hs _
      (P.energy_positiveSuccessor K L Ψ w₀ (policyDepth P.policy P.N P.q P.a P.t)
        ((hp.trans (Nat.sub_le _ _)).trans P.base_right) (P.i+1) hlo hhi)
    simp only [positiveBranchState] at hb
    rw [← P.suffixWeight_eq_branchExponent _ _ _ _ hprofile] at hb
    have he := hrec.suffix P rfl rfl rfl hN (by omega) hwide (by omega) hlo w₀
    have hstep : P.positiveCount w₀ ≤ M := he.trans hb
    have herr : 0 ≤ ((2:ℝ)^P.N)^(-T) := by positivity
    linarith


theorem angular_energy_step (P : PolicyJetData m) {K L N₀ : ℕ} {ε T : ℝ}
    {Ψ : ℝ → ℝ} (w₀ : Sphere (m+3))
    (hrec : PolicyRecursionBounds m K L P.J P.lam P.σ ε T P.Z N₀ Ψ)
    (hN : N₀ ≤ P.N) (hi : P.i+1 ≤ P.J) (hσ : 0 < P.σ) (hZ : 1 ≤ P.Z)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N)
    (hbase : (P.t₀:ℝ) ≤ P.t+P.σ*P.N)
    (hwide : P.a+100*P.q < P.t) (hq : P.σ*(P.N:ℝ) ≤ P.q)
    (hceil : ⌈10*P.σ*(P.N:ℝ)⌉₊ < P.q) (hq10 : 10*P.σ*(P.N:ℝ) ≤ P.q)
    (M : ℝ) (hM : 0 ≤ M)
    (hchildren : P.ChildrenBound K L Ψ w₀ P.branchState ε M) :
    P.envelope K L Ψ ≤ 3*M+((2:ℝ)^P.N)^(-T) := by
  by_cases hfar : P.a < P.splitDepth
  · have hnear : ∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (P.splitDepth-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (P.splitDepth-P.a),
        P.farWeight P.splitDepth P.lam P.σ ε *
          (P.child P.splitDepth hfar.le row hrow).envelope K L Ψ ≤ M := by
      intro row hrow
      rw [P.nearWeight_eq_branchExponent _ _ _ hprofile]
      exact hchildren _ _ (P.near_branch hwide hfar) _
        (P.energy_child K L Ψ w₀ P.splitDepth hfar.le row hrow)
    have hcollisions : ∀ b ∈ Finset.Icc (P.a+9) (P.splitDepth+6),
        ENNReal.ofReal (P.farWeight b P.lam P.σ ε)*
          farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
            P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a) ≤ ENNReal.ofReal M := by
      intro b hb
      have hab : P.a ≤ b := by have := (Finset.mem_Icc.mp hb).1; omega
      have hw : 0 < P.farWeight b P.lam P.σ ε := by unfold farWeight; positivity
      have hends (U : List (Fin (m+3) → Bool)) (hU : U.length = P.a)
          (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
          (hr : row ∈ farCellPartners (P.Q.descendant U) P.ρ (b-P.a)) :
          (P.farPositiveSuccessor b hab U hU row hr).positiveCount w₀ ≤
            M/P.farWeight b P.lam P.σ ε := by
        apply (le_div_iff₀ hw).mpr
        have he := hchildren _ _ (P.far_branch hwide hfar hb) _
          (P.energy_farPositiveSuccessor K L Ψ w₀ b hab U hU row hr)
        rw [← P.farWeight_eq_branchExponent _ _ _ _ hprofile] at he
        simpa only [mul_comm] using he
      have hmax := P.farCollisionMaximum_le_positive_successors b hab w₀
        (M/P.farWeight b P.lam P.σ ε) (hends P.X P.X_length) (hends P.Y P.Y_length)
      calc
        _ ≤ ENNReal.ofReal (P.farWeight b P.lam P.σ ε)*
            ENNReal.ofReal (M/P.farWeight b P.lam P.σ ε) := mul_le_mul' le_rfl hmax
        _ = ENNReal.ofReal M := by
          rw [← ENNReal.ofReal_mul hw.le,mul_div_cancel₀ _ hw.ne']
    have he := hrec.far P rfl rfl hN hfar hZ w₀ M hM hnear hcollisions
    linarith
  · obtain ⟨d,hd⟩ := PlanarFalconer.actual_direct_policy_witness P.policy hσ.le P.q_pos
      hceil hq hq10 hbase hwide (Nat.le_of_not_gt hfar)
    have hchild : ∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ ((P.directGeometry d hd).p-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ ((P.directGeometry d hd).p-P.a),
        P.directWeight (P.directGeometry d hd).p P.lam P.σ ε *
          (P.child (P.directGeometry d hd).p (P.directGeometry d hd).ap row hrow).envelope K L Ψ ≤ M := by
      intro row hrow
      rw [P.directWeight_eq_branchExponent _ _ _ _ hprofile]
      exact hchildren _ _ (P.direct_branch hwide hd) _
        (P.energy_child K L Ψ w₀ (P.directGeometry d hd).p (P.directGeometry d hd).ap row hrow)
    have he := hrec.graph P rfl rfl rfl rfl hN hi (P.directGeometry d hd) M hM hchild
    linarith

end PolicyJetData
end Falconer

end OAI
