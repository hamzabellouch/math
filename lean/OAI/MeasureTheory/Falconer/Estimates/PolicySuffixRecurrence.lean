import OAI.MeasureTheory.Falconer.Shells.PolicyPositiveBand
import OAI.MeasureTheory.Falconer.Recursion.PolicyBranchCoefficients

namespace OAI

/-! # The actual positive suffix reduction with the scalar branch weight -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (policyDepth)

namespace PolicyJetData
variable {m : ℕ}

noncomputable def suffixWeight (P : PolicyJetData m) (p : ℕ) (lam σ ε : ℝ) : ℝ :=
  ((2:ℝ)^P.N)^(Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N
    (((m+3:ℕ):ℝ)/2) p P.t+4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε)

theorem suffixWeight_eq_branchExponent (P : PolicyJetData m) (p : ℕ) (lam σ ε : ℝ)
    (hprofile : P.policy = profileExcess (d := m+3) P.profile P.N) :
    P.suffixWeight p lam σ ε = ((2:ℝ)^P.N)^(PlanarFalconer.branchExponent P.policy
      (dimensionalBranchReserve (m+3) lam σ) σ ε (.D P.a P.t P.i) (.suffix) (.D P.a p (P.i+1))) := by
  unfold suffixWeight PlanarFalconer.branchExponent PlanarFalconer.branchCost
  simp only [PlanarFalconer.BranchState.start,PlanarFalconer.BranchState.finish,
    sub_self,mul_zero,zero_add,reduceCtorEq,ite_false,hprofile]
  rfl

end PolicyJetData

theorem exists_policy_positive_suffix_recurrence (m : ℕ) {lam σ ε : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 < σ) (hε : 0 < ε) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ P : PolicyJetData m,
      P.lam = lam → P.σ = σ → P.J = J → N₀ ≤ P.N → P.i ≤ P.J →
      P.a+100*P.q < P.t → P.a+P.t < 2*policyDepth P.policy P.N P.q P.a P.t →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ∀ (w₀ : Sphere (m+3)),
      P.positiveCount w₀ ≤ P.suffixWeight (policyDepth P.policy P.N P.q P.a P.t) lam σ ε *
        (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
          P.N P.σ P.J (P.i+1) P.q P.a (policyDepth P.policy P.N P.q P.a P.t) P.X P.Y).toReal := by
  obtain ⟨Ns,hs⟩ := uniform_policy_suffix_count (d := m+3) hσ hJ
  let C : ℝ := ((PlanarFalconer.bandOffsets (100*(((m+3:ℕ):ℝ)+1))).card:ℝ)*
    ((PlanarFalconer.bandOffsets 3).card:ℝ)
  obtain ⟨Nc,hc⟩ := Regularization.fixed_constant_absorbed hε C
  refine ⟨max Ns Nc,?_⟩
  intro P _hLam hσP hJP hN hi hwide hside hlo w₀
  let := P.regular.probability
  have hbound := hs P.N ((le_max_left _ _).trans hN) P.Q P.unit P.ρ
    (fun u => P.profile (u/P.N)) P.policy P.q P.a (policyDepth P.policy P.N P.q P.a P.t)
    P.t P.i P.q_pos (P.base_right.trans P.base_N) hwide rfl hside
    (by simpa only [hJP] using hi) w₀ P.X P.Y P.X_length P.Y_length hlo
  rw [← hσP,← hJP] at hbound
  have ht := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) ENNReal.ofReal_ne_top
    · exact positiveCollisionCount_ne_top w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
        P.N P.σ P.J (P.i+1) P.q P.a (policyDepth P.policy P.N P.q P.a P.t) P.X P.Y) hbound
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2:ℝ)^P.N)^(
      Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N (((m+3:ℕ):ℝ)/2)
        (policyDepth P.policy P.N P.q P.a P.t) P.t+1000*(((m+3:ℕ):ℝ)+1)*P.σ))] at ht
  have hcoeff : C*((2:ℝ)^P.N)^(
      Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N (((m+3:ℕ):ℝ)/2)
        (policyDepth P.policy P.N P.q P.a P.t) P.t+1000*(((m+3:ℕ):ℝ)+1)*P.σ) ≤
      P.suffixWeight (policyDepth P.policy P.N P.q P.a P.t) lam σ ε := by
    unfold PolicyJetData.suffixWeight
    rw [hσP]
    calc
      _ ≤ ((2:ℝ)^P.N)^ε*((2:ℝ)^P.N)^(
          Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N (((m+3:ℕ):ℝ)/2)
            (policyDepth P.policy P.N P.q P.a P.t) P.t+1000*(((m+3:ℕ):ℝ)+1)*σ) :=
        mul_le_mul_of_nonneg_right (hc P.N ((le_max_right _ _).trans hN)) (by positivity)
      _ = ((2:ℝ)^P.N)^(ε+(
          Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N (((m+3:ℕ):ℝ)/2)
            (policyDepth P.policy P.N P.q P.a P.t) P.t+1000*(((m+3:ℕ):ℝ)+1)*σ)) :=
        (Real.rpow_add (by positivity) _ _).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
        have hr := graph_loss_le_branch_reserve (m+3) hlam hσ.le
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (m+3)) hσ.le]
  change _ ≤ (C*_)*_ at ht
  exact ht.trans (mul_le_mul_of_nonneg_right hcoeff ENNReal.toReal_nonneg)

end Falconer

end OAI
