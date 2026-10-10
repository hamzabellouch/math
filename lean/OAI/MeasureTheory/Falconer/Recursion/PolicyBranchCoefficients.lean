import OAI.MeasureTheory.Falconer.Graphs.PolicyGraphStep
import OAI.MeasureTheory.Falconer.Estimates.PolicyFarStep
import OAI.MeasureTheory.Falconer.Recursion.BranchExponentAlgebra

namespace OAI

/-! # Dimension-dependent coefficient payments in the scalar branch ledger -/

namespace Falconer
open Set MeasureTheory

def dimensionalBranchReserve (d : ℕ) (lam σ : ℝ) : ℝ := ((d:ℝ)+1)*(lam+σ)

theorem dimensionalBranchReserve_nonneg (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) : 0 ≤ dimensionalBranchReserve d lam σ := by
  unfold dimensionalBranchReserve
  positivity

theorem graph_loss_le_branch_reserve (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) :
    (1000*((d:ℝ)+1)+32*d)*σ+4*((d:ℝ)+1)*lam ≤
      4000*(dimensionalBranchReserve d lam σ+σ) := by
  unfold dimensionalBranchReserve
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hlam,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hσ]

theorem near_loss_le_branch_reserve (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) :
    4*((d:ℝ)+1)*lam ≤ 4000*(dimensionalBranchReserve d lam σ+σ) :=
  (le_add_of_nonneg_left (by positivity : 0 ≤ (1000*((d:ℝ)+1)+32*d)*σ)).trans
    (graph_loss_le_branch_reserve d hlam hσ)

private theorem absorbed_power_coefficient {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y z : ℝ, y ≤ z →
      C*((2:ℝ)^N)^(x+y) ≤ ((2:ℝ)^N)^(x+z+ε) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hε C
  refine ⟨N₀,?_⟩
  intro N hN x y z hyz
  calc
    _ ≤ ((2:ℝ)^N)^ε*((2:ℝ)^N)^(x+y) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(ε+(x+y)) := (Real.rpow_add (by positivity) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (by linarith)

theorem eventual_policy_graph_coefficient (m K : ℕ) {lam σ ε : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ P : PolicyJetData m, P.lam = lam → P.σ = σ → N₀ ≤ P.N →
      ∀ p : ℕ,
      P.graphCoefficient p *
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2) ≤
      ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N p-
        profileExcess (d := m+3) P.profile P.N P.a)+
        PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
        4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε) := by
  let C : ℝ := 2*11^(m+3)*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2)
  obtain ⟨N₀,hN₀⟩ := absorbed_power_coefficient hε C
  refine ⟨N₀,?_⟩
  intro P hLam hσP hN p
  have he := hN₀ P.N hN
    (-2*(profileExcess (d := m+3) P.profile P.N p-
      profileExcess (d := m+3) P.profile P.N P.a)+
      PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p)
    ((1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*σ+4*(((m+3:ℕ):ℝ)+1)*lam)
    (4000*(dimensionalBranchReserve (m+3) lam σ+σ))
    (graph_loss_le_branch_reserve (m+3) hlam hσ)
  convert he using 1
  unfold PolicyJetData.graphCoefficient C
  rw [hLam,hσP]
  have hexp :
      -(profileExcess (d := m+3) P.profile P.N p-profileExcess (d := m+3) P.profile P.N P.a)-
        (profileExcess (d := m+3) P.profile P.N p-profileExcess (d := m+3) P.profile P.N P.a)+
        PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
        (1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*σ+4*(((m+3:ℕ):ℝ)+1)*lam =
      -2*(profileExcess (d := m+3) P.profile P.N p-profileExcess (d := m+3) P.profile P.N P.a)+
        PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) P.a p+
        ((1000*(((m+3:ℕ):ℝ)+1)+32*(m+3:ℕ))*σ+4*(((m+3:ℕ):ℝ)+1)*lam) := by ring
  rw [hexp]
  ring

theorem eventual_policy_near_coefficient (m K : ℕ) {lam σ ε : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ P : PolicyJetData m, P.lam = lam → N₀ ≤ P.N →
      ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
        ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
          profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2) ≤
      ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
        profileExcess (d := m+3) P.profile P.N P.a)+
        4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε) := by
  let C : ℝ := ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2)
  obtain ⟨N₀,hN₀⟩ := absorbed_power_coefficient hε C
  refine ⟨N₀,?_⟩
  intro P hLam hN
  have he := hN₀ P.N hN
    (-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
      profileExcess (d := m+3) P.profile P.N P.a))
    (4*(((m+3:ℕ):ℝ)+1)*lam) (4000*(dimensionalBranchReserve (m+3) lam σ+σ))
    (near_loss_le_branch_reserve (m+3) hlam hσ)
  convert he using 1
  rw [hLam]
  dsimp [C]
  ring

end Falconer

end OAI
