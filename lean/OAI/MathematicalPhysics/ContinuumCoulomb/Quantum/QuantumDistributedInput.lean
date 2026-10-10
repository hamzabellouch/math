import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalInput

namespace OAI

/-! Input checks may occur at separate history times before their qubits are changed. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaInputCheck (c : QMACircuit) (i : Fin (c.work+1)) (s : SourceSpinBasis (c.work+1)) : Prop :=
  c.witness ≤ i.val ∧ s i ≠ 0

theorem qmaMask_norm_sq {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaMask p u‖^2 = ∑ s, if p s then ‖u s‖^2 else 0 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : p s <;> simp [qmaMask_apply,hs]

theorem qmaInputPenalty_le_checks (c : QMACircuit)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaInputPenalty c u ≤ ∑ i : Fin (c.work+1), ‖qmaMask (qmaInputCheck c i) (u 0)‖^2 := by
  simp only [qmaInputPenalty,qmaMask_norm_sq]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro s _
  have h := mul_le_mul_of_nonneg_right (qmaAncillaCount_dominates c s) (sq_nonneg ‖u 0 s‖)
  have hs : (∑ i : Fin (c.work+1), if qmaInputCheck c i s then ‖u 0 s‖^2 else 0) =
      qmaAncillaCount c s*‖u 0 s‖^2 := by
    rw [qmaAncillaCount,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : c.witness ≤ i.val ∧ s i ≠ 0
    · simp [qmaInputCheck,hi]
    · simp [qmaInputCheck,hi]
  rw [hs]
  convert h using 1
  by_cases hc : QMAAncillaZero c s <;> simp [hc]

def qmaDistributedInput (c : QMACircuit) (τ : Fin (c.work+1) → ℕ)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  ∑ i : Fin (c.work+1), ‖qmaMask (qmaInputCheck c i) (u (τ i))‖^2

theorem qmaInputPenalty_le_distributed (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → ℕ) (hτ : ∀ i, τ i ≤ c.gates.length)
    (hcheck : ∀ (i : Fin (c.work+1)) (v : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))),
      ‖qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c (τ i)) v)‖ =
        ‖qmaMask (qmaInputCheck c i) v‖)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    qmaInputPenalty c u ≤ 2*qmaDistributedInput c τ u+
      2*(c.work+1:ℝ)*c.gates.length*qmaPropagationEnergy c u := by
  apply (qmaInputPenalty_le_checks c u).trans
  have h (i : Fin (c.work+1)) : ‖qmaMask (qmaInputCheck c i) (u 0)‖^2 ≤
      2*‖qmaMask (qmaInputCheck c i) (u (τ i))‖^2+
        2*c.gates.length*qmaPropagationEnergy c u := by
    let v := qmaApplyMatrix (qmaPrefixMatrix c (τ i)) (u 0)
    have hd := pow_le_pow_left₀ (norm_nonneg _)
      (qmaMask_sub_norm_le (qmaInputCheck c i) v (u (τ i))) 2
    rw [norm_sub_rev v] at hd
    have ha := qma_history_anchor_bound c hc u (τ i) (hτ i)
    have hs := norm_add_sq_two (qmaMask (qmaInputCheck c i) (u (τ i)))
      (qmaMask (qmaInputCheck c i) v-qmaMask (qmaInputCheck c i) (u (τ i)))
    rw [add_sub_cancel, hcheck i (u 0)] at hs
    dsimp only [v] at hd
    linarith
  calc
    _ ≤ ∑ i : Fin (c.work+1),
        (2*‖qmaMask (qmaInputCheck c i) (u (τ i))‖^2+
          2*c.gates.length*qmaPropagationEnergy c u) := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,qmaDistributedInput]
      push_cast
      ring

def qmaDistributedHistoryEnergy (c : QMACircuit) (τ : Fin (c.work+1) → ℕ)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) : ℝ :=
  qmaOutputPenalty c u+14*qmaDistributedInput c τ u+
    (14*(c.work+1)+8)*c.gates.length*qmaPropagationEnergy c u

theorem qmaDistributedHistoryEnergy_sound (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → ℕ) (hτ : ∀ i, τ i ≤ c.gates.length)
    (hcheck : ∀ (i : Fin (c.work+1)) (v : EuclideanSpace ℂ (SourceSpinBasis (c.work+1))),
      ‖qmaMask (qmaInputCheck c i) (qmaApplyMatrix (qmaPrefixMatrix c (τ i)) v)‖ =
        ‖qmaMask (qmaInputCheck c i) v‖)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : ℕ → EuclideanSpace ℂ (SourceSpinBasis (c.work+1))) :
    2*qmaHistoryMass c u ≤ 5*(c.gates.length+1:ℝ)*qmaDistributedHistoryEnergy c τ u := by
  have h := qmaInputPenalty_le_distributed c hc τ hτ hcheck u
  have he : qmaHistoryEnergy c u ≤ qmaDistributedHistoryEnergy c τ u := by
    unfold qmaHistoryEnergy qmaDistributedHistoryEnergy
    nlinarith
  exact (qma_history_energy_sound c hc hsound u).trans
    (mul_le_mul_of_nonneg_left he (by positivity))

end ContinuumCoulomb

end

end OAI
