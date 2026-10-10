import OAI.MeasureTheory.Falconer.Recursion.ReachedStateRecursion
import OAI.MeasureTheory.Falconer.Recursion.BranchErrorBounds

namespace OAI

namespace PlanarFalconer
namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

noncomputable def exponentSum (b : PolicyBranch A N q sig n) (lam eps : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))

noncomputable def weight (b : PolicyBranch A N q sig n) (lam eps : ℝ) : ℝ :=
  ((2:ℝ)^N)^(b.exponentSum lam eps)

theorem weight_pos (b : PolicyBranch A N q sig n) (lam eps : ℝ) : 0 < b.weight lam eps := by
  unfold weight
  positivity

theorem exponentSum_extend (b : PolicyBranch A N q sig n) (lam eps : ℝ)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).exponentSum lam eps = b.exponentSum lam eps+
      branchExponent A lam sig eps (b.state n) l u := by
  unfold exponentSum
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hj := Finset.mem_range.mp hj
    rw [b.extend_state_le hu hstep hj.le,b.extend_label_lt hu hstep hj,
      b.extend_state_le hu hstep (by omega : j+1 ≤ n)]
  · rw [b.extend_state_le hu hstep le_rfl,b.extend_last_label,b.extend_last_state]

theorem weight_extend (b : PolicyBranch A N q sig n) (lam eps : ℝ)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).weight lam eps = b.weight lam eps*
      ((2:ℝ)^N)^(branchExponent A lam sig eps (b.state n) l u) := by
  unfold weight
  rw [exponentSum_extend,Real.rpow_add (by positivity)]

theorem weight_eq_product (b : PolicyBranch A N q sig n) (lam eps : ℝ) :
    b.weight lam eps = ∏ j ∈ Finset.range n,
      ((2:ℝ)^N)^(branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) :=
  Real.rpow_sum_of_pos (by positivity) _ _

theorem weight_zero (b : PolicyBranch A N q sig 0) (lam eps : ℝ) : b.weight lam eps = 1 := by
  simp [weight,exponentSum]

end PolicyBranch

theorem uniform_source_weighted_terminal {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DiscreteProfileLipschitz A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      b.weight lam (eta/(2*(1+20/kap+1/sig))) *
        ((2:ℝ)^N)^(200*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      ((2:ℝ)^N)^(2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*kap+10^6*(lam+sig)/kap+eta) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_branch_exponent hlam hsig hkap hkap1 hgap heta
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (h₀ N hN A hA n b hi)

theorem uniform_source_weighted_error {lam sig kap T eps : ℝ}
    (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1) (hgap : sig < kap/1000)
    (hloss : 4000*(lam+sig) ≤ 1) (heps : eps ≤ 1)
    (hT : 1000*(1/sig+1/kap)+1000 < T) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DiscreteProfileLipschitz A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).index = 0 →
      b.weight lam eps*((2:ℝ)^N)^(-T) ≤ ((2:ℝ)^N)^(-10:ℝ) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_source_error_branch hsig hkap hkap1 hgap hloss heps hT
  refine ⟨N₀,hN₀,?_⟩
  intro N hN A hA n b hi
  rw [PolicyBranch.weight,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N),add_comm]
  exact h₀ N hN A hA n b hi

end PlanarFalconer

end OAI
