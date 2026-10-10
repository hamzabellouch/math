import OAI.MeasureTheory.Falconer.Recursion.BranchPotential
import OAI.MeasureTheory.Falconer.Recursion.SourceBranchDepth

namespace OAI

namespace PlanarFalconer

theorem branch_nonlow_indicator_sum (label : ℕ → BranchLabel) (n : ℕ) :
    (∑ j ∈ Finset.range n, if label j = .low then 0 else 1) = branchNonlowCount label n := by
  have htot := branch_count_total label n
  have hsum : branchCount label n .low +
      (∑ j ∈ Finset.range n, if label j = .low then 0 else 1) = n := by
    simp only [branchCount,← Finset.sum_add_distrib]
    calc
      _ = ∑ _j ∈ Finset.range n, (1:ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : label j = .low <;> simp [hj]
      _ = n := by simp
  omega

theorem branch_nonlow_loss_sum (label : ℕ → BranchLabel) (n : ℕ) (loss : ℝ) :
    (∑ j ∈ Finset.range n, if label j = .low then 0 else loss) =
      (branchNonlowCount label n:ℝ)*loss := by
  have hcast := congrArg (fun k : ℕ => (k:ℝ)) (branch_nonlow_indicator_sum label n)
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] at hcast
  calc
    _ = ∑ j ∈ Finset.range n, (if label j = .low then (0:ℝ) else 1)*loss := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : label j = .low <;> simp [hj]
    _ = _ := by rw [← Finset.sum_mul,hcast]

noncomputable def branchExponent (A : ℕ → ℝ) (lam sig eps : ℝ)
    (s : BranchState) (label : BranchLabel) (u : BranchState) : ℝ :=
  -2*(A u.start-A s.start)+branchCost A s label u+
    (if label = .low then 0 else 4000*(lam+sig))+eps

theorem branch_exponent_sum (A : ℕ → ℝ) (lam sig eps : ℝ)
    (state : ℕ → BranchState) (label : ℕ → BranchLabel) (n : ℕ) :
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (state j) (label j) (state (j+1))) =
      2*A (state 0).start-2*A (state n).start+
      (∑ j ∈ Finset.range n, branchCost A (state j) (label j) (state (j+1)))+
      (branchNonlowCount label n:ℝ)*(4000*(lam+sig))+(n:ℝ)*eps := by
  simp only [branchExponent,Finset.sum_add_distrib]
  rw [profile_increments_telescope A (fun j => (state j).start) n,branch_nonlow_loss_sum]
  simp

theorem source_branch_exponent {A : ℕ → ℝ} {N n : ℕ} {lam sig kap eta : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (heta : 0 < eta) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < sourcePolicyBlock N kap)
    (hslack : sig*(N:ℝ) ≤ sourcePolicyBlock N kap)
    (hqratio : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap)
    (hA : DiscreteProfileLipschitz A N)
    (b : PolicyBranch A N (sourcePolicyBlock N kap) sig n)
    (hinit : (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish) :
    let eps := eta/(2*(1+20/kap+1/sig))
    (∑ j ∈ Finset.range n, branchExponent A lam sig eps (b.state j) (b.label j) (b.state (j+1))) +
      (200*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*kap+10^6*(lam+sig)/kap+eta := by
  dsimp only
  have hq := sourcePolicyBlock_pos hN hkap
  have hc := b.costs_le_final_start hN hq hslack hA hinit
  have hb := source_branch_count_bounds hN hsig hkap hkap1 hceil b
  let D : ℝ := 1+20/kap+1/sig
  have hD : 0 < D := by dsimp [D]; positivity
  have heps : 0 ≤ eta/(2*D) := by positivity
  have htime : (n:ℝ)*(eta/(2*D)) ≤ eta/2 := by
    have hn : (n:ℝ) ≤ D := by dsimp [D]; linarith [hb.2.2]
    calc
      _ ≤ D*(eta/(2*D)) := mul_le_mul_of_nonneg_right hn heps
      _ = eta/2 := by field_simp
  have hloss : (branchNonlowCount b.label n:ℝ)*(4000*(lam+sig)) ≤ 80000*(lam+sig)/kap := by
    calc
      _ ≤ (20/kap)*(4000*(lam+sig)) := mul_le_mul_of_nonneg_right hb.1 (by positivity)
      _ = _ := by ring
  have hlamK : lam ≤ (lam+sig)/kap := by
    apply (le_div_iff₀ hkap).mpr
    have hh := mul_le_mul_of_nonneg_left hkap1 hlam
    linarith
  have hbudget : 0 ≤ (lam+sig)/kap := by positivity
  rw [branch_exponent_sum]
  dsimp only [D] at htime
  simp only [mul_div_assoc] at hc hloss ⊢
  nlinarith

theorem uniform_source_branch_exponent {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (heta : 0 < eta) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ A : ℕ → ℝ,
      DiscreteProfileLipschitz A N → ∀ n : ℕ,
      ∀ b : PolicyBranch A N (sourcePolicyBlock N kap) sig n,
      (b.state 0).start+10*sourcePolicyBlock N kap ≤ (b.state 0).finish →
      (∑ j ∈ Finset.range n, branchExponent A lam sig (eta/(2*(1+20/kap+1/sig)))
        (b.state j) (b.label j) (b.state (j+1))) +
        (200*(sourcePolicyBlock N kap:ℝ)/N+12*lam+eta/2) ≤
      2*A (b.state 0).start-potential A (b.state 0).start (b.state 0).finish
        (10*sourcePolicyBlock N kap)+500*kap+10^6*(lam+sig)/kap+eta := by
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_source_ceiling_slack hsig hgap
  obtain ⟨N₂,hN₂⟩ := exists_nat_gt (1/kap)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN A hA n b hi
  have hNp : 0 < N := by omega
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hNp
  have hkn : 1 < kap*(N:ℝ) := by
    have hh := (div_lt_iff₀ hkap).mp (hN₂.trans_le (Nat.cast_le.mpr (show N₂ ≤ N by omega)))
    linarith
  have hq : (sourcePolicyBlock N kap:ℝ) < kap*N+1 :=
    Nat.ceil_lt_add_one (mul_nonneg hkap.le hNR.le)
  have hqr : (sourcePolicyBlock N kap:ℝ)/(N:ℝ) ≤ 2*kap :=
    (div_le_iff₀ hNR).mpr (by linarith)
  exact source_branch_exponent hNp hlam hsig hkap hkap1 heta
    (h₁ N (by omega)).1 (h₁ N (by omega)).2.2 hqr hA b hi

end PlanarFalconer

end OAI
