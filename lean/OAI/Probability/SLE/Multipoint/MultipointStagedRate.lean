import OAI.Probability.SLE.Multipoint.MultipointPiecewiseClock

namespace OAI

/-! The single adapted discount rate obtained by reading the current
finite stopping interval and its past-measurable switch pattern. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def stagedPatternRate {Ω ι : Type*} [DecidableEq ι]
    (N : ℕ) (s : Finset ι) (ρ : ι → Ω → ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (g : Finset ι → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  finiteSwitchRate ((Finset.range N).product s.powerset)
    (fun k => τ k.1) (fun k => τ (k.1+1))
    (fun k => switchPatternEvent s ρ (τ k.1) k.2) (fun k => g k.2)

theorem stagedPatternRate_eq {Ω ι : Type*} [DecidableEq ι]
    (N : ℕ) (s : Finset ι) (ρ : ι → Ω → ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (g : Finset ι → ℝ≥0 → Ω → ℝ) (hmono : ∀ ω, Monotone (fun n => τ n ω))
    (n : ℕ) (hn : n < N) (A : Finset ι) (hA : A ∈ s.powerset)
    (t : ℝ≥0) (ω : Ω) (hω : ω ∈ switchPatternEvent s ρ (τ n) A)
    (hnt : τ n ω ≤ t) (htn : t < τ (n+1) ω) :
    stagedPatternRate N s ρ τ g t ω = g A t ω := by
  classical
  unfold stagedPatternRate finiteSwitchRate
  rw [Finset.sum_eq_single (n,A)]
  · simp only [stoppedBranchRate, hω, hnt, htn, and_self, ite_true]
  · rintro ⟨m,C⟩ hmem hneq
    obtain ⟨_, hC⟩ := Finset.mem_product.mp hmem
    change stoppedBranchRate (τ m) (τ (m+1)) (switchPatternEvent s ρ (τ m) C) (g C) t ω = 0
    unfold stoppedBranchRate
    apply ite_eq_right
    rintro ⟨hωC, hmt, htm⟩
    have hmn : m = n := by
      rcases lt_trichotomy m n with h | h | h
      · exact False.elim ((not_le_of_gt htm) ((hmono ω (Nat.succ_le_of_lt h)).trans hnt))
      · exact h
      · exact False.elim ((not_le_of_gt htn) ((hmono ω (Nat.succ_le_of_lt h)).trans hmt))
    subst m
    have hCA : C = A := switchPatternEvent_unique s ρ (τ n)
      (Finset.mem_powerset.mp hC) (Finset.mem_powerset.mp hA) hωC hω
    exact hneq (Prod.ext rfl hCA)
  · intro h
    exact False.elim (h (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hn,hA⟩))

theorem stagedPatternRate_progressive {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    (ℱ : Filtration ℝ≥0 mΩ) (N : ℕ) (s : Finset ι)
    (ρ : ι → Ω → ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hρ : ∀ i ∈ s, IsStoppingTime ℱ (fun ω => (ρ i ω : WithTop ℝ≥0)))
    (hτ : ∀ n, IsStoppingTime ℱ (fun ω => (τ n ω : WithTop ℝ≥0)))
    (g : Finset ι → ℝ≥0 → Ω → ℝ) (hg : ∀ A ∈ s.powerset, IsProgressive ℱ (g A)) :
    IsProgressive ℱ (stagedPatternRate N s ρ τ g) := by
  exact finiteSwitchRate_progressive ℱ ((Finset.range N).product s.powerset)
    (fun k => τ k.1) (fun k => τ (k.1+1))
    (fun k _ => hτ k.1) (fun k _ => hτ (k.1+1))
    (fun k => switchPatternEvent s ρ (τ k.1) k.2)
    (fun k _ => switchPatternEvent_measurable ℱ s ρ (τ k.1) hρ (hτ k.1) k.2)
    (fun k => g k.2) (fun k hk => hg k.2 (Finset.mem_product.mp hk).2)

theorem stagedPatternRate_measurable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    (ℱ : Filtration ℝ≥0 mΩ) (N : ℕ) (s : Finset ι)
    (ρ : ι → Ω → ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hρ : ∀ i ∈ s, IsStoppingTime ℱ (fun ω => (ρ i ω : WithTop ℝ≥0)))
    (hτ : ∀ n, IsStoppingTime ℱ (fun ω => (τ n ω : WithTop ℝ≥0)))
    (g : Finset ι → ℝ≥0 → Ω → ℝ)
    (hg : ∀ A ∈ s.powerset, Measurable (Function.uncurry (g A))) :
    Measurable (Function.uncurry (stagedPatternRate N s ρ τ g)) := by
  apply finiteSwitchRate_measurable
  · exact fun k _ => stopping_time_measurable_nnreal (hτ k.1)
  · exact fun k _ => stopping_time_measurable_nnreal (hτ (k.1+1))
  · exact fun k _ => (hτ k.1).measurableSpace_le _
      (switchPatternEvent_measurable ℱ s ρ (τ k.1) hρ (hτ k.1) k.2)
  · exact fun k hk => hg k.2 (Finset.mem_product.mp hk).2

lemma stagedPatternRate_nonneg {Ω ι : Type*} [DecidableEq ι]
    (N : ℕ) (s : Finset ι) (ρ : ι → Ω → ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (g : Finset ι → ℝ≥0 → Ω → ℝ) (hg : ∀ A ∈ s.powerset, ∀ t ω, 0 ≤ g A t ω)
    (t : ℝ≥0) (ω : Ω) : 0 ≤ stagedPatternRate N s ρ τ g t ω :=
  finiteSwitchRate_nonneg _ _ _ _ _
    (fun k hk => hg k.2 (Finset.mem_product.mp hk).2) t ω

lemma stagedPatternRate_bound {Ω ι : Type*} [DecidableEq ι]
    (N : ℕ) (s : Finset ι) (ρ : ι → Ω → ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (g : Finset ι → ℝ≥0 → Ω → ℝ) (C : Finset ι → ℝ≥0)
    (hg : ∀ A ∈ s.powerset, ∀ t ω, |g A t ω| ≤ C A) (t : ℝ≥0) (ω : Ω) :
    |stagedPatternRate N s ρ τ g t ω| ≤
      (∑ k ∈ (Finset.range N).product s.powerset, C k.2 : ℝ≥0) :=
  finiteSwitchRate_norm_le ((Finset.range N).product s.powerset)
    (fun k => τ k.1) (fun k => τ (k.1+1))
    (fun k => switchPatternEvent s ρ (τ k.1) k.2) (fun k => g k.2) (fun k => C k.2)
    (fun k hk => hg k.2 (Finset.mem_product.mp hk).2) t ω

end SLEExactGauge.Multipoint

end

end OAI
