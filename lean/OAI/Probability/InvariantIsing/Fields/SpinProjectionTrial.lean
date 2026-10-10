import OAI.Probability.InvariantIsing.Core.FiniteProjectionTrial

namespace OAI

/-! Actual restricted spin partitions admit the projected canonical law as
a trial law. The prior remains the mass inherited from the full cube. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

theorem restrictedSpinLog_projection_bound {N : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (f : Spin N → Spin N)
    (hf : ∀ σ, f σ ∈ S) (H : Spin N → ℝ) (t : ℝ) :
    logPartition H - restrictedSpinLog S H ≤
      (∑ σ, finiteCanonicalWeights H σ * (H σ - H (f σ))) +
      t * (∑ σ, finiteCanonicalWeights H σ * (hammingDist σ (f σ) : ℝ)) +
      N * Real.log (1 + Real.exp (-t)) := by
  classical
  let : Nonempty {τ // τ ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  let g : Spin N → {τ // τ ∈ S} := fun σ => ⟨f σ, hf σ⟩
  have hkernel (τ : {τ // τ ∈ S}) :
      (∑ σ ∈ Finset.univ.filter (fun σ => g σ = τ),
        Real.exp (-(t * (hammingDist σ (f σ) : ℝ)))) ≤
          (1 + Real.exp (-t)) ^ N := by
    calc
      _ = ∑ σ ∈ Finset.univ.filter (fun σ => g σ = τ),
          Real.exp (-t * (hammingDist σ τ.val : ℝ)) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        have he : f σ = τ.val := congrArg Subtype.val (Finset.mem_filter.mp hσ).2
        rw [he]
        congr 1
        ring
      _ ≤ ∑ σ : Spin N, Real.exp (-t * (hammingDist σ τ.val : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun σ _ _ => (Real.exp_pos _).le)
      _ = _ := sum_exp_hamming τ.val t
  have he := log_sum_exp_projection_bound g H (fun τ => H τ.val)
    (fun σ => t * (hammingDist σ (f σ) : ℝ)) _ (by positivity) hkernel
  have hsum : (∑ τ : {τ // τ ∈ S}, Real.exp (H τ.val)) =
      ∑ τ ∈ S, Real.exp (H τ) := by
    change (∑ τ ∈ S.attach, Real.exp (H τ.val)) = _
    exact Finset.sum_attach S (fun τ : Spin N => Real.exp (H τ))
  rw [hsum, Real.log_pow] at he
  have hcost : (∑ σ, finiteCanonicalWeights H σ * (t * (hammingDist σ (f σ) : ℝ))) =
      t * (∑ σ, finiteCanonicalWeights H σ * (hammingDist σ (f σ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [hcost] at he
  rw [logPartition_eq, log_card_spin, restrictedSpinLog]
  change Real.log (∑ σ, Real.exp (H σ)) - ↑N * Real.log 2 -
      (Real.log (∑ σ ∈ S, Real.exp (H σ)) - ↑N * Real.log 2) ≤ _
  change Real.log (∑ σ, Real.exp (H σ)) ≤ Real.log (∑ σ ∈ S, Real.exp (H σ)) +
    (∑ σ, finiteCanonicalWeights H σ * (H σ - H (f σ))) +
    t * (∑ σ, finiteCanonicalWeights H σ * (hammingDist σ (f σ) : ℝ)) +
    ↑N * Real.log (1 + Real.exp (-t)) at he
  linarith

end InvariantIsing

end

end OAI
