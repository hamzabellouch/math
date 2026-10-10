import OAI.Combinatorics.BalancedRyser.Probability.FiniteHistory

namespace OAI

open MeasureTheory ProbabilityTheory Filter Finset Preorder
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.FiniteHistory

variable {S : Type*} [Fintype S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

theorem ae_pmf_nonzero (p : PMF S) : ∀ᵐ s ∂p.toMeasure, p s ≠ 0 := by
  rw [ae_iff]
  change p.toMeasure p.supportᶜ = 0
  exact (p.toMeasure_apply_eq_zero_iff MeasurableSet.of_discrete).2
    disjoint_compl_right

theorem ae_initial_state (step : ℕ → S → PMF S) (s₀ : S) :
    ∀ᵐ ω ∂pathLaw step s₀, ω 0 = s₀ := by
  have hp : (pathLaw step s₀).map (frestrictLe 0) =
      Measure.dirac (fun _ : Iic 0 ↦ s₀) := by
    rw [map_prefix_pathLaw, Kernel.partialTraj_self, Kernel.id_apply]
  have hi : ∀ᵐ h ∂(pathLaw step s₀).map (frestrictLe 0),
      h ⟨0, mem_Iic.mpr le_rfl⟩ = s₀ := by
    rw [hp]
    exact (ae_dirac_iff MeasurableSet.of_discrete).2 rfl
  exact ae_of_ae_map (by fun_prop) hi

theorem ae_step_support (step : ℕ → S → PMF S) (s₀ : S) (n : ℕ) :
    ∀ᵐ ω ∂pathLaw step s₀, step n (ω n) (ω (n + 1)) ≠ 0 := by
  have hp : ∀ᵐ z ∂((pathLaw step s₀).map (frestrictLe n)) ⊗ₘ historyKernel step n,
      step n (z.1 ⟨n, mem_Iic.mpr le_rfl⟩) z.2 ≠ 0 := by
    apply Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete
    apply Eventually.of_forall
    intro h
    exact ae_pmf_nonzero (step n (h ⟨n, mem_Iic.mpr le_rfl⟩))
  rw [← map_prefix_next_pathLaw] at hp
  exact ae_of_ae_map (f := fun ω : Path S ↦ (frestrictLe n ω, ω (n + 1)))
    (by fun_prop) hp

theorem ae_all_invariant (step : ℕ → S → PMF S) (s₀ : S)
    (P : ℕ → S → Prop) (h₀ : P 0 s₀)
    (hstep : ∀ n s t, step n s t ≠ 0 → P n s → P (n + 1) t) :
    ∀ᵐ ω ∂pathLaw step s₀, ∀ n, P n (ω n) := by
  filter_upwards [ae_initial_state step s₀,
    ae_all_iff.2 (fun n ↦ ae_step_support step s₀ n)] with ω hi hs
  intro n
  induction n with
  | zero => simpa only [hi] using h₀
  | succ n ih => exact hstep n (ω n) (ω (n + 1)) (hs n) ih

end Balanced.FiniteHistory

end OAI
