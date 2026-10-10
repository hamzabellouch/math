import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserBounds
import Mathlib.Analysis.ODE.ExistUnique

namespace OAI

/-! Actual integral curves of the manufactured-density field exist through
time one. The flow is stationary outside the well support. No transport map
or ODE solution is introduced as an assumed analytic input. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

theorem moser_trajectory_exists {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    (t₀ : Set.Icc (0 : ℝ) 1) (x : Position) :
    ∃ α : ℝ → Position, α t₀ = x ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  have hf : IsPicardLindelof (moserVelocity rho V) t₀ x L 0 L K := {
    lipschitzOnWith := fun t ht => (hK t ht).lipschitzOnWith
    continuousOn := fun y _ => ht y
    norm_le := fun t ht y _ => hL t ht y
    mul_max_le := by
      have hm : max (1 - (t₀ : ℝ)) ((t₀ : ℝ) - 0) ≤ 1 :=
        max_le (by linarith [t₀.2.1]) (by linarith [t₀.2.2])
      simpa only [mul_one, NNReal.coe_zero, sub_zero] using
        mul_le_mul_of_nonneg_left hm L.coe_nonneg }
  exact hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Uniqueness is on the closed transport interval, including both endpoints. -/
theorem moser_trajectory_unique {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {α β : ℝ → Position}
    (hα : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t)
    (hβ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t)
    (hzero : α 0 = β 0) : Set.EqOn α β (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  have hright (γ : ℝ → Position)
      (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Icc (0 : ℝ) 1) t)
      (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Ici t) t := by
    apply (hγ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset (Icc_mem_nhdsGE ht.2)
    exact Set.Icc_subset_Icc_left ht.1
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hK t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hα) (hright α hα) (fun _ _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hβ) (hright β hβ) (fun _ _ => Set.mem_univ _) hzero

/-- A single family of actual trajectories, stationary outside the well,
with a uniform Lipschitz bound in time. -/
theorem moser_flow_exists {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ (G : Position → ℝ → Position) (L : ℝ≥0),
      (∀ x, G x 0 = x) ∧
      (∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (G x) (moserVelocity rho V t (G x t)) (Set.Icc (0 : ℝ) 1) t) ∧
      (∀ x, LipschitzOnWith L (G x) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ x, x ∉ tsupport V → ∀ t ∈ Set.Icc (0 : ℝ) 1, G x t = x) := by
  have hex (x : Position) := moser_trajectory_exists hrho V hV hc hbound
    ⟨0, by constructor <;> norm_num⟩ x
  choose G hG0 hG using hex
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  refine ⟨G, L, hG0, hG, ?_, ?_⟩
  · intro x
    exact (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (hG x) (fun t ht => by exact_mod_cast hL t ht (G x t))
  · intro x hx t ht
    have hconst (s : ℝ) (_hs : s ∈ Set.Icc (0 : ℝ) 1) :
        HasDerivWithinAt (fun _ : ℝ => x) (moserVelocity rho V s x)
          (Set.Icc (0 : ℝ) 1) s := by
      rw [moserVelocity_zero hx]
      exact hasDerivWithinAt_const s _ x
    exact moser_trajectory_unique hrho V hV hc hbound (hG x) hconst (hG0 x) ht

end ContinuumCoulomb

end

end OAI
