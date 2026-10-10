import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserFlow

namespace OAI

/-! The actual time-one map is a bijection of physical space. This follows
from forward uniqueness and trajectories with terminal data, rather than
from assuming that the continuity equation already produces a diffeomorphism. -/

noncomputable section
open scoped Topology NNReal
namespace ContinuumCoulomb

theorem moser_trajectory_unique_terminal {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2)
    {α β : ℝ → Position}
    (hα : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t)
    (hβ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t)
    (hone : α 1 = β 1) : Set.EqOn α β (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  have hleft (γ : ℝ → Position)
      (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Icc (0 : ℝ) 1) t)
      (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      HasDerivWithinAt γ (moserVelocity rho V t (γ t)) (Set.Iic t) t := by
    apply (hγ t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset (Icc_mem_nhdsLE ht.1)
    exact Set.Icc_subset_Icc_right ht.2
  exact ODE_solution_unique_of_mem_Icc_left (s := fun _ => Set.univ)
    (fun t ht => (hK t ⟨ht.1.le, ht.2⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hα) (hleft α hα) (fun _ _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hβ) (hleft β hβ) (fun _ _ => Set.mem_univ _) hone

/-- The usual exponential spatial-dependence bound for these actual curves. -/
theorem moser_trajectory_spatial_bound {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ K : ℝ≥0, ∀ (α β : ℝ → Position),
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt α (moserVelocity rho V t (α t)) (Set.Icc (0 : ℝ) 1) t) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt β (moserVelocity rho V t (β t)) (Set.Icc (0 : ℝ) 1) t) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (α t) (β t) ≤ dist (α 0) (β 0) * Real.exp ((K : ℝ) * t) := by
  obtain ⟨L, K, hL, hK, ht⟩ := moserVelocity_uniform_bounds hrho V hV hc hbound
  refine ⟨K, fun α β hα hβ t ht => ?_⟩
  have hright (γ : ℝ → Position)
      (hγ : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (moserVelocity rho V s (γ s)) (Set.Icc (0 : ℝ) 1) s)
      (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
      HasDerivWithinAt γ (moserVelocity rho V s (γ s)) (Set.Ici s) s := by
    apply (hγ s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
    apply Filter.mem_of_superset (Icc_mem_nhdsGE hs.2)
    exact Set.Icc_subset_Icc_left hs.1
  simpa only [sub_zero] using
    dist_le_of_trajectories_ODE_of_mem (s := fun _ => Set.univ)
      (fun s hs => (hK s ⟨hs.1, hs.2.le⟩).lipschitzOnWith)
      (HasDerivWithinAt.continuousOn hα) (hright α hα) (fun _ _ => Set.mem_univ _)
      (HasDerivWithinAt.continuousOn hβ) (hright β hβ) (fun _ _ => Set.mem_univ _)
      (le_refl (dist (α 0) (β 0))) t ht

/-- The generated time-one map is globally Lipschitz, bijective, and fixes
the complement of the compact well support. -/
theorem moser_time_one_exists {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (hc : HasCompactSupport V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho / 2) :
    ∃ G : Position → ℝ → Position,
      (∀ x, G x 0 = x) ∧
      (∀ x, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (G x) (moserVelocity rho V t (G x t)) (Set.Icc (0 : ℝ) 1) t) ∧
      Function.Bijective (fun x => G x 1) ∧
      (∃ C : ℝ≥0, LipschitzWith C (fun x => G x 1)) ∧
      (∀ x, x ∉ tsupport V → G x 1 = x) := by
  obtain ⟨G, L, hG0, hG, hGt, hfix⟩ := moser_flow_exists hrho V hV hc hbound
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  refine ⟨G, hG0, hG, ⟨?_, ?_⟩, ?_, fun x hx => hfix x hx 1 h11⟩
  · intro x y hxy
    have h := moser_trajectory_unique_terminal hrho V hV hc hbound (hG x) (hG y) hxy h01
    simpa only [hG0] using h
  · intro y
    obtain ⟨β, hβ1, hβ⟩ := moser_trajectory_exists hrho V hV hc hbound ⟨1, h11⟩ y
    refine ⟨β 0, ?_⟩
    have h := moser_trajectory_unique hrho V hV hc hbound (hG (β 0)) hβ (hG0 (β 0)) h11
    exact h.trans hβ1
  · obtain ⟨K, hK⟩ := moser_trajectory_spatial_bound hrho V hV hc hbound
    refine ⟨⟨Real.exp (K : ℝ), (Real.exp_pos _).le⟩, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (G x 1) (G y 1) ≤ Real.exp (K : ℝ) * dist x y
    simpa only [hG0, mul_one, mul_comm] using hK (G x) (G y) (hG x) (hG y) 1 h11

end ContinuumCoulomb

end

end OAI
