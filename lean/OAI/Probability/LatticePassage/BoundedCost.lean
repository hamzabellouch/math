import OAI.Probability.LatticePassage.UniformCheapPaths
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Filter Topology

theorem unbounded_cheap_paths_null (x : Vertex) (m : ℕ) :
    environmentLaw {ω : Environment | ∀ R : ℕ, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ (m : ℝ)} = 0 := by
  let E := {ω : Environment | ∀ R : ℕ, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ (m : ℝ)}
  have hb (n : ℕ) : environmentLaw.real E ≤
      (8 / 3 : ℝ) * exp (5 * (m : ℝ)) * (1 / 2 : ℝ)^(n+1) := by
    have hsub : E ⊆ {ω : Environment | ∃ z ∈ ({x} : Finset Vertex), ∃ y,
        ∃ (p : lattice.Walk z y), p.IsPath ∧ n+1 ≤ p.length ∧ pathCost ω p ≤ (m : ℝ)} := by
      intro ω hω
      obtain ⟨y,p,hp,hl,hc⟩ := hω (n+1)
      exact ⟨x, by simp, y,p,hp,hl,hc⟩
    have hle := ENNReal.toReal_mono (measure_ne_top environmentLaw _) (measure_mono (μ := environmentLaw) hsub)
    have h := no_long_cheap_paths ({x} : Finset Vertex) (n+1) (by omega) m (by positivity)
    exact hle.trans (by simpa [measureReal_def] using h)
  have ht : Tendsto (fun n : ℕ =>
      (8 / 3 : ℝ) * exp (5 * (m : ℝ)) * (1 / 2 : ℝ)^(n+1)) atTop (𝓝 0) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).mul_const (1/2 : ℝ)
    simpa only [← pow_succ, zero_mul, mul_zero] using hp.const_mul ((8/3 : ℝ) * exp (5*(m:ℝ)))
  have hz : environmentLaw.real E = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) ENNReal.toReal_nonneg
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.zero_ne_top).mp
  simpa [measureReal_def, E] using hz

theorem bounded_cost_path_lengths : ∀ᵐ ω ∂environmentLaw, ∀ x : Vertex, ∀ m : ℕ,
    ∃ R : ℕ, ∀ y, ∀ p : lattice.Walk x y,
      p.IsPath → pathCost ω p ≤ (m : ℝ) → p.length < R := by
  rw [ae_all_iff]
  intro x
  rw [ae_all_iff]
  intro m
  have ha : ∀ᵐ ω ∂environmentLaw, ¬ (∀ R : ℕ, ∃ y, ∃ (p : lattice.Walk x y),
      p.IsPath ∧ R ≤ p.length ∧ pathCost ω p ≤ (m : ℝ)) := by
    simpa only [ae_iff, not_not] using unbounded_cheap_paths_null x m
  filter_upwards [ha] with ω hω
  obtain ⟨R,hR⟩ := not_forall.mp hω
  refine ⟨R, ?_⟩
  intro y p hp hc
  by_contra hlen
  exact hR ⟨y,p,hp, Nat.le_of_not_gt hlen,hc⟩

end CompanionFPP

end OAI
