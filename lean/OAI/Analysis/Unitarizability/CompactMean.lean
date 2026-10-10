import OAI.Analysis.Unitarizability.Model
import Mathlib.Analysis.Normed.Module.WeakDual
import OAI.Analysis.Unitarizability.Average

namespace OAI

/-! Weak-star compactness for positive normalized invariant means. -/
noncomputable section
namespace Dixmier
open Filter Topology
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- Approximate positive normalized means, with all finite translation tests,
have a positive normalized invariant weak-star cluster point. -/
theorem amenable_of_approximate_means
    (h : ∀ (S : Finset G) (ε : ℝ), 0 < ε →
      ∃ m : (G →ᵇ ℂ) →L[ℂ] ℂ,
        ‖m‖ ≤ 1 ∧ m (BoundedContinuousFunction.const G (1 : ℂ)) = 1 ∧
        (∀ b : G →ᵇ ℂ, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) →
          0 ≤ (m b).re ∧ (m b).im = 0) ∧
        ∀ g ∈ S, ∀ b : G →ᵇ ℂ, ‖m (leftTranslate g b) - m b‖ ≤ ε * ‖b‖) :
    Amenable G := by
  classical
  let J := Finset G × ℕ
  have hm : ∀ a : J, ∃ m : (G →ᵇ ℂ) →L[ℂ] ℂ,
      ‖m‖ ≤ 1 ∧ m (BoundedContinuousFunction.const G (1 : ℂ)) = 1 ∧
      (∀ b : G →ᵇ ℂ, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) →
        0 ≤ (m b).re ∧ (m b).im = 0) ∧
      ∀ g ∈ a.1, ∀ b : G →ᵇ ℂ, ‖m (leftTranslate g b) - m b‖ ≤
        (1 / ((a.2 : ℝ) + 1)) * ‖b‖ := by
    intro a
    exact h a.1 _ (by positivity)
  choose m hm using hm
  let μ : J → WeakDual ℂ (G →ᵇ ℂ) := fun a => StrongDual.toWeakDual (m a)
  have hball : ∀ a, μ a ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1 := by
    intro a
    change m a ∈ Metric.closedBall 0 1
    simpa [Metric.mem_closedBall, dist_zero_right] using (hm a).1
  obtain ⟨M, _, hM⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1).exists_mapClusterPt
    (f := (atTop : Filter J)) (u := μ)
    (by
      rw [Filter.le_principal_iff]
      change ∀ᶠ a in (atTop : Filter J), μ a ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (G →ᵇ ℂ)) 1
      exact Filter.Eventually.of_forall hball)
  refine ⟨M.toStrongDual.toLinearMap, ?_, ?_, ?_⟩
  · have hc : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | M (BoundedContinuousFunction.const G (1 : ℂ)) = 1} :=
      isClosed_eq (WeakDual.eval_continuous _) continuous_const
    exact hc.mem_of_mapClusterPt hM (Filter.Eventually.of_forall (fun a => (hm a).2.1))
  · intro b hb
    have hr : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | 0 ≤ (M b).re} :=
      isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous b))
    have hi : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | (M b).im = 0} :=
      isClosed_eq (Complex.continuous_im.comp (WeakDual.eval_continuous b)) continuous_const
    exact (hr.inter hi).mem_of_mapClusterPt hM
      (Filter.Eventually.of_forall (fun a => (hm a).2.2.1 b hb))
  · intro g b
    have hsmall : ∀ ε : ℝ, 0 < ε → ‖M (leftTranslate g b) - M b‖ ≤ ε := by
      intro ε hε
      have hc : IsClosed {M : WeakDual ℂ (G →ᵇ ℂ) | ‖M (leftTranslate g b) - M b‖ ≤ ε} :=
        isClosed_le (((WeakDual.eval_continuous (leftTranslate g b)).sub
        (WeakDual.eval_continuous b)).norm) continuous_const
      apply hc.mem_of_mapClusterPt hM
      obtain ⟨n, hn⟩ := exists_nat_gt (‖b‖ / ε)
      apply Filter.eventually_atTop.mpr
      refine ⟨({g}, n), fun a ha => ?_⟩
      have hg : g ∈ a.1 := ha.1 (Finset.mem_singleton_self g)
      have hna : (n : ℝ) ≤ a.2 := by exact_mod_cast ha.2
      have hpos : (0 : ℝ) < a.2 + 1 := by positivity
      have hbn : ‖b‖ < ε * (n : ℝ) := by
        have := (div_lt_iff₀ hε).mp hn
        nlinarith
      have he : (1 / ((a.2 : ℝ) + 1)) * ‖b‖ ≤ ε := by
        rw [one_div_mul_eq_div]
        apply (div_le_iff₀ hpos).mpr
        nlinarith
      exact ((hm a).2.2.2 g hg b).trans he
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    by_contra hne
    have hp : 0 < ‖M (leftTranslate g b) - M b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have := hsmall (‖M (leftTranslate g b) - M b‖ / 2) (by positivity)
    linarith

end Dixmier

end

end OAI
