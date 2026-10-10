import OAI.Combinatorics.BalancedRyser.Profiles.ProfileFiniteScheduledLemmas
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileGridFiniteIdentity
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMarkLimit
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileScheduledMargin

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileSourceMarkLimit

universe u

open ProfileScheduledFiniteComparison ProfileGridDetection
  ProfileScheduledMarks ProfileScheduledMargin ProfileClassMargin

theorem source_limitLowerBound
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A) :
    LimitLowerBound A sourceTest := by
  intro F _ _ _ D C hA hq c P νD νC hlim n r hr
  have hp : ∀ t, IsProfilePair k (D t) (C t) :=
    fun t => hvalid (F t) (D t) (C t) (hA t)
  have hd := dCutoff_le_liminf_actual_grid k hk D C hp hq hlim n
  have hc := cCutoff_le_liminf_actual_grid k D C hp hq hlim n
  have herr := ProfileMarkedError.bound_tendsto_zero k (threshold n)
    (threshold_pos n) (fun t => Fintype.card (F t)) hq
  have hfinite := eventually_finiteDetection_of_profileClass k hk A hvalid hgap
    D C hA hq (threshold n) (threshold n) (threshold_pos n)
  have hcompare : ∀ᶠ t in atTop,
      dGridCutoffMass (D t) (C t) n + cGridCutoffMass (D t) (C t) n ≤
        sourceTest n (F t) (D t) (C t) +
          32 * (2 * (k : ℝ) + 1)^2 /
            ((Fintype.card (F t) : ℝ) * (threshold n)^2) := by
    filter_upwards [hfinite] with t ht
    simpa only [dGridCutoffMass_eq_dFinite, cGridCutoffMass_eq_cFinite,
      sourceTest, threshold] using ht
  exact ProfileMarkLimit.eventually_lt_of_detection_liminfs
    (Eventually.of_forall fun t => dGridCutoffMass_nonneg (D t) (C t) n)
    (Eventually.of_forall fun t => cGridCutoffMass_nonneg (D t) (C t) n)
    hd hc herr hcompare hr

theorem exists_source_mean_margin
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        (C.card : ℝ) + ξ * (Fintype.card F : ℝ) ≤
          𝔼 p : ConditionalOrderVariance.OrderPair D C,
            (sourceMarkCount D C (threshold n) (threshold n) p : ℝ) :=
  ProfileScheduledMargin.exists_source_mean_margin k A hvalid hgap hvisible
    (source_limitLowerBound k hk A hvalid hgap)

theorem exists_uniform_positive_tail
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    (hvisible : ProfileVisibleExcess A) :
    ∃ n : ℕ, ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
        (D C : Finset (Line F)), A F D C → N ≤ Fintype.card F →
        ξ / (4 * (k : ℝ)) ≤
          tailProbability D C (threshold n) (threshold n) ξ :=
  ProfileScheduledMargin.exists_uniform_positive_tail k hk A hvalid hgap hvisible
    (source_limitLowerBound k hk A hvalid hgap)

end Balanced.ProfileSourceMarkLimit

end

end OAI
