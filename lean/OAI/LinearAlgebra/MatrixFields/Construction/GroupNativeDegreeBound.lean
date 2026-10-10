import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.GroupProjectedEntropy

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupNativeDegreeBound

open AllFieldHistory AllFieldActiveLaws AllFieldActiveCapacity
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupCountRate AllFieldGroupPairWindows AllFieldGroupPairEntropy
open AllFieldGroupProjectedEntropy JointCompatibilityRateLimit
open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def maxNativeDegree (allocation : Allocation) (sigma : Placement) : ℝ :=
  max (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)
    (max (orderNativeDegree (K := K) (tick := tick) allocation sigma 1)
      (orderNativeDegree (K := K) (tick := tick) allocation sigma 2))

theorem orderNativeDegree_le_max (allocation : Allocation) (sigma : Placement) (side : Fin 3) :
    orderNativeDegree (K := K) (tick := tick) allocation sigma side ≤
      maxNativeDegree (K := K) (tick := tick) allocation sigma := by
  fin_cases side
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem nativeCompatibilityRate_eq (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (hside : side ≠ 0) :
    nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side =
      orderNativeDegree (K := K) (tick := tick) allocation sigma side := by
  have hp := projected_native_entropy_eq (K := K) (tick := tick) allocation sigma side hside
  have hb := baseEntropy_sub_pairReferenceEntropy (K := K) (tick := tick) allocation sigma side
  unfold nativeCompatibilityRate compatibilityRate
  rw [show ∀ a b c d : ℝ, a - b + c + d = (a - b) + (c + d) by intros; ring,
    hb, hp, ← Finset.sum_add_distrib]
  unfold orderNativeDegree
  apply Finset.sum_congr rfl
  intro h _
  have hs : (parentBase allocation h : ℝ) =
      (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h :=
    population_cast_real allocation 1 (h.val.val.1.source, h.val.val.2)
  rw [hs]
  ring

theorem exists_threshold_eventually_counts_le (allocation : Allocation) (sigma : Placement)
    {δ widthMax : ℝ} (hδ : 0 < δ) (hwidthMax : 0 < widthMax) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
      ∀ width : ℝ, 0 < width → width ≤ threshold →
        ∀ᶠ m : ℕ in atTop,
          (∀ e : Targets (K := K) (tick := tick) allocation m sigma,
            (((data allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
              Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ))) ∧
          (∀ (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma),
            o ∈ (data allocation m width sigma).orbits e →
            ∀ v : Variable (K := K) (tick := tick) allocation m sigma,
              v ∈ (data allocation m width sigma).passing e o →
              (((data allocation m width sigma).competitors e o v).card : ℝ) ≤
                Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ))) := by
  obtain ⟨t₁, ht₁, ht₁Max, h₁⟩ :=
    exists_threshold_eventually_competitors_le (K := K) (tick := tick)
      allocation sigma 1 hδ hwidthMax
  obtain ⟨t₂, ht₂, _, h₂⟩ :=
    exists_threshold_eventually_competitors_le (K := K) (tick := tick)
      allocation sigma 2 hδ hwidthMax
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, (min_le_left _ _).trans ht₁Max, ?_⟩
  intro width hw hwt
  filter_upwards [eventually_eligibility_card_le (K := K) (tick := tick)
    allocation sigma width hδ,
    h₁ width hw (hwt.trans (min_le_left _ _)),
    h₂ width hw (hwt.trans (min_le_right _ _))] with m hm₀ hm₁ hm₂
  have hm (side : Fin 3) :
      Real.exp ((m : ℝ) * (orderNativeDegree (K := K) (tick := tick) allocation sigma side + δ)) ≤
        Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (add_le_add (orderNativeDegree_le_max (K := K) (tick := tick) allocation sigma side) le_rfl) (Nat.cast_nonneg m))
  refine ⟨fun e => (hm₀ e).trans (hm 0), ?_⟩
  intro e o ho v hv
  rcases v with ⟨side, w⟩
  fin_cases side
  · exact (Nat.cast_le.mpr (Finset.card_le_card
      (competitors_subset_eligibility_of_first allocation m width sigma e o (0, w) rfl))).trans
        ((hm₀ e).trans (hm 0))
  · have hh := hm₁ e o ho w hv
    rw [nativeCompatibilityRate_eq (K := K) (tick := tick) allocation sigma 1 (by decide)] at hh
    exact hh.trans (hm 1)
  · have hh := hm₂ e o ho w hv
    rw [nativeCompatibilityRate_eq (K := K) (tick := tick) allocation sigma 2 (by decide)] at hh
    exact hh.trans (hm 2)

end MatrixMultiplication.AllFieldGroupNativeDegreeBound

end
end

end MatrixAllFields

end OAI
