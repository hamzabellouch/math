import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.ActualBandInverseBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.OwnProbabilityRareCapBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

lemma originalQueryDensity_info_measurable {N K : ℕ} (F : fermionGraph N)
    (r : ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr₀ : 0 < r₀)
    (hs : 0 < s) (y : Space) :
    Measurable[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j]
      (fun z => originalQueryDensity F r j c₁ r₀ s z y) := by
  exact (jointMasterPosterior_measurable (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) j hc hr₀ hs
    canonicalRealPacket_smooth.continuous).comp (measurable_id.prodMk measurable_const)

lemma original_inverse_failure_info_measurable {N K : ℕ} (F : fermionGraph N)
    (Z lam r₀ s c₁ h xi : ℝ) (j : Fin K) (y : Space)
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) :
    MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r₀ k) j]
      (originalLowFailure F Z lam r₀ s c₁ h xi j y ∪
        originalHighFailure F Z lam r₀ s c₁ h xi j y) := by
  have hf := originalQueryField_info_measurable (K := K) F Z lam r₀ j hc hr₀ hs y
  have hd := originalQueryDensity_info_measurable (K := K) F r₀ j hc hr₀ hs y
  exact ((measurableSet_le measurable_const hf).inter (measurableSet_le hd measurable_const)).union
    ((measurableSet_le hf measurable_const).inter (measurableSet_le measurable_const hd))

lemma original_inverse_height_net_union_bound {N K : ℕ} {F : fermionGraph N}
    {Z lam r₀ s c₁ xi : ℝ} {j : Fin K} (Q : Finset Space) (H : Finset ℝ)
    (hQ : ∀ h ∈ H, ∀ y ∈ Q, OriginalPointInverseBounds F Z lam r₀ s c₁ h xi j y) :
    (physicalObservationLaw (graphRawLaw F) K).real
      (⋃ h ∈ H, ⋃ y ∈ Q, originalLowFailure F Z lam r₀ s c₁ h xi j y ∪
        originalHighFailure F Z lam r₀ s c₁ h xi j y) ≤
      4*(H.card:ℝ)*(Q.card:ℝ)*((2:ℝ)^j.val*r₀)^40 := by
  apply (measureReal_biUnion_finset_le H _).trans
  calc
    _ ≤ ∑ _h ∈ H, 4*(Q.card:ℝ)*((2:ℝ)^j.val*r₀)^40 := by
      exact Finset.sum_le_sum (fun h hh => original_inverse_net_union_bound Q (hQ h hh))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

lemma exists_inverse_band_spatial_net {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    ∃ Q : Finset Space,
      (∀ x ∈ Q, 11*u/8 ≤ ‖x‖ ∧ ‖x‖ ≤ 13*u/8) ∧
      (∀ y : Space, 11*u/8 ≤ ‖y‖ → ‖y‖ ≤ 13*u/8 →
        ∃ x ∈ Q, ‖x-y‖ ≤ u^2) ∧
      (Q.card:ℝ) ≤ 4913/u^3 := by
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_spatial_grid_net
    (A := {x : Space | 11*u/8 ≤ ‖x‖ ∧ ‖x‖ ≤ 13*u/8})
    (R := 2*u) (h := u^2/3) (by positivity) (by positivity)
    (fun _ hx => by linarith [hx.2])
  refine ⟨Q,hQ,?_,hcard.trans ?_⟩
  · intro y hyl hyh
    obtain ⟨x,hx,hxy⟩ := hcover y ⟨hyl,hyh⟩
    refine ⟨x,hx,?_⟩
    rw [norm_sub_rev] at hxy
    nlinarith
  · have hlin : 2*(2*u/(u^2/3))+5 ≤ 17/u := by
      apply (le_div_iff₀ hu).mpr
      field_simp
      nlinarith
    calc _ ≤ (17/u)^3 := pow_le_pow_left₀ (by positivity) hlin 3
         _ = _ := by ring

lemma divided_net_field_variation {a b alpha beta t : ℝ}
    (ht : 1 ≤ t) (ha : 0 ≤ alpha) (hv : |b-a| ≤ alpha+beta*max (-a) 0) :
    |b/t-a/t| ≤ alpha+beta*max (-(a/t)) 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hm : max (-(a/t)) 0 = max (-a) 0/t := by
    simpa only [neg_div,zero_div] using max_div_div_right ht0.le (-a) 0
  rw [←sub_div,abs_div,abs_of_pos ht0,hm]
  calc
    _ ≤ (alpha+beta*max (-a) 0)/t := div_le_div_of_nonneg_right hv ht0.le
    _ = alpha/t+beta*(max (-a) 0/t) := by ring
    _ ≤ _ := add_le_add (div_le_self ha ht) le_rfl

lemma localCellRadius_normalized {y : Space} (p : ℕ) (a : ℝ) :
    (localCellRadius y)^p*a = (‖y‖^p*a)/(100000:ℝ)^p := by
  simp only [localCellRadius,div_pow]
  ring

end CoulombAtom

end

end OAI
