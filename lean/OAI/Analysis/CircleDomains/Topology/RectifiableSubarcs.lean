import OAI.Analysis.CircleDomains.Modulus.ReversedArclength
import OAI.Analysis.CircleDomains.Selection.LastEntryCuts
import OAI.Analysis.CircleDomains.Modulus.SmallWeightedArcs

namespace OAI

/-! Actual short rectifiable arcs between nearby parameters of a
finite-cost curve, with either orientation. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem pathOccupation_affine (γ : RectifiablePath X) {a b : PathTime} (hab : a < b) :
    pathOccupation (affineRectifiablePath γ hab) =
      ((pathLengthMeasure γ).restrict (Icc a b)).map γ.val := by
  rw [pathOccupation, pathLengthMeasure_affine]
  change (((pathLengthMeasure γ).restrict (Icc a b)).map (rescalePathTime a b)).map
    (affineRestrictedPath a b γ.val) = _
  rw [Measure.map_map (affineRestrictedPath a b γ.val).continuous.measurable
    (rescalePathTime a b).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change γ.val (affinePathTime a b (rescalePathTime a b t)) = γ.val t
  rw [affine_rescalePathTime hab ht]

theorem pathCost_affine (γ : RectifiablePath X) {a b : PathTime} (hab : a < b)
    (g : X → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g x ∂pathOccupation (affineRectifiablePath γ hab)) =
      ∫⁻ t in Icc a b, g (γ.val t) ∂pathLengthMeasure γ := by
  rw [pathOccupation_affine γ hab]
  exact lintegral_map hg γ.val.continuous.measurable

def constantRectifiablePath (x : X) : RectifiablePath X :=
  ⟨ContinuousMap.const PathTime x, by
    change eVariationOn _ _ ≠ ∞
    have hz : eVariationOn (ContinuousMap.const PathTime x) univ = 0 :=
      (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _
    rw [hz]
    exact ENNReal.zero_ne_top⟩

theorem pathOccupation_constant (x : X) : pathOccupation (constantRectifiablePath x) = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [pathOccupation_univ]
  exact (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _

theorem exists_rectifiable_subarc (γ : RectifiablePath X) (a b : PathTime)
    (g : X → ℝ≥0∞) (hg : Measurable g) :
    ∃ ρ : RectifiablePath X, ρ.val ⊥ = γ.val a ∧ ρ.val ⊤ = γ.val b ∧
      range ρ.val ⊆ γ.val '' Icc (min a b) (max a b) ∧
      (∫⁻ x, g x ∂pathOccupation ρ) =
        ∫⁻ t in Icc (min a b) (max a b), g (γ.val t) ∂pathLengthMeasure γ := by
  have hforward {s t : PathTime} (hst : s < t) :
      ∃ ρ : RectifiablePath X, ρ.val ⊥ = γ.val s ∧ ρ.val ⊤ = γ.val t ∧
        range ρ.val ⊆ γ.val '' Icc s t ∧
        (∫⁻ x, g x ∂pathOccupation ρ) =
          ∫⁻ u in Icc s t, g (γ.val u) ∂pathLengthMeasure γ := by
    refine ⟨affineRectifiablePath γ hst, ?_, ?_, ?_, pathCost_affine γ hst g hg⟩
    · exact congrArg γ.val (affinePathTime_zero s t)
    · exact congrArg γ.val (affinePathTime_one s t)
    · rintro x ⟨u, rfl⟩
      exact ⟨affinePathTime s t u, affinePathTime_mem_Icc hst.le u, rfl⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · simpa only [min_eq_left hab.le, max_eq_right hab.le] using hforward hab
  · refine ⟨constantRectifiablePath (γ.val a), rfl, rfl, ?_, ?_⟩
    · rintro x ⟨u, rfl⟩
      exact ⟨a, by simp, rfl⟩
    · simp only [pathOccupation_constant, lintegral_zero_measure, min_self, max_self, Icc_self,
        Measure.restrict_singleton, measure_singleton, zero_smul]
  · obtain ⟨ρ, hρ0, hρ1, hρrange, hρcost⟩ := hforward hba
    refine ⟨reversedRectifiablePath ρ, ?_, ?_, ?_, ?_⟩
    · exact (reversedPath_zero ρ.val).trans hρ1
    · exact (reversedPath_one ρ.val).trans hρ0
    · rintro x ⟨u, rfl⟩
      change ρ.val (unitInterval.symm u) ∈ γ.val '' Icc (min a b) (max a b)
      simpa only [min_eq_right hba.le, max_eq_left hba.le] using
        hρrange (mem_range_self (unitInterval.symm u))
    · simpa only [pathOccupation_reversed, min_eq_right hba.le, max_eq_left hba.le] using hρcost

theorem exists_small_rectifiable_subarcs (γ : RectifiablePath X) (g : X → ℝ≥0∞)
    (hg : Measurable g) (hfinite : (∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ) < ∞)
    (r : PathTime) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : PathTime, dist a r < δ → dist b r < δ →
      ∃ ρ : RectifiablePath X, ρ.val ⊥ = γ.val a ∧ ρ.val ⊤ = γ.val b ∧
        range ρ.val ⊆ range γ.val ∧ (∫⁻ x, g x ∂pathOccupation ρ) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_weighted_arcs γ g hfinite r hε
  refine ⟨δ, hδ, fun a b ha hb => ?_⟩
  obtain ⟨ρ, hρa, hρb, hρrange, hρcost⟩ := exists_rectifiable_subarc γ a b g hg
  refine ⟨ρ, hρa, hρb, hρrange.trans (image_subset_range _ _), ?_⟩
  rw [hρcost]
  exact hsmall a b ha hb

end CircleDomainRigidity

end

end OAI
