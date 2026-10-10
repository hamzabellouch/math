import OAI.Analysis.CircleDomains.Selection.ReversedResidualBounds
import OAI.Analysis.CircleDomains.Modulus.PhysicalLengthCharacterization

namespace OAI

/-! Reversing time preserves the actual physical-domain length. Dyadic
cells are matched with their reversed indices before summing. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem symm_timeClip {a b : PathTime} (hab : a ≤ b) (t : PathTime) :
    unitInterval.symm (timeClip a b t) =
      timeClip (unitInterval.symm b) (unitInterval.symm a) (unitInterval.symm t) := by
  change unitInterval.symm (max a (min b t)) =
    max (unitInterval.symm b) (min (unitInterval.symm a) (unitInterval.symm t))
  rw [unitInterval.strictAnti_symm.antitone.map_max,
    unitInterval.strictAnti_symm.antitone.map_min, min_max_distrib_left,
    min_eq_right (unitInterval.symm_le_symm.mpr hab)]

theorem symm_dyadicLeft (n : ℕ) (i : Fin (2 ^ n)) :
    unitInterval.symm (dyadicLeft n i) = dyadicRight n i.rev := by
  have hs : i.val + (i.rev.val + 1) = 2 ^ n := by
    rw [Fin.val_rev]
    omega
  have hr : (i.val : ℝ) + ((i.rev.val + 1 : ℕ) : ℝ) = (2 : ℝ) ^ n := by
    exact_mod_cast hs
  apply Subtype.ext
  change 1 - (i.val : ℝ) / (2 : ℝ) ^ n = ((i.rev.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
  field_simp
  linarith

theorem symm_dyadicRight (n : ℕ) (i : Fin (2 ^ n)) :
    unitInterval.symm (dyadicRight n i) = dyadicLeft n i.rev := by
  have h := congrArg unitInterval.symm (symm_dyadicLeft n i.rev)
  simpa only [Fin.rev_rev, unitInterval.symm_symm] using h.symm

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem pathsInsideOn_reversed_iff (γ : C(PathTime, X)) (a b : PathTime) :
    reversedPath γ ∈ pathsInsideOn U a b ↔
      γ ∈ pathsInsideOn U (unitInterval.symm b) (unitInterval.symm a) := by
  constructor
  · intro h t ht
    have hs : unitInterval.symm t ∈ Icc a b :=
      ⟨unitInterval.le_symm_comm.mpr ht.2, unitInterval.symm_le_comm.mpr ht.1⟩
    simpa only [reversedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      unitInterval.symm_symm] using h hs
  · intro h t ht
    exact h ⟨unitInterval.symm_le_symm.mpr ht.2, unitInterval.symm_le_symm.mpr ht.1⟩

theorem physicalDyadicPath_reversed (e : G ≃ₜ U) (y₀ : Y)
    (γ : C(PathTime, X)) (n : ℕ) (i : Fin (2 ^ n)) :
    physicalDyadicPath e y₀ n i (reversedPath γ) =
      reversedPath (physicalDyadicPath e y₀ n i.rev γ) := by
  by_cases hnew : reversedPath γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · have hold : γ ∈ pathsInsideOn U (dyadicLeft n i.rev) (dyadicRight n i.rev) := by
      simpa only [symm_dyadicRight, symm_dyadicLeft] using
        (pathsInsideOn_reversed_iff γ _ _).mp hnew
    rw [physicalDyadicPath_of_mem e y₀ n i _ hnew,
      physicalDyadicPath_of_mem e y₀ n i.rev _ hold]
    apply ContinuousMap.ext
    intro t
    change (e.symm ⟨γ (unitInterval.symm (timeClip (dyadicLeft n i) (dyadicRight n i) t)), _⟩).val =
      (e.symm ⟨γ (timeClip (dyadicLeft n i.rev) (dyadicRight n i.rev) (unitInterval.symm t)), _⟩).val
    apply congrArg Subtype.val
    apply congrArg e.symm
    apply Subtype.ext
    apply congrArg γ
    rw [symm_timeClip (dyadicLeft_le_right n i), symm_dyadicRight, symm_dyadicLeft]
  · have hold : γ ∉ pathsInsideOn U (dyadicLeft n i.rev) (dyadicRight n i.rev) := by
      intro h
      apply hnew
      apply (pathsInsideOn_reversed_iff γ _ _).mpr
      simpa only [symm_dyadicRight, symm_dyadicLeft] using h
    simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hnew, dite_eq_right hold]
    rfl

theorem variation_reversedPath {Z : Type*} [MetricSpace Z] (γ : C(PathTime, Z)) :
    eVariationOn (reversedPath γ) univ = eVariationOn γ univ := by
  change eVariationOn (γ ∘ unitInterval.symm) univ = _
  rw [eVariationOn.comp_eq_of_antitoneOn γ unitInterval.symm
    (unitInterval.strictAnti_symm.antitone.antitoneOn _), image_univ,
    unitInterval.symm_bijective.surjective.range_eq]

theorem physicalDomainLength_reversed (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) :
    physicalDomainLength e y₀ (reversedPath γ) = physicalDomainLength e y₀ γ := by
  unfold physicalDomainLength
  congr 1
  funext n
  unfold physicalStageLength physicalDyadicLength
  simp_rw [physicalDyadicPath_reversed, variation_reversedPath]
  exact Equiv.sum_comp (Fin.revPerm (n := 2 ^ n))
    (fun i => eVariationOn (physicalDyadicPath e y₀ n i γ) univ)

end CircleDomainRigidity

end

end OAI
