import OAI.Analysis.CircleDomains.Selection.AffineTagRestriction
import OAI.Analysis.CircleDomains.Probability.MonotoneDyadicMass
import OAI.Analysis.CircleDomains.Modulus.PhysicalLengthCharacterization
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! An affine restriction has at most the original physical-domain length.
The estimate uses the actual inverse quotient and its arclength measure. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem affinePathTime_clip {a b : PathTime} (hab : a < b) (c d t : PathTime) :
    affinePathTime a b (timeClip c d t) =
      timeClip (affinePathTime a b c) (affinePathTime a b d) (affinePathTime a b t) := by
  change affinePathTime a b (max c (min d t)) =
    max (affinePathTime a b c) (min (affinePathTime a b d) (affinePathTime a b t))
  rw [(affinePathTime_strictMono hab).monotone.map_max,
    (affinePathTime_strictMono hab).monotone.map_min]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem pathsInsideOn_affine_image {a b : PathTime} (hab : a < b)
    (γ : C(PathTime, X)) {c d : PathTime}
    (hγ : affineRestrictedPath a b γ ∈ pathsInsideOn U c d) :
    γ ∈ pathsInsideOn U (affinePathTime a b c) (affinePathTime a b d) := by
  intro t ht
  have he := (affinePathTime a b).continuous.image_Icc_of_strictMono
    (affinePathTime_strictMono hab) (a := c) (b := d)
  rw [← he] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact hγ hs

theorem physicalSubpath_affine (e : G ≃ₜ U) {a b : PathTime} (hab : a < b)
    (γ : C(PathTime, X)) {c d : PathTime} (hcd : c ≤ d)
    (hγ : affineRestrictedPath a b γ ∈ pathsInsideOn U c d) :
    physicalSubpath e hcd ⟨affineRestrictedPath a b γ, hγ⟩ =
      (physicalSubpath e ((affinePathTime_strictMono hab).monotone hcd)
        ⟨γ, pathsInsideOn_affine_image hab γ hγ⟩).comp (affinePathTime a b) := by
  apply ContinuousMap.ext
  intro t
  change (e.symm ⟨γ (affinePathTime a b (timeClip c d t)), _⟩).val =
    (e.symm ⟨γ (timeClip (affinePathTime a b c) (affinePathTime a b d)
      (affinePathTime a b t)), _⟩).val
  apply congrArg Subtype.val
  apply congrArg e.symm
  apply Subtype.ext
  exact congrArg γ (affinePathTime_clip hab c d t)

theorem physicalSubpath_affine_length_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    {c d : PathTime} (hcd : c ≤ d)
    (hγ : affineRestrictedPath a b γ.val ∈ pathsInsideOn U c d) :
    eVariationOn (physicalSubpath e hcd ⟨affineRestrictedPath a b γ.val, hγ⟩) univ ≤
      physicalTimeLength e y₀ γ (Icc (affinePathTime a b c) (affinePathTime a b d)) := by
  rw [physicalSubpath_affine e hab γ.val hcd hγ,
    physicalTimeLength_compact_mass e hU y₀ γ ((affinePathTime_strictMono hab).monotone hcd)
      (pathsInsideOn_affine_image hab γ.val hγ)]
  exact eVariationOn.comp_le_of_monotoneOn
    (physicalSubpath e ((affinePathTime_strictMono hab).monotone hcd)
      ⟨γ.val, pathsInsideOn_affine_image hab γ.val hγ⟩) (affinePathTime a b)
    ((affinePathTime_strictMono hab).monotone.monotoneOn _) (fun _ _ => mem_univ _)

theorem physicalDyadicLength_affine_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    (n : ℕ) (i : Fin (2 ^ n)) :
    physicalDyadicLength e y₀ n i (affineRestrictedPath a b γ.val) ≤
      physicalTimeLength e y₀ γ
        (Icc (affinePathTime a b (dyadicLeft n i)) (affinePathTime a b (dyadicRight n i))) := by
  by_cases hi : affineRestrictedPath a b γ.val ∈
      pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · rw [physicalDyadicLength, physicalDyadicPath_of_mem e y₀ n i _ hi]
    exact physicalSubpath_affine_length_le e hU y₀ γ hab (dyadicLeft_le_right n i) hi
  · simp only [physicalDyadicLength, physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hi]
    have hz : eVariationOn (ContinuousMap.const PathTime y₀) univ = 0 :=
      (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _
    rw [hz]
    exact bot_le

theorem physicalDomainLength_affine_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    physicalDomainLength e y₀ (affineRestrictedPath a b γ.val) ≤
      physicalTimeLength e y₀ γ (Icc a b) := by
  apply iSup_le
  intro n
  calc
    physicalStageLength e y₀ n (affineRestrictedPath a b γ.val) ≤
        ∑ i : Fin (2 ^ n), physicalTimeLength e y₀ γ
          (Icc (affinePathTime a b (dyadicLeft n i)) (affinePathTime a b (dyadicRight n i))) :=
      Finset.sum_le_sum fun i _ => physicalDyadicLength_affine_le e hU y₀ γ hab n i
    _ = _ := by rw [sum_monotone_dyadic_mass _ _ (affinePathTime_strictMono hab).monotone,
      affinePathTime_zero, affinePathTime_one]

theorem physicalDomainLength_affine_finite (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b) :
    physicalDomainLength e y₀ (affineRestrictedPath a b γ.val) < ∞ :=
  (physicalDomainLength_affine_le e hU y₀ γ hab).trans_lt
    ((measure_mono (subset_univ _)).trans_lt (measure_lt_top _ _))

end CircleDomainRigidity

end

end OAI
