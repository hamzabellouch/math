import OAI.Analysis.CircleDomains.Topology.AffineClippedIntervals
import OAI.Analysis.CircleDomains.Modulus.CountableConcatenationLength

namespace OAI

/-! Local physical arclength of a glued path is charged to the original
piece, without assuming in advance that the glued path is rectifiable. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalSubpath_piece_length (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (η : C(PathTime, X))
    {a b : PathTime} (hab : a < b)
    (hmatch : ∀ s, η (affinePathTime a b s) = γ.val s)
    {c d : PathTime} (hcd : c ≤ d) (hη : η ∈ pathsInsideOn U c d) :
    eVariationOn (physicalSubpath e hcd ⟨η, hη⟩) (Icc a b) ≤
      physicalTimeLength e y₀ γ (Icc (rescalePathTime a b c) (rescalePathTime a b d)) := by
  by_cases hi : (Icc c d ∩ Icc a b).Nonempty
  · obtain ⟨t, ht, htab⟩ := hi
    have hc : c ≤ b := ht.1.trans htab.2
    have hd : a ≤ d := htab.1.trans ht.2
    have hκ := rescalePathTime_monotone hab hcd
    have hγ : γ.val ∈ pathsInsideOn U (rescalePathTime a b c) (rescalePathTime a b d) := by
      intro s hs
      rw [← hmatch]
      apply hη
      constructor
      · have hh := (affinePathTime_strictMono hab).monotone hs.1
        rw [affine_rescale_eq_clip hab] at hh
        have hlo : c ≤ timeClip a b c := by
          change c ≤ max a (min b c)
          rw [min_eq_right hc]
          exact le_max_right _ _
        exact hlo.trans hh
      · have hh := (affinePathTime_strictMono hab).monotone hs.2
        rw [affine_rescale_eq_clip hab] at hh
        exact hh.trans (max_le hd (min_le_right _ _))
    have heq : (physicalSubpath e hcd ⟨η, hη⟩).comp (affinePathTime a b) =
        physicalSubpath e hκ ⟨γ.val, hγ⟩ := by
      apply ContinuousMap.ext
      intro s
      apply congrArg Subtype.val
      apply congrArg e.symm
      apply Subtype.ext
      change η (timeClip c d (affinePathTime a b s)) =
        γ.val (timeClip (rescalePathTime a b c) (rescalePathTime a b d) s)
      rw [← hmatch, affine_clip_rescaled hab hc hd]
    have hv := eVariationOn.comp_eq_of_monotoneOn
      (physicalSubpath e hcd ⟨η, hη⟩) (affinePathTime a b)
      ((affinePathTime_strictMono hab).monotone.monotoneOn univ)
    rw [image_univ, range_affinePathTime hab] at hv
    have hv' : eVariationOn ((physicalSubpath e hcd ⟨η, hη⟩).comp
        (affinePathTime a b)) univ = eVariationOn (physicalSubpath e hcd ⟨η, hη⟩) (Icc a b) := hv
    rw [← hv', heq, ← physicalTimeLength_compact_mass e hU y₀ γ hκ hγ]
  · have hconst := timeClip_eq_const_of_disjoint hcd hab.le hi
    have hz : eVariationOn (physicalSubpath e hcd ⟨η, hη⟩) (Icc a b) = 0 := by
      apply (eVariationOn.eq_zero_iff _).mpr
      intro s hs t ht
      have hst : timeClip c d s = timeClip c d t := by
        rcases hconst with hconst | hconst <;> exact (hconst hs).trans (hconst ht).symm
      have heq : physicalSubpath e hcd ⟨η, hη⟩ s = physicalSubpath e hcd ⟨η, hη⟩ t := by
        apply congrArg Subtype.val
        apply congrArg e.symm
        exact Subtype.ext (congrArg η hst)
      rw [heq, edist_self]
    rw [hz]
    exact bot_le

end CircleDomainRigidity

end

end OAI
