import OAI.Geometry.SurfaceImmersion.Geometry.CompactLocalBounds
import OAI.Geometry.Immersion.ClosedSurface.ModeBounds

namespace OAI

/-! Actual reconstruction coefficients have finite bounds on compactly
contained good-mode domains, uniformly over slow scales at most one. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SmallModes
open WeightedEstimates

theorem ModeDomain.compact_reconstruction_bounds {G : Field 4} {Ω V K : Set Base}
    (h : ModeDomain G Ω) (hV : IsOpen V) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      ReconstructionCoefficientBound G V s m C := by
  let S : Base → Fin 8 → ℂ := fun x =>
    ![ClosedSurfaceR4.SmallModes.connectionX G dx dx x, ClosedSurfaceR4.SmallModes.connectionY G dx dx x,
      ClosedSurfaceR4.SmallModes.connectionX G dx dy x, ClosedSurfaceR4.SmallModes.connectionY G dx dy x,
      ClosedSurfaceR4.SmallModes.connectionX G dy dy x, ClosedSurfaceR4.SmallModes.connectionY G dy dy x,
      ClosedSurfaceR4.SmallModes.secondRatio G dx dx x, ClosedSurfaceR4.SmallModes.secondRatio G dx dy x]
  let T : Base → Fin 5 → Ambient 4 := fun x =>
    ![ClosedSurfaceR4.SmallModes.secondForm G dx dx x, ClosedSurfaceR4.SmallModes.secondForm G dx dy x,
      ClosedSurfaceR4.SmallModes.tangentDualX G x, ClosedSurfaceR4.SmallModes.tangentDualY G x, ClosedSurfaceR4.SmallModes.normalDual G x]
  have hS : ContDiffOn ℝ ∞ S Ω := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact h.connectionX dx dx
    · exact h.connectionY dx dx
    · exact h.connectionX dx dy
    · exact h.connectionY dx dy
    · exact h.connectionX dy dy
    · exact h.connectionY dy dy
    · exact h.secondRatio dx dx
    · exact h.secondRatio dx dy
  have hT : ContDiffOn ℝ ∞ T Ω := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact h.secondForm dx dx
    · exact h.secondForm dx dy
    · exact h.tangentDualX
    · exact h.tangentDualY
    · exact h.normalDual
  obtain ⟨B,hB,hb⟩ := compact_local_weighted_bound hV h.isOpen hK hVK hKΩ hS m
  obtain ⟨D,hD,hd⟩ := compact_local_weighted_bound hV h.isOpen hK hVK hKΩ hT m
  refine ⟨max B D, hB.trans (le_max_left _ _),?_⟩
  intro s hs hs1
  have hnonneg : 0 ≤ max B D := zero_le_one.trans (hB.trans (le_max_left _ _))
  have hb' := (hb s hs.le hs1).mono_const (le_max_left B D)
  have hd' := (hd s hs.le hs1).mono_const (le_max_right B D)
  have hscalar (i : Fin 8) := hb'.component hV.uniqueDiffOn hs.le hnonneg
    (hS.mono (hVK.trans hKΩ)) i
  have hvector (i : Fin 5) := hd'.component hV.uniqueDiffOn hs.le hnonneg
    (hT.mono (hVK.trans hKΩ)) i
  exact ⟨⟨⟨hscalar 0,hscalar 1,hscalar 2,hscalar 3,hscalar 4,hscalar 5,hscalar 6,hscalar 7⟩,
    hvector 0,hvector 1⟩,hvector 2,hvector 3,hvector 4⟩

end ClosedSurfaceR4.SmallModes

end

end OAI
