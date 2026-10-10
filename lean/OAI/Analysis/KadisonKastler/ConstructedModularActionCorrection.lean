import OAI.Analysis.KadisonKastler.ConstructedNormalizerCorrection
import OAI.Analysis.KadisonKastler.NormalizingRepresentations
import OAI.Analysis.KadisonKastler.InvariantOperatorMean

namespace OAI

/-! # A common action from nearby normalizers

Pointwise selected normalizers need no continuity or measurability. Their
multiplicative error is corrected in the closed normalizer group, then a
single polar intertwiner gives the change of position. This is the final
part of the manuscript's modular-alignment argument.
-/

namespace KadisonKastler

open scoped BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

local instance constructedActionCorrectionCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

/-- An arbitrary unitary family uniformly close to a representation has
multiplication error at most three times that displacement. -/
theorem constructed_cocycleDefect_le_of_close_representation
    (U : G →* unitary (H →L[ℂ] H)) (v : G → unitary (H →L[ℂ] H))
    {d : ℝ} (hd : 0 ≤ d)
    (hclose : ∀ g, ‖(v g : H →L[ℂ] H) - (U g : H →L[ℂ] H)‖ ≤ d) :
    unitaryCocycleDefect 1 (boundedUnitaryFamily v) ≤ 3 * d := by
  have hzero : unitaryCocycleError 1 (boundedUnitaryFamily U) = 0 := by
    apply BoundedContinuousFunction.ext
    rintro ⟨g, k⟩
    change (U g : H →L[ℂ] H) * (U k : H →L[ℂ] H) - (U (g * k) : H →L[ℂ] H) = 0
    rw [map_mul, Submonoid.coe_mul, sub_self]
  have hnorm : ‖(boundedUnitaryFamily v).val - (boundedUnitaryFamily U).val‖ ≤ d :=
    (BoundedContinuousFunction.norm_le hd).mpr hclose
  have h := (unitaryCocycleError_lipschitz
    (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)))).dist_le_mul
    (boundedUnitaryFamily v) (boundedUnitaryFamily U)
  rw [hzero, dist_zero_right, Subtype.dist_eq, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))

/-- The given action normalizes a single nearby conjugate algebra after
correcting the arbitrary pointwise choices of nearby normalizers. -/
theorem constructed_exists_common_action_of_near_normalizers
    (P : VonNeumannAlgebra H) (hpub : SmallNormalizerFactorization P)
    (m : ScalarInvariantMean G)
    (U : G →* unitary (H →L[ℂ] H)) (v : G → unitary (H →L[ℂ] H))
    (hv : ∀ g, Conjugates (v g) P P)
    {d : ℝ} (hd : 0 ≤ d) (hsmall : 3 * d ≤ 1 / 16384)
    (hclose : ∀ g, ‖(v g : H →L[ℂ] H) - (U g : H →L[ℂ] H)‖ ≤ d) :
    ∃ q : unitary (H →L[ℂ] H), ‖(q : H →L[ℂ] H) - 1‖ ≤ 3074 * d ∧
      ∀ g, Conjugates (U g) (unitaryConjugateAlgebra q P)
        (unitaryConjugateAlgebra q P) := by
  have hdef := constructed_cocycleDefect_le_of_close_representation U v hd hclose
  obtain ⟨z, hz, hznorm⟩ := constructed_exists_normalizing_representation P hpub m.bimoduleMean
    m.bimoduleMean_trivial_equivariant (fun Q F hF => m.operatorMean_mem Q F hF)
    (boundedUnitaryFamily v) hv (hdef.trans hsmall)
  have hzU (g : G) : ‖(z g : H →L[ℂ] H) - (U g : H →L[ℂ] H)‖ ≤ 1537 * d := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (z g : H →L[ℂ] H)
      (v g : H →L[ℂ] H) (U g : H →L[ℂ] H)
    have hzv := hznorm g
    have hvU := hclose g
    change ‖(z g : H →L[ℂ] H) - (v g : H →L[ℂ] H)‖ ≤ _ at hzv
    linarith
  obtain ⟨q, hq, hact⟩ := exists_near_conjugated_normalizing_action P U z hz
    m.bimoduleMean m.bimoduleMean_trivial_equivariant (by linarith : 1537 * d < 1) hzU
  exact ⟨q, by linarith, hact⟩

end

end KadisonKastler

end OAI
