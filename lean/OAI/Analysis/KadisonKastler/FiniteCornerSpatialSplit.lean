import OAI.Analysis.KadisonKastler.FiniteCommutantSpatialSplit
import OAI.Analysis.KadisonKastler.ReducingSpatialLift
import OAI.Analysis.KadisonKastler.GeneralCornerFactor
import OAI.Analysis.KadisonKastler.SpatialProjectionPinching

namespace OAI

/-! # Spatial splitting from one nonzero finite commutant corner -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem exists_selfAdjoint_split_of_reducing_finite_corner
    (M : VonNeumannAlgebra H) (hN : ScalarCenter M.commutant)
    (hE : E.starProjection ∈ M.commutant) (hE0 : E.starProjection ≠ 0)
    (hfinite : FiniteProjectionIn M.commutant ⟨E.starProjection, hE⟩)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (hTE : E.starProjection * T = T * E.starProjection) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  let φ := commutantReducingHom E M hE
  let R := generatedVonNeumannAlgebra φ.range
  have hi : Function.Injective φ := commutantReducingHom_injective E M hE hE0 hN
  let e : Algebra M ≃⋆ₐ[ℂ] Algebra R := boundedWeakNormalEquiv M φ hi
    (commutantReducingHom_boundedWeakNormal E M hE)
  have he (a : Algebra M) : (e a).val = cornerCompression E a.val := rfl
  have hRT := reducing_spatial_preserves E M hE R e he T hTE hT
  have hR : ScalarCenter R.commutant := by
    rw [commutant_reducingClosure E M hE]
    exact scalarCenter_representedCorner_general E M.commutant hE hN
  have hRf : FiniteProjectionIn R.commutant 1 := by
    rw [commutant_reducingClosure E M hE]
    intro v hv _
    exact finite_representedCorner_of_finite_projection M.commutant hE hfinite v hv
  let : Nontrivial E := by
    have hn := representedCorner_nonzero_of_projection_ne_zero hE0
    by_contra h
    have : Subsingleton E := not_nontrivial_iff_subsingleton.mp h
    exact hn (Subsingleton.elim _ _)
  have hT0 : IsSelfAdjoint (cornerCompression E T) := by
    change star (cornerCompression E T) = cornerCompression E T
    rw [← cornerCompression_star, hTsa.star_eq]
  obtain ⟨c, hc, hcsa, hcn, hTc⟩ :=
    exists_selfAdjoint_split_of_finite_factor_commutant R hR hRf
      (cornerCompression E T) hT0 hRT
  obtain ⟨a, ha, hasa, han, hTa⟩ :=
    lift_reducing_spatial_split E M hE R e he T hTE hT c hc hcsa hTc
  exact ⟨a, ha, hasa, han.le.trans (hcn.trans (norm_cornerCompression_le E T)), hTa⟩

theorem exists_selfAdjoint_split_of_finite_commutant_corner
    (M : VonNeumannAlgebra H) (hN : ScalarCenter M.commutant)
    (hE : E.starProjection ∈ M.commutant) (hE0 : E.starProjection ≠ 0)
    (hfinite : FiniteProjectionIn M.commutant ⟨E.starProjection, hE⟩)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  obtain ⟨S, hSsa, hSn, hST, hSE⟩ := exists_projection_reducing_implementer M T hTsa hT
    E.starProjection (isStarProjection_starProjection (U := E)) hE
  have hS : ∀ a ∈ M, S * a - a * S ∈ M := by
    intro a ha
    have hc := VonNeumannAlgebra.mem_commutant_iff.mp hST a ha
    have he : S * a - a * S = T * a - a * T := by
      change a * (S - T) = (S - T) * a at hc
      rw [mul_sub, sub_mul] at hc
      simpa only [neg_sub] using congrArg Neg.neg (sub_eq_sub_iff_sub_eq_sub.mp hc)
    rw [he]
    exact hT a ha
  obtain ⟨a, ha, hasa, han, hSa⟩ :=
    exists_selfAdjoint_split_of_reducing_finite_corner E M hN hE hE0 hfinite S hSsa hS hSE.eq
  refine ⟨a, ha, hasa, han.trans hSn, ?_⟩
  have he : T - a = (S - a) - (S - T) := by abel
  rw [he]
  exact M.commutant.sub_mem hSa hST

end

end KadisonKastler

end OAI
