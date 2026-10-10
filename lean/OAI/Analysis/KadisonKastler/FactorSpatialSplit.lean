import OAI.Analysis.KadisonKastler.FiniteCornerSpatialSplit
import OAI.Analysis.KadisonKastler.TypeIIICommutantSpatialSplit

namespace OAI

/-! # Spatial splitting for factors with countably decomposable commutant -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem scalarCenter_commutant (M : VonNeumannAlgebra H) (hM : ScalarCenter M) :
    ScalarCenter M.commutant := by
  intro T hT hc
  have hm : T ∈ M := by
    rw [← VonNeumannAlgebra.commutant_commutant M]
    exact VonNeumannAlgebra.mem_commutant_iff.mpr hc
  exact hM T hm (fun a ha => VonNeumannAlgebra.mem_commutant_iff.mp hT a ha)

theorem exists_selfAdjoint_split_of_factor_commutant
    [Nontrivial H] (M : VonNeumannAlgebra H) (hN : ScalarCenter M.commutant)
    (hFamilies : HasCountableProjectionFamilies M.commutant)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  classical
  by_cases hfinite : ∃ p : Algebra M.commutant, IsStarProjection p ∧ p ≠ 0 ∧
      FiniteProjectionIn M.commutant p
  · obtain ⟨p, hp, hp0, hpf⟩ := hfinite
    let q : AlgebraProjection M.commutant := ⟨p, hp⟩
    let E := typeIIIInitialSpace q
    have hEq : p.val = E.starProjection := typeIIIInitialSpace_projection q
    have hE : E.starProjection ∈ M.commutant := hEq ▸ p.property
    have hE0 : E.starProjection ≠ 0 := by
      intro h
      exact hp0 (Subtype.ext (hEq.trans h))
    have hf : FiniteProjectionIn M.commutant ⟨E.starProjection, hE⟩ := by
      have he : (⟨E.starProjection, hE⟩ : Algebra M.commutant) = p := Subtype.ext hEq.symm
      rwa [he]
    exact exists_selfAdjoint_split_of_finite_commutant_corner E M hN hE hE0 hf T hTsa hT
  · have hIII : TypeIIIFactor M.commutant := {
      nonzero := one_ne_zero
      factor := hN
      purelyInfinite := by
        intro p hp hf
        by_contra hp0
        exact hfinite ⟨p, hp, hp0, hf⟩ }
    exact exists_selfAdjoint_split_of_typeIII_commutant_of_projection_countability
      M hIII hFamilies T hTsa hT

theorem exists_selfAdjoint_split_of_factor
    [Nontrivial H] (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    (hFamilies : HasCountableProjectionFamilies M.commutant)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant :=
  exists_selfAdjoint_split_of_factor_commutant M (scalarCenter_commutant M hM)
    hFamilies T hTsa hT

end

end KadisonKastler

end OAI
