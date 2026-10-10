import OAI.Analysis.KadisonKastler.TypeIIIConstantNorm
import OAI.Analysis.KadisonKastler.SpatialProjectionCorners
import OAI.Analysis.KadisonKastler.VonNeumannProjectionCommutation

namespace OAI

/-! # Spatial splitting when the commutant is a separably acting type III factor

This is the type III commutant step of Sakai's spatial innerness proof.
Compact minimization, finite unitary averages and spectral projection
comparison supply every part of the argument.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_split_of_typeIII_commutant_of_projection_countability
    (M : VonNeumannAlgebra H) (hN : TypeIIIFactor M.commutant)
    (hFamilies : HasCountableProjectionFamilies M.commutant)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  obtain ⟨X, S, hXM, hXsa, hSsa, hSn, hST, hmin⟩ :=
    exists_minimal_selfAdjoint_spatial_implementer M T hTsa
  let r := ‖X - S‖
  let C := X - S
  let K := boundedSpatialResiduals M T X r
  have hC : C ∈ K := by
    refine ⟨hXsa.sub hSsa, le_rfl, ?_, ?_⟩
    · simpa only [C, sub_sub_cancel] using hSn
    · simpa only [C, sub_sub_cancel] using hST
  have hK : Convex ℝ K := boundedSpatialResiduals_convex M T X r
  have hinv (w : unitary (Algebra M.commutant)) (V : H →L[ℂ] H) (hV : V ∈ K) :
      unitaryConj (ambientAlgebraUnitary w) V ∈ K :=
    boundedSpatialResiduals_conjugate M T X r hXM hT (ambientAlgebraUnitary w)
      (w : Algebra M.commutant).property V hV
  have hself (V : H →L[ℂ] H) (hV : V ∈ K) : IsSelfAdjoint V := hV.1
  have hnorm (V : H →L[ℂ] H) (hV : V ∈ K) : ‖V‖ = r :=
    boundedSpatialResiduals_norm_eq M T X r hXsa
      (fun W hW hWn hWT => hmin X W hXM hXsa hW hWn hWT) V hV
  have hpreserve := boundedSpatialResiduals_preserves_commutant M T X r hXM hT C hC
  have hCN : C ∈ M.commutant.commutant := by
    apply mem_commutant_of_commutes_projections M.commutant C
    intro p
    by_cases hp : p.val = 0
    · rw [hp]
      exact Commute.zero_right _
    by_cases hp1 : p.val = 1
    · rw [hp1]
      exact Commute.one_right _
    obtain ⟨F, hF, hFp, _⟩ :=
      hN.exists_projection_coordinates_of_projection_countability hFamilies p hp hp1
    have hcorner : F.matrix C 0 1 = 0 :=
      F.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability
        M.commutant hN hFamilies hF K hK hinv
        hself r hnorm C hC
        (F.offDiagonal_mem_of_preserves M.commutant hF C hpreserve 0 1 (by decide))
    have hh := F.firstRange_commutes_of_corner_zero C hC.1 hcorner
    rw [hFp] at hh
    exact hh.symm
  have hCM : C ∈ M := by
    simpa only [VonNeumannAlgebra.commutant_commutant] using hCN
  have hSM : S ∈ M := by
    change S ∈ M.toSubalgebra
    have hh := M.sub_mem hXM hCM
    simpa only [C, sub_sub_cancel] using hh
  refine ⟨S, hSM, hSsa, hSn, ?_⟩
  change T - S ∈ M.commutant.toSubalgebra
  simpa only [neg_sub] using M.commutant.neg_mem hST

theorem exists_selfAdjoint_split_of_typeIII_commutant [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (hN : TypeIIIFactor M.commutant)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant :=
  exists_selfAdjoint_split_of_typeIII_commutant_of_projection_countability M hN
    (fun _ p hp ho => countable_of_orthogonal_nonzero_projections p hp ho) T hTsa hT

end

end KadisonKastler

end OAI
