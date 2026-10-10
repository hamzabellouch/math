import OAI.Analysis.KadisonKastler.ConstructedFiniteAmplification
import OAI.Analysis.KadisonKastler.PairedFactor

namespace OAI

/-! # Complete closeness from the proved finite-factor estimate -/

namespace KadisonKastler
noncomputable section
universe u
variable {A : Type*} [CStarAlgebra A]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
variable {P : VonNeumannAlgebra (Generator.FiniteHilbert (Fin 2) H)}
local instance constructedPairedAmplificationSourceOrder : PartialOrder A := CStarAlgebra.spectralOrder _
local instance constructedPairedAmplificationSourceStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance constructedPairedAmplificationOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance constructedPairedAmplificationOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
local instance constructedPairedAmplificationFactorOrder : PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _
local instance constructedPairedAmplificationFactorStarOrder : StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _
local instance constructedPairedAmplificationSumOrder : PartialOrder (Generator.FiniteHilbert (Fin 2) H →L[ℂ]
    Generator.FiniteHilbert (Fin 2) H) := CStarAlgebra.spectralOrder _
local instance constructedPairedAmplificationSumStarOrder : StarOrderedRing (Generator.FiniteHilbert (Fin 2) H →L[ℂ]
    Generator.FiniteHilbert (Fin 2) H) := CStarAlgebra.spectralOrderedRing _

theorem constructed_complete_closeness_of_paired_factor
    (hP : Generator.IsII1Factor P.toStarSubalgebra)
    (ρ θ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : A ≃⋆ₐ[ℂ] Algebra P)
    (he : ∀ x, (e x).val = hilbertMatrix (pairedRepresentation ρ θ x))
    {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ x, ‖ρ x - θ x‖ ≤ δ * ‖x‖) :
    CompletelyBoundedBy (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap) (1000000 * δ) := by
  let S := (blockFlip (A := H →L[ℂ] H) :
    CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H))
  let T := hilbertMatrix S
  have hcomm (x : A) : innerDerivation T (e x).val =
      hilbertMatrix (offDiagonalLinearMap (ρ x - θ x)) := by
    rw [he]
    change T * hilbertMatrix (pairedRepresentation ρ θ x) -
      hilbertMatrix (pairedRepresentation ρ θ x) * T = _
    rw [show T = hilbertMatrix S from rfl, ← hilbertMatrix_mul, ← hilbertMatrix_mul]
    have hsub := map_sub (hilbertMatrixHom (H := H) (n := Fin 2))
      (S * pairedRepresentation ρ θ x) (pairedRepresentation ρ θ x * S)
    change hilbertMatrix (S * pairedRepresentation ρ θ x - pairedRepresentation ρ θ x * S) =
      hilbertMatrix (S * pairedRepresentation ρ θ x) -
        hilbertMatrix (pairedRepresentation ρ θ x * S) at hsub
    rw [← hsub]
    exact congrArg hilbertMatrix (paired_switch_commutator ρ θ x)
  have hb : ∀ a ∈ P, ‖T * a - a * T‖ ≤ δ * ‖a‖ := by
    intro a ha
    let x := e.symm ⟨a, ha⟩
    have hex : e x = ⟨a, ha⟩ := e.apply_symm_apply _
    have hi := congrArg norm (hcomm x)
    rw [hex, norm_hilbertMatrix, offDiagonalLinearMap_apply, norm_blockOffDiagonal] at hi
    change ‖T * a - a * T‖ = max ‖-(ρ x - θ x)‖ ‖ρ x - θ x‖ at hi
    simp only [norm_neg, max_self] at hi
    have hxnorm : ‖x‖ = ‖a‖ := by
      have hh : ‖e x‖ = ‖x‖ := injective_starAlgHom_norm e.toStarAlgHom e.injective x
      rw [hex] at hh
      exact hh.symm
    rw [hi]
    simpa only [hxnorm] using hclose x
  have hc := constructed_finiteFactor_completelyBounded P hP T hδ hb
  have hmap : ((innerDerivation T).comp P.toStarSubalgebra.subtype.toLinearMap).comp
      e.toAlgEquiv.toLinearMap =
      (hilbertMatrixHom (H := H) (n := Fin 2)).toAlgHom.toLinearMap.comp
        (offDiagonalLinearMap.comp (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap)) := by
    apply LinearMap.ext
    intro x
    exact hcomm x
  have hcb : CompletelyBoundedBy
      (offDiagonalLinearMap.comp (ρ.toAlgHom.toLinearMap - θ.toAlgHom.toLinearMap))
      (1000000 * δ) := by
    intro p q X
    have hX := hc p q (CStarMatrix.mapₗ e.toAlgEquiv.toLinearMap X)
    have hn : ‖CStarMatrix.mapₗ e.toAlgEquiv.toLinearMap X‖ = ‖X‖ :=
      injective_starAlgHom_completelyIsometric e.toStarAlgHom e.injective p q X
    rw [hn] at hX
    rw [← matrix_map_comp, hmap, matrix_map_comp,
      injective_starAlgHom_completelyIsometric
        (hilbertMatrixHom (H := H) (n := Fin 2)) hilbertMatrixHom_injective] at hX
    exact hX
  exact (completelyBoundedBy_offDiagonal_iff _ _).mp hcb

end
end KadisonKastler

end OAI
