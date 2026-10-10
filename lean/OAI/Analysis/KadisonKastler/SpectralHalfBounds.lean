import OAI.Analysis.KadisonKastler.ProjectionSwapAverage
import OAI.Analysis.FactorGeneration.Supports

namespace OAI

/-! # Order bounds from the positive spectral half -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

local instance spectralHalfOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance spectralHalfPreorder : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralHalfLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance spectralHalfStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- The positive and negative spectral halves bound a self-adjoint operator
by its norm times the corresponding projection. -/
theorem spectral_half_bounds (x : Algebra M) (hx : IsSelfAdjoint x) :
    let p := positiveSupport x
    x.val ≤ ‖x‖ • p.val.val ∧
      -(‖x‖ • (1 - p.val.val)) ≤ x.val := by
  let p := positiveSupport x
  let q : AlgebraProjection M := ⟨1 - p.val, p.property.one_sub⟩
  have hpos : p.val * x * p.val ≤ ‖x‖ • p.val := by
    have h := star_left_conjugate_le_conjugate (hx.le_algebraMap_norm_self) p.val
    simpa only [p.property.isSelfAdjoint.star_eq, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, smul_mul_assoc, mul_one, p.property.isIdempotentElem.eq] using h
  have hneg : -(‖x‖ • q.val) ≤ q.val * x * q.val := by
    have h := star_left_conjugate_le_conjugate (hx.neg_algebraMap_norm_le_self) q.val
    simpa only [q.property.isSelfAdjoint.star_eq, Algebra.algebraMap_eq_smul_one,
      mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      q.property.isIdempotentElem.eq] using h
  have hu : x ≤ ‖x‖ • p.val := by
    apply le_trans _ hpos
    rw [positiveSupport_compression x hx]
    calc
      x = x⁺ - x⁻ := (CFC.posPart_sub_negPart x hx).symm
      _ ≤ x⁺ := sub_le_self _ (CFC.negPart_nonneg x)
  have hl : -(‖x‖ • q.val) ≤ x := by
    apply hneg.trans
    change (1 - p.val) * x * (1 - p.val) ≤ x
    rw [positiveSupport_complement_compression x hx]
    calc
      -x⁻ ≤ x⁺ - x⁻ := by simpa using sub_le_sub_right (CFC.posPart_nonneg x) x⁻
      _ = x := CFC.posPart_sub_negPart x hx
  constructor
  · have h := map_rel M.toStarSubalgebra.subtype hu
    let L := M.toStarSubalgebra.subtype.toAlgHom.toLinearMap.restrictScalars ℝ
    change L x ≤ L (‖x‖ • p.val) at h
    rw [L.map_smul] at h
    exact h
  · have h := map_rel M.toStarSubalgebra.subtype hl
    let L := M.toStarSubalgebra.subtype.toAlgHom.toLinearMap.restrictScalars ℝ
    change L (-(‖x‖ • q.val)) ≤ L x at h
    rw [map_neg, L.map_smul] at h
    exact h

/-- Symmetric scalar order bounds control the norm of a self-adjoint operator. -/
theorem norm_le_of_symmetric_scalar_bounds [Nontrivial H]
    (x : H →L[ℂ] H) (hx : IsSelfAdjoint x) (r : ℝ)
    (hl : -(algebraMap ℝ (H →L[ℂ] H) r) ≤ x)
    (hu : x ≤ algebraMap ℝ (H →L[ℂ] H) r) : ‖x‖ ≤ r := by
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum x hx with h | h
  · exact (le_algebraMap_iff_spectrum_le hx).mp hu _ h
  · have hh := (algebraMap_le_iff_le_spectrum hx).mp
      (show algebraMap ℝ (H →L[ℂ] H) (-r) ≤ x by simpa using hl) _ h
    linarith

end

end KadisonKastler

end OAI
