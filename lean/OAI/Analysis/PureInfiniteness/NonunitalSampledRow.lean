import OAI.Analysis.PureInfiniteness.SpectralRowSampling
import OAI.Analysis.PureInfiniteness.SpectralMaps
import OAI.Analysis.PureInfiniteness.MappedSpectralEstimates
import OAI.Analysis.Nuclearity.UnitizedCompression

namespace OAI

/-! The sampled row error in the faithful unitization representation. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A J : Type*} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A] [Fintype J] [DecidableEq J]

lemma nonunital_sampled_row_error_norm_le
    (a : A) (f d : J → A) (t : J → ℝ) (H : CStarMatrix (Fin 1) J A)
    (hH : ∀ j, H 0 j = CFC.sqrt (f j) * d j)
    (ha : IsSelfAdjoint a) (hf : ∀ j, 0 ≤ f j) (haf : ∀ j, Commute a (f j))
    (C q : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q) (hd : ∀ j, ‖d j‖ ≤ C)
    (herr : ‖∑ j, sampledQuadraticError a (f j) (t j)‖ ≤ q ^ 2) :
    ‖unitizationOneByOne a * rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H -
      rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H * scalarSample t‖ ≤ q * C := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  exact sampled_row_error_norm_le (φ a) (fun j => φ (f j)) (fun j => φ (d j)) t
    (rectangularMap φ H) (rectangularMap_row_factor φ H f d hf hH)
    (ha.map φ) (fun j => map_nonneg φ (hf j)) (fun j => (haf j).map φ)
    C q hC hq (fun j => (NonUnitalStarAlgHom.norm_apply_le φ _).trans (hd j))
    (mapped_quadratic_norm_le φ a f t (q ^ 2) herr)

omit [PartialOrder A] [StarOrderedRing A] in
lemma nonunital_squared_row_error_norm_le (a : A)
    (H : CStarMatrix (Fin 1) J A) (t : J → ℝ) (E R : ℝ)
    (hR : 0 ≤ R) (ht0 : ∀ j, 0 ≤ t j) (htR : ∀ j, t j ≤ R)
    (hrow : ‖unitizationOneByOne a * rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H -
      rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H * scalarSample t‖ ≤ E) :
    ‖unitizationOneByOne (a * a) * rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H -
      rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ A) H *
        scalarSample (fun j => (t j) ^ 2)‖ ≤ (‖a‖ + R) * E := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hs := squared_row_error_norm_le (unitizationOneByOne a) (rectangularMap φ H)
    (scalarSample t)
  rw [← map_mul, scalarSample_square, unitizationOneByOne_norm] at hs
  apply hs.trans
  apply mul_le_mul
  · exact add_le_add le_rfl (scalarSample_norm_le t R hR ht0 htR)
  · exact hrow
  · exact norm_nonneg _
  · exact add_nonneg (norm_nonneg _) hR

end WeakPureInfiniteness

end

end OAI
