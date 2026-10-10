import OAI.Geometry.SurfaceImmersion.Geometry.EuclideanSurfaceImageNull
import Mathlib.LinearAlgebra.CrossProduct

namespace OAI

/-! A smooth curve in three-space admits one constant vector transverse
to every nonzero velocity.  This uses the proved two-dimensional image estimate. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_curve_transverse_vector (v : ℝ → (Fin 3 → ℝ))
    (hv : ContDiff ℝ ∞ v) :
    ∃ a : Fin 3 → ℝ, ∀ t r : ℝ, r • v t ≠ a := by
  let E := EuclideanSpace.equiv (Fin 3) ℝ
  let f : Base → ProjectionTarget 3 := fun x => E.symm (x 0 • v (x 1))
  have hf : ContDiff ℝ ∞ f :=
    E.symm.contDiff.comp ((contDiff_apply ℝ ℝ 0).smul (hv.comp (contDiff_apply ℝ ℝ 1)))
  have hn : volume (range f) = 0 := euclidean_surface_image_null f hf
  have hae : ∀ᵐ x ∂volume, x ∉ range f := by
    simp only [ae_iff,not_not]
    exact hn
  obtain ⟨a,_,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty
    univ isOpen_univ Set.univ_nonempty
  refine ⟨E a,?_⟩
  intro t r heq
  apply ha
  refine ⟨![r,t],?_⟩
  change E.symm (r • v t) = a
  rw [heq,E.symm_apply_apply]

lemma curve_transverse_vector_independent {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : LinearIndependent ℝ ![v,a] :=
  (LinearIndependent.pair_iff' hv).mpr ha

lemma curve_transverse_cross_ne_zero {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : v ⨯₃ a ≠ 0 :=
  crossProduct_ne_zero_iff_linearIndependent.mpr (curve_transverse_vector_independent hv ha)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
