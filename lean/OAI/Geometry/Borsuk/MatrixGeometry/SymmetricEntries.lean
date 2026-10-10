import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.SymmetricCoordinates

namespace OAI

namespace BorsukNine
open scoped Matrix RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
section SymmetricEntries
variable {ν : Type*} [Fintype ν] [LinearOrder ν]

noncomputable def symmetricEntries : Matrix ν ν ℝ →ₗ[ℝ] EuclideanSpace ℝ (UpperTriangle ν) where
  toFun Q := WithLp.toLp 2 (fun p => Q p.val.1 p.val.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ν] in
lemma symmetricEntries_coordinates (x : EuclideanSpace ℝ (UpperTriangle ν)) :
    symmetricEntries (symmetricCoordinates x) = x := by
  ext p
  exact symmetricCoordinates_upper x _ _ p.property

omit [Fintype ν] in
lemma symmetricCoordinates_entries {Q : Matrix ν ν ℝ} (hQ : IsSelfAdjoint Q) :
    symmetricCoordinates (symmetricEntries Q) = Q := by
  ext i j
  change (if h : i ≤ j then Q i j else Q j i) = Q i j
  split_ifs with h
  · rfl
  · have he := congrArg (fun B : Matrix ν ν ℝ => B i j) hQ.star_eq
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial] using he

end SymmetricEntries
end BorsukNine

namespace BorsukNine
open scoped RealInnerProductSpace
lemma orthogonal_frame (k : ℕ) {u : EuclideanSpace ℝ (Fin (k+1))} (hu : ‖u‖ = 1) :
    ∃ e : EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k+1)),
      (∀ x, ⟪u,e x⟫ = 0) ∧
      (∀ v, ⟪u,v⟫ = 0 → ∃ x, e x = v) := by
  let W := (Submodule.span ℝ {u})ᗮ
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hdim : Module.finrank ℝ W = k := by
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k+1))) = k+1) := ⟨by simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hu0
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
  refine ⟨W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry,?_,?_⟩
  · intro x
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b.repr.symm x).property)
  · intro v hv
    have hvW : v ∈ W := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
    refine ⟨b.repr ⟨v,hvW⟩,?_⟩
    change (b.repr.symm (b.repr ⟨v,hvW⟩)).val = v
    rw [LinearIsometryEquiv.symm_apply_apply]
end BorsukNine

end OAI
