import OAI.Analysis.KadisonSimilarity.Similarity.CyclicSimilarity
import OAI.Analysis.KadisonSimilarity.Similarity.SimilarityRetract

namespace OAI

/-! Finite matrix amplification of a bounded homomorphism. A finite
generating family becomes one cyclic vector for this amplification. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def boundedMatrixHom (π : BoundedUnitalHom A H) (n : ℕ) :
    BoundedUnitalHom (CStarMatrix (Fin n) (Fin n) A) (HilbertCopies H n) := by
  let ρ := (operatorMatrixRepresentation (H := H) n).toAlgHom.comp
    (π.1.mapMatrix.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toAlgHom)
  refine ⟨ρ, ?_⟩
  have hmap : Continuous (fun X : Matrix (Fin n) (Fin n) A => X.map π.1) := by
    exact continuous_pi fun i => continuous_pi fun j =>
      π.2.comp ((continuous_apply j).comp (continuous_apply i))
  have hop : Continuous (fun X : Matrix (Fin n) (Fin n) (H →L[ℂ] H) => matrixOperator X) := by
    let L := (matrixRepresentation (H := H) n).toLinearMap.mkContinuous 1
      (fun X => by
        simpa using (NonUnitalStarAlgHom.norm_apply_le (matrixRepresentation (H := H) n) X))
    exact L.continuous.comp CStarMatrix.ofMatrixL.continuous
  exact hop.comp (hmap.comp CStarMatrix.ofMatrixL.symm.continuous)

@[simp] theorem boundedMatrixHom_apply (π : BoundedUnitalHom A H) (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) A) (ξ : HilbertCopies H n) (i : Fin n) :
    (boundedMatrixHom π n).1 X ξ i = ∑ j, π.1 (X i j) (ξ j) := by
  exact matrixOperator_apply _ ξ i

def finiteOrbitMap (π : BoundedUnitalHom A H) {n : ℕ} (ξ : Fin n → H) :
    (Fin n → A) →ₗ[ℂ] H where
  toFun a := ∑ i, π.1 (a i) (ξ i)
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum]

theorem boundedMatrixHom_cyclic (π : BoundedUnitalHom A H) {n : ℕ}
    (ξ : Fin n → H) (hξ : DenseRange (finiteOrbitMap π ξ)) :
    DenseRange (fun X : CStarMatrix (Fin n) (Fin n) A =>
      (boundedMatrixHom π n).1 X (WithLp.toLp 2 ξ)) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm
  have hd : DenseRange (fun a : Fin n → Fin n → A => fun i => finiteOrbitMap π ξ (a i)) :=
    DenseRange.piMap (fun _ => hξ)
  have he := e.surjective.denseRange.comp hd e.continuous
  apply he.mono
  rintro x ⟨a, rfl⟩
  refine ⟨CStarMatrix.ofMatrix a, ?_⟩
  ext i
  simp only [boundedMatrixHom_apply, finiteOrbitMap, LinearMap.coe_mk,
    AddHom.coe_mk]
  rfl

end KadisonSimilarity

end

end OAI
