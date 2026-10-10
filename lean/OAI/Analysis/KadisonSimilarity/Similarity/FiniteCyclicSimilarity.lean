import OAI.Analysis.KadisonSimilarity.Tracial.BoundedMatrixHom

namespace OAI

/-! Finitely cyclic representations reduce to the cyclic case by finite
matrix amplification and the first-coordinate corner. -/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def scalarCStarMatrixHom (n : ℕ) : A →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp {
    toAlgHom := Matrix.scalarAlgHom (Fin n) ℂ
    map_star' := by
      intro a
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar, Matrix.star_apply, h, eq_comm] }

def firstCoordinateInclusion (n : ℕ) (hn : 0 < n) : H →L[ℂ] HilbertCopies H n :=
  ({ toFun := fun x => PiLp.single 2 (⟨0, hn⟩ : Fin n) x
     map_add' := by intro x y; exact PiLp.single_add _ _
     map_smul' := by
       intro c x
       ext i
       by_cases h : i = (⟨0, hn⟩ : Fin n) <;> simp [h] } :
    H →ₗ[ℂ] HilbertCopies H n).mkContinuous 1 (fun x => by simp)

theorem finitely_cyclic_similarity (π : BoundedUnitalHom A H) {n : ℕ} (hn : 0 < n)
    (ξ : Fin n → H) (hξ : DenseRange (finiteOrbitMap π ξ)) : SimilarToStar A H π := by
  let ρ := boundedMatrixHom π n
  obtain ⟨S, hS⟩ := cyclic_similarity ρ (WithLp.toLp 2 ξ) (boundedMatrixHom_cyclic π ξ hξ)
  let φ := scalarCStarMatrixHom (A := A) n
  let L := φ.toLinearMap.mkContinuous 1
    (fun a => by simpa using NonUnitalStarAlgHom.norm_apply_le φ a)
  let τ : BoundedUnitalHom A (HilbertCopies H n) :=
    ⟨ρ.1.comp φ.toAlgHom, ρ.2.comp L.continuous⟩
  have hτ : SimilarToStar A (HilbertCopies H n) τ := by
    refine ⟨S, fun a => ?_⟩
    change (S : _ →L[ℂ] _) * ρ.1 (φ (star a)) * (↑S⁻¹ : _ →L[ℂ] _) = _
    rw [map_star]
    exact hS (φ a)
  let U := firstCoordinateInclusion (H := H) n hn
  let V : HilbertCopies H n →L[ℂ] H := PiLp.proj 2 (fun _ : Fin n => H) (⟨0, hn⟩ : Fin n)
  apply similarity_of_retract π τ U V ?_ hτ
  intro a
  ext x
  change (boundedMatrixHom π n).1 (φ a) (U x) (⟨0, hn⟩ : Fin n) = π.1 a x
  rw [boundedMatrixHom_apply]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · have hd : (φ a) (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) = a := by
      change (if (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ then a else 0) = a
      simp
    rw [hd]
    congr 1
  · intro j _ hj
    have hd : (φ a) (⟨0, hn⟩ : Fin n) j = 0 := by
      change (if (⟨0, hn⟩ : Fin n) = j then a else 0) = 0
      simp [Ne.symm hj]
    rw [hd, map_zero]
    rfl
  · simp

end KadisonSimilarity

end

end OAI
