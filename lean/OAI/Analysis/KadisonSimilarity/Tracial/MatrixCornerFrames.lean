import OAI.Analysis.KadisonSimilarity.Tracial.MatrixUnitCoordinates

namespace OAI

/-! A finite family of partial isometries with common initial projection
constructs the actual Hilbert coordinate frame of a corner. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- An algebraic partial isometry is unchanged by its initial projection. -/
theorem mul_initial_projection (e v : P) (he : IsStarProjection e) (hv : star v * v = e) :
    v * e = v := by
  apply sub_eq_zero.mp
  apply (CStarRing.star_mul_self_eq_zero_iff (v * e - v)).mp
  calc
    star (v * e - v) * (v * e - v) =
        e * (star v * v) * e - e * (star v * v) - (star v * v) * e + star v * v := by
      rw [star_sub, star_mul, he.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = 0 := by simp only [hv, he.isIdempotentElem.eq]; abel

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The columns are multiplication by the partial isometries after the
isometric inclusion of the initial corner. -/
def partialIsometryColumns (L : P →⋆ₐ[ℂ] (H →L[ℂ] H))
    (e : P) (he : IsStarProjection e) {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1)
    (I : F →ₗᵢ[ℂ] H)
    (hI : I.toContinuousLinearMap.comp I.toContinuousLinearMap.adjoint = L e) :
    FiniteOrthogonalColumns F H n where
  inclusion i := (L (v i)).comp I.toContinuousLinearMap
  adjoint_comp i j := by
    simp only [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc (L (star (v i))), ← ContinuousLinearMap.mul_def,
      ← map_mul, hv]
    split_ifs with hij
    · rw [← hI]
      simp only [← ContinuousLinearMap.comp_assoc, I.adjoint_comp_self,
        ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    · simp
  resolution := by
    have hu (i : Fin n) : v i * e = v i :=
      mul_initial_projection e (v i) he (by simpa using hv i i)
    have hterm (i : Fin n) :
        ((L (v i)).comp I.toContinuousLinearMap).comp
          ((L (v i)).comp I.toContinuousLinearMap).adjoint = L (v i * star (v i)) := by
      rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
      change ((L (v i)).comp I.toContinuousLinearMap).comp
        (I.toContinuousLinearMap.adjoint.comp (L (star (v i)))) = _
      rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc I.toContinuousLinearMap,
        hI]
      change L (v i) * (L e * L (star (v i))) = _
      rw [← map_mul, ← map_mul, ← mul_assoc, hu]
    simp_rw [hterm]
    rw [← map_sum, hsum, map_one]
    rfl

/-- The matrix entries of the represented algebra are the algebraic corner
compressions by the same partial isometries. -/
theorem partialIsometryColumns_entry
    (L : P →⋆ₐ[ℂ] (H →L[ℂ] H)) (e : P) (he : IsStarProjection e)
    {n : ℕ} (v : Fin n → P)
    (hv : ∀ i j, star (v i) * v j = if i = j then e else 0)
    (hsum : ∑ i, v i * star (v i) = 1) (I : F →ₗᵢ[ℂ] H)
    (hI : I.toContinuousLinearMap.comp I.toContinuousLinearMap.adjoint = L e)
    (a : P) (i j : Fin n) :
    ((partialIsometryColumns L e he v hv hsum I hI).inclusion i).adjoint.comp
      ((L a).comp ((partialIsometryColumns L e he v hv hsum I hI).inclusion j)) =
      I.toContinuousLinearMap.adjoint.comp
        ((L (star (v i) * a * v j)).comp I.toContinuousLinearMap) := by
  change ((L (v i)).comp I.toContinuousLinearMap).adjoint.comp
    ((L a).comp ((L (v j)).comp I.toContinuousLinearMap)) = _
  rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
  simp only [map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

end KadisonSimilarity

end

end OAI
