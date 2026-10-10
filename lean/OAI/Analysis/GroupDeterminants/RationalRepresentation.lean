import OAI.Analysis.GroupDeterminants.TransferTrace

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section RationalMap
variable {G I J : Type} [Group G]

def rationalComplexMap : MonoidAlgebra ℚ G →+* MonoidAlgebra ℂ G :=
  MonoidAlgebra.mapRingHom G (Rat.castHom ℂ)

lemma rationalComplexMap_smul (q : ℚ) (A : Matrix I J (MonoidAlgebra ℚ G)) :
    (q • A).map rationalComplexMap = (q : ℝ) • A.map rationalComplexMap := by
  apply Matrix.ext
  intro i j
  change rationalComplexMap (q • A i j) = (q : ℝ) • rationalComplexMap (A i j)
  rw [map_rat_smul, Rat.cast_smul_eq_qsmul ℝ]

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
omit [Fintype J] in
lemma transferMatrix_map_complex (q : ℚ) (P : Matrix J J (MonoidAlgebra ℚ G))
    (U : Matrix J I (MonoidAlgebra ℚ G)) (V : Matrix I J (MonoidAlgebra ℚ G)) :
    (transferMatrix q P U V).map rationalComplexMap =
      transferMatrix (q : ℝ) (P.map rationalComplexMap) (U.map rationalComplexMap)
        (V.map rationalComplexMap) := by
  simp only [transferMatrix, Matrix.fromBlocks_map, rationalComplexMap_smul,
    Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_sub _ (map_sub _) _ _, Matrix.map_mul, Rat.cast_inv]

omit [Fintype I] [DecidableEq I] in
lemma rationalComplexMap_star (P : Matrix I I (MonoidAlgebra ℚ G)) :
    (star P).map rationalComplexMap = star (P.map rationalComplexMap) := by
  apply Matrix.ext
  intro i j
  change rationalComplexMap (star (P j i)) = star (rationalComplexMap (P j i))
  exact groupAlgebra_map_star (Rat.castHom ℂ) (fun q => by simp) _

omit [DecidableEq I] in
lemma rationalComplexMap_trace (P : Matrix I I (MonoidAlgebra ℚ G)) :
    (∑ i, ((P.map rationalComplexMap) i i).coeff 1).re =
      ((∑ i, (P i i).coeff 1 : ℚ) : ℝ) := by
  simp [Matrix.map_apply, rationalComplexMap]

lemma reindexed_rational_isUnit (A : Matrix I I (MonoidAlgebra ℤ G))
    (hA : IsUnit (A.map toRat)) :
    IsUnit (rationalMatrix (Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I) A)) :=
  hA.map (Matrix.reindexRingEquiv (MonoidAlgebra ℚ G) (Fintype.equivFin I)).toRingHom

lemma rationalIndexed_integer (A : Matrix I I (MonoidAlgebra ℤ G)) :
    indexedComplexRepresentation ((A.map toRat).map rationalComplexMap) =
      regularOperator (Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I) A) := by
  have hf : rationalComplexMap.comp (toRat (G := G)) =
      MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ) := by
    rw [rationalComplexMap, toRat, ← MonoidAlgebra.mapRingHom_comp]
    congr 1
  change complexOperator ((Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I) A).map
    (rationalComplexMap.comp (toRat (G := G)))) = _
  rw [hf, complexOperator_integer]

end RationalMap
end GroupRingDeterminant

end

end OAI
