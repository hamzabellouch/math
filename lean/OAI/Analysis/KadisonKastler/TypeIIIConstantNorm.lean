import OAI.Analysis.KadisonKastler.TypeIIIPositiveCorner
import OAI.Analysis.KadisonKastler.MatrixStrictContraction
import OAI.Analysis.KadisonKastler.MatrixDiagonalAverage

namespace OAI

/-! # Type III corners of a constant-norm convex family vanish

The nonzero corner can be made strictly positive by independent small
left and right contractions. Both contractions come from convex unitary
averages. Removing the resulting off-diagonal corner then contradicts
the constant norm of the family.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance typeIIIConstantNormInstance1 : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance typeIIIConstantNormInstance2 : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
local instance typeIIIConstantNormInstance3 (N : VonNeumannAlgebra H) : LE (Algebra N) :=
  (CStarAlgebra.spectralOrder (Algebra N)).toLE
local instance typeIIIConstantNormInstance4 (N : VonNeumannAlgebra H) : PartialOrder (Algebra N) :=
  CStarAlgebra.spectralOrder _
local instance typeIIIConstantNormInstance5 (N : VonNeumannAlgebra H) : Preorder (Algebra N) :=
  (CStarAlgebra.spectralOrder (Algebra N)).toPreorder
local instance typeIIIConstantNormInstance6 (N : VonNeumannAlgebra H) : StarOrderedRing (Algebra N) :=
  CStarAlgebra.spectralOrderedRing _

theorem CuntzFamily.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability
    (S : CuntzFamily (Fin 2) H) (N : VonNeumannAlgebra H) (hN : TypeIIIFactor N)
    (hFamilies : HasCountableProjectionFamilies N)
    (hS : ∀ i, S.entry i ∈ N) (K : Set (H →L[ℂ] H)) (hK : Convex ℝ K)
    (hinv : ∀ w : unitary (Algebra N), ∀ T ∈ K,
      unitaryConj (ambientAlgebraUnitary w) T ∈ K)
    (hself : ∀ T ∈ K, IsSelfAdjoint T) (r : ℝ) (hnorm : ∀ T ∈ K, ‖T‖ = r)
    (T : H →L[ℂ] H) (hT : T ∈ K) (hc : S.matrix T 0 1 ∈ N) :
    S.matrix T 0 1 = 0 := by
  let : Nontrivial (H →L[ℂ] H) := ⟨⟨1, 0, hN.nonzero⟩⟩
  by_contra hc0
  let c : Algebra N := ⟨S.matrix T 0 1, hc⟩
  have hcne : c ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  obtain ⟨a, b, ha, hb, δ, hδ, hpos⟩ :=
    hN.exists_small_positive_product_of_projection_countability hFamilies c hcne
  obtain ⟨V, hV, hVcorner⟩ := S.small_contraction_corner_mem N hS K hK hinv T hT a b ha hb
  have hpositive : algebraMap ℝ (H →L[ℂ] H) δ ≤ S.matrix V 0 1 := by
    have hm := (NonUnitalStarAlgHom.map_le_map_iff
      N.toStarSubalgebra.subtype.toNonUnitalStarAlgHom Subtype.val_injective).mpr hpos
    change δ • (1 : H →L[ℂ] H) ≤ a.val * c.val * b.val at hm
    rw [Algebra.algebraMap_eq_smul_one, hVcorner]
    exact hm
  have hmatrix : IsSelfAdjoint (S.matrix V) := by
    change star (S.matrixHom V) = S.matrixHom V
    rw [← map_star, (hself V hV).star_eq]
  have hlt := norm_matrix_diagonal_lt_of_positive_corner (S.matrix V) hmatrix δ hδ hpositive
  obtain ⟨W, hW, hWmatrix⟩ := S.exists_diagonal_average_mem N hS K hK hinv V hV
  rw [← hWmatrix, S.norm_matrix, S.norm_matrix, hnorm W hW, hnorm V hV] at hlt
  exact (lt_irrefl r) hlt

theorem CuntzFamily.upperRight_eq_zero_of_typeIII_constantNorm
    [TopologicalSpace.SeparableSpace H]
    (S : CuntzFamily (Fin 2) H) (N : VonNeumannAlgebra H) (hN : TypeIIIFactor N)
    (hS : ∀ i, S.entry i ∈ N) (K : Set (H →L[ℂ] H)) (hK : Convex ℝ K)
    (hinv : ∀ w : unitary (Algebra N), ∀ T ∈ K,
      unitaryConj (ambientAlgebraUnitary w) T ∈ K)
    (hself : ∀ T ∈ K, IsSelfAdjoint T) (r : ℝ) (hnorm : ∀ T ∈ K, ‖T‖ = r)
    (T : H →L[ℂ] H) (hT : T ∈ K) (hc : S.matrix T 0 1 ∈ N) :
    S.matrix T 0 1 = 0 :=
  S.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability N hN
    (fun _ p hp ho => countable_of_orthogonal_nonzero_projections p hp ho)
    hS K hK hinv hself r hnorm T hT hc

end

end KadisonKastler

end OAI
