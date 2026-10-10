import OAI.Analysis.BoundedHochschild.PaulsenMatrixBlocks

namespace OAI

/-! Complete contractivity implies complete positivity of the associated
unital two-by-two operator-system map. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial A]

theorem paulsenSystemMap_positive (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (T : A →ₗ[ℂ] B)
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖)
    (n : ℕ) (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    0 ≤ operatorSystemAmplification (paulsenSystem A) (paulsenSystemMap f T) n X := by
  have hs := map_nonneg (flipMatrixNesting (A := A) n 2) hX
  rw [paulsenMatrix_source_block f hf X hX] at hs
  have ht := scalarPositiveBlock_transfer T n (hT n)
    (paulsenMatrixDiagonal f 0 X) (paulsenMatrixDiagonal f 1 X) (paulsenMatrixUpper X) hs
  rw [← paulsenMatrix_target_block f T X hX] at ht
  have h := map_nonneg (flipMatrixNesting (A := B) n 2).symm ht
  simpa only [StarAlgEquiv.symm_apply_apply] using h

end BoundedHochschild.KadisonRingrose

end

end OAI
