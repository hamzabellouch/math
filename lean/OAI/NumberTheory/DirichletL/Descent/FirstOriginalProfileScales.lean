import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileCells

namespace OAI

noncomputable section
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows InverseSecondSourceBlocks

def physicalScales (X : ℝ) (k : SourceIndex) (l : ℕ) : Fin 9→ℝ :=
  rawScales k l (X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))
    (X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))

lemma physicalScales_pos (X : ℝ) (hX : 0<X) (k : SourceIndex) (l : ℕ) :
    ∀i,0<physicalScales X k l i := by
  apply rawScales_pos
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))

lemma physicalScales_products (X : ℝ) (k : SourceIndex) (l : ℕ) :
    physicalScales X k l 0*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 7=X ∧
    physicalScales X k l 1*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 8=X := by
  constructor
  · change (dyadScale (k 0)*dyadScale (k 2)*dyadScale l)*(X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))=X
    exact mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)))
  · change (dyadScale (k 1)*dyadScale (k 2)*dyadScale l)*(X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))=X
    exact mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)))

theorem physicalScales_rpow (Z r : ℝ) (hZ : 1<Z) (k : SourceIndex) (l : ℕ) :
    physicalScales (Z^r) k l=fun i=>Z^(![Real.logb Z (dyadScale (k 0)),
      Real.logb Z (dyadScale (k 1)),Real.logb Z (dyadScale (k 2)),
      Real.logb Z (dyadScale (k 3)),Real.logb Z (dyadScale (k 4)),Real.logb Z (dyadScale l),
      Real.logb Z (dyadScale (k 5)),
      r-Real.logb Z (dyadScale (k 0))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l),
      r-Real.logb Z (dyadScale (k 1))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l)] i) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he (n : ℕ) : Z^(Real.logb Z (dyadScale n))=dyadScale n :=
    Real.rpow_logb hz (ne_of_gt hZ) (dyadScale_pos n)
  funext i
  fin_cases i <;> simp [physicalScales,rawScales,he,Real.rpow_sub hz,div_div]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
