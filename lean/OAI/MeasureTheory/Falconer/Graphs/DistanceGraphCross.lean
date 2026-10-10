import OAI.MeasureTheory.Falconer.Estimates.SelectedDistanceAssembly
import OAI.MeasureTheory.Falconer.Graphs.GraphOriginalNonedgePower

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem distanceBinIntegrand_cross (ρ ν : Measure Plane) (X Y X' Y' : Set Plane)
    (M₁ M₂ : ℝ) (b₁ b₂ : Plane → UnitCircle → ℂ) (axis : ℝ) (n j k : ℕ)
    (r : ℝ) (u w : UnitCircle) :
    distanceBinIntegrand ρ ν X Y M₁ M₂ b₁ b₂ axis n j (r,u) *
      conj (distanceBinIntegrand ρ ν X' Y' M₁ M₂ b₁ b₂ axis n k (r,w)) =
    sourceGraphFourTransform ![ρ,ν,ν,ρ] ![X,Y,Y',X'] ![M₁,M₂,M₂,M₁] ![b₁,b₂,b₂,b₁]
      (graphSourceWeight true true axis n j k) r u w := by
  simp only [sourceGraphFourTransform,graphSourceWeight,↓reduceIte,graphRotatedDistanceWeight_eq,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons,distanceBinIntegrand,map_mul,starRingEnd_self_apply]
  ring

theorem graphOriginalTerm_profile_normalization
    (ρ : Fin 4 → Measure Plane) (X : Fin 4 → Set Plane) (Mp Ma : Fin 4 → ℝ)
    (hM : ∀ i, Mp i ≠ 0) (b : Fin 4 → Plane → UnitCircle → ℂ)
    (distance plus : Bool) (axis δ v : ℝ) (j k : ℕ) (Ψ : ℝ → ℝ) :
    graphOriginalTerm ρ X Ma b distance plus axis δ v j k Ψ =
      ((Mp 0/Ma 0)*(Mp 1/Ma 1)*(Mp 2/Ma 2)*(Mp 3/Ma 3)) •
        graphOriginalTerm ρ X Mp b distance plus axis δ v j k Ψ := by
  unfold graphOriginalTerm
  simp_rw [sourceGraphFourTransform_profile_normalization ρ X Mp Ma hM b,
    smul_comm (Ψ _) ((Mp 0/Ma 0)*(Mp 1/Ma 1)*(Mp 2/Ma 2)*(Mp 3/Ma 3)), integral_smul]
  exact smul_comm _ _ _

end PlanarFalconer

end OAI
