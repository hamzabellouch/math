import OAI.MeasureTheory.Falconer.Angular.AngularNearSum
import OAI.MeasureTheory.Falconer.Angular.AngularTransformSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem angular_pair_sum_product (S T : Finset CellPath) (U V : CellPath → ℂ) :
    (∑ row ∈ S ×ˢ T, ∑ col ∈ S ×ˢ T, angularPairTerm U V row col) =
      ((∑ P ∈ S, U P)*conj (∑ P ∈ S, U P))*
      ((∑ Q ∈ T, V Q)*conj (∑ Q ∈ T, V Q)) := by
  have ht (row col : CellPath × CellPath) :
      angularPairTerm U V row col = (U row.1*V row.2)*conj (U col.1*V col.2) := by
    simp only [angularPairTerm,map_mul]
    ring
  simp_rw [ht]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul,← map_sum]
  simp only [Finset.sum_product,← Finset.mul_sum,← Finset.sum_mul,map_mul]
  ring

theorem sourceAngularTransform_split_absolute
    (Q : DyadicSquare) (hQ : 0 < Q.side) (A : CellPath)
    (ρ : Measure Plane) [IsFiniteMeasure ρ] (n : ℕ) (Ma Mp : ℝ) (hMp : Mp ≠ 0)
    (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2))
    (C : ℝ) (hC : ∀ x ω, ‖b x ω‖ ≤ C) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ (Q.descendant A).carrier Ma b r ω =
      (Mp / Ma) • ∑ P ∈ (occupiedAnchorPaths (Q.descendant A) ρ n).image (fun c => A++c),
        sourceAngularTransform ρ (Q.descendant P).carrier Mp b r ω := by
  classical
  rw [sourceAngularTransform_split (Q.descendant A) (Q.descendant_side_pos hQ A)
    ρ n Ma Mp hMp b hb C hC]
  congr 1
  rw [Finset.sum_image (fun _ _ _ _ he => List.append_cancel_left he)]
  simp only [DyadicSquare.descendant_append]

theorem angular_parent_occupied_partition
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : CellPath) (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (n : ℕ) (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    (D₁ D₂ : ℝ) (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂)
    (r : ℝ) (u w : UnitCircle) :
    let U := sourceAngularTransform ρ (Q₁.descendant A).carrier Ma₁ β r u
    let V := sourceAngularTransform ν (Q₂.descendant B).carrier Ma₂ γ r w
    let Uc := fun P => sourceAngularTransform ρ (Q₁.descendant P).carrier Mp₁ β r u
    let Vc := fun Q => sourceAngularTransform ν (Q₂.descendant Q).carrier Mp₂ γ r w
    (U*conj U)*(V*conj V) = ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) •
      ∑ row ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n,
      ∑ col ∈ sourceProductVertices Q₁ Q₂ ρ ν A B n, angularPairTerm Uc Vc row col := by
  dsimp only
  rw [sourceProductVertices,angular_pair_sum_product]
  rw [sourceAngularTransform_split_absolute Q₁ hQ₁ A ρ n Ma₁ Mp₁ hMp₁ β hβ D₁ hbβ,
    sourceAngularTransform_split_absolute Q₂ hQ₂ B ν n Ma₂ Mp₂ hMp₂ γ hγ D₂ hbγ]
  simp only [Complex.real_smul,map_mul,Complex.conj_ofReal,Complex.ofReal_mul,Complex.ofReal_pow]
  ring

end PlanarFalconer

end OAI
