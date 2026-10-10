import OAI.MeasureTheory.Falconer.Graphs.GraphFourTransformExpansion
import OAI.MeasureTheory.Falconer.Graphs.ProductGraphIndices
import OAI.MeasureTheory.Falconer.Angular.AngularTransformSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem graphProductWeight_total {m : ℕ} (hm : 0 < m) (p : UnitCircle × UnitCircle) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ∑ s : Bool, graphProductWeight s m j k p) = 1 := by
  simp only [Fintype.sum_bool,graphProductWeight_partition]
  simp only [graphBinWeight,← Complex.ofReal_sum,← Finset.mul_sum,
    circleAngularBin_partition hm,mul_one,Complex.ofReal_one]

theorem sourceGraphFourTransform_measurable
    (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ l, Measurable (fun p : Plane × UnitCircle => b l p.1 p.2)) (hW : Measurable W) :
    Measurable (fun p : ℝ × (UnitCircle × UnitCircle) => sourceGraphFourTransform ρ X M b W p.1 p.2.1 p.2.2) := by
  have hm := graphFourKernel_measurable b W hb hW
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi (fun l => (ρ l).restrict (X l)))
  simp_rw [sourceGraphFourTransform_endpoint_integral]
  exact (measurable_const (a := ((M 0*M 1)*(M 2*M 3))⁻¹)).smul hi.measurable

theorem sourceGraphFourTransform_bound
    (ρ : Fin 4 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (X : Fin 4 → Set Plane) (M : Fin 4 → ℝ) (hM : ∀ l, 0 < M l)
    (b : Fin 4 → Plane → UnitCircle → ℂ) (W : UnitCircle × UnitCircle → ℂ)
    (B : Fin 4 → ℝ) (hB : ∀ l, 0 ≤ B l) (hb : ∀ l x dir, ‖b l x dir‖ ≤ B l)
    (hW : ∀ p, ‖W p‖ ≤ 1) (r : ℝ) (u w : UnitCircle) :
    ‖sourceGraphFourTransform ρ X M b W r u w‖ ≤
      ((B 0*(ρ 0 (X 0)).toReal/M 0)*(B 1*(ρ 1 (X 1)).toReal/M 1))*
      ((B 2*(ρ 2 (X 2)).toReal/M 2)*(B 3*(ρ 3 (X 3)).toReal/M 3)) := by
  have ht := fun l dir => sourceAngularTransform_norm_le (ρ l) (X l) (M l) (hM l) (b l)
    (B l) (fun x _ => hb l x) r dir
  have hp (l : Fin 4) : 0 ≤ B l*(ρ l (X l)).toReal/M l :=
    div_nonneg (mul_nonneg (hB l) ENNReal.toReal_nonneg) (hM l).le
  simp only [sourceGraphFourTransform,norm_mul,Complex.norm_conj]
  calc
    _ ≤ 1*((B 0*(ρ 0 (X 0)).toReal/M 0)*(B 1*(ρ 1 (X 1)).toReal/M 1))*
        ((B 2*(ρ 2 (X 2)).toReal/M 2)*(B 3*(ρ 3 (X 3)).toReal/M 3)) := by
      exact mul_le_mul
        (mul_le_mul (hW (u,w)) (mul_le_mul (ht 0 u) (ht 1 u) (norm_nonneg _) (hp 0))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one)
        (mul_le_mul (ht 2 w) (ht 3 w) (norm_nonneg _) (hp 2))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg zero_le_one (mul_nonneg (hp 0) (hp 1)))
    _ = _ := by ring

theorem sourceGraphFourTransform_product_partition
    (X Y : DyadicSquare) (hX : 0 < X.side) (hY : 0 < Y.side)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν] (n m : ℕ) (hm : 0 < m)
    (M₁ M₂ : ℝ) (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0) (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hb₁ : Measurable (fun p : Plane × UnitCircle => b₁ p.1 p.2))
    (hb₂ : Measurable (fun p : Plane × UnitCircle => b₂ p.1 p.2))
    (C₁ C₂ : ℝ) (hC₁ : ∀ x dir, ‖b₁ x dir‖ ≤ C₁) (hC₂ : ∀ x dir, ‖b₂ x dir‖ ≤ C₂)
    (r : ℝ) (u w : UnitCircle) :
    sourceGraphFourTransform ![ρ,ρ,ν,ν] ![X.carrier,X.carrier,Y.carrier,Y.carrier]
      ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂] (fun _ => 1) r u w =
    ∑ e ∈ sourceProductRelativeIndices X Y ρ ν n m,
      sourceGraphFourTransform ![ρ,ρ,ν,ν]
        (fun l => (graphQuadCells ![X,X,Y,Y] e.1 l).carrier)
        ![M₁,M₁,M₂,M₂] ![b₁,b₁,b₂,b₂] (graphProductWeight e.2.2 m e.2.1.1 e.2.1.2) r u w := by
  classical
  simp only [sourceProductRelativeIndices,Finset.sum_product]
  simp only [sourceGraphFourTransform,graphQuadCells,graphQuadPath,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one_mul]
  simp only [← Finset.sum_mul,graphProductWeight_total hm,one_mul]
  rw [sourceAngularTransform_split X hX ρ n M₁ M₁ hM₁ b₁ hb₁ C₁ hC₁,
    sourceAngularTransform_split Y hY ν n M₂ M₂ hM₂ b₂ hb₂ C₂ hC₂]
  simp only [div_self hM₁,div_self hM₂,one_smul]
  simp only [← Finset.mul_sum,← Finset.sum_mul,← map_sum]

end PlanarFalconer

end OAI
