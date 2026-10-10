import OAI.Algebra.Finitistic.Ordinary.OrdinaryComplexTensorMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinarySignedExactness

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable (Z : CochainComplex (ModuleCat.{u} A) ℤ)

@[simp] theorem map_id_left {p q q' : ℤ} (g : Z.X q ⟶ Z.X q') :
    map k A Q Z (𝟙 (Q.X p)) g =
      @mapRightTo k A (rightTerm k A Q p) (leftTerm k A Z q) (leftTerm k A Z q')
        _ _ _ _ _ _ _ _ _ (scalarLeftTower k A (Z.X q))
        _ _ _ (scalarLeftTower k A (Z.X q')) g.hom := by
  apply BalancedTensor.ext
  intro x y
  rfl

/-- A signed tensor column for an actual projective right term preserves acyclicity. -/
theorem column_acyclic (p : ℤ) [Module.Projective Aᵐᵒᵖ (rightTerm k A Q p)]
    (hZ : Z.Acyclic) : (column k A Q Z p).Acyclic := by
  intro n
  have hh := (HomologicalComplex.exactAt_iff' Z ((n-1) + -p) (n + -p) ((n+1) + -p)
    (by simp; omega)
    (by simp; omega)).mp (hZ (n + -p))
  have hex : Function.Exact
      ((Z.d ((n-1) + -p) (n + -p)).hom : leftTerm k A Z ((n-1) + -p) →ₗ[A] leftTerm k A Z (n + -p))
      ((Z.d (n + -p) ((n+1) + -p)).hom : leftTerm k A Z (n + -p) →ₗ[A] leftTerm k A Z ((n+1) + -p)) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hh
  have ht := @projectiveTensor_exact k A (rightTerm k A Q p) _ _ _ _ _ _ _
    (leftTerm k A Z ((n-1) + -p)) (leftTerm k A Z (n + -p)) (leftTerm k A Z ((n+1) + -p))
    _ _ _ (scalarLeftTower k A (Z.X ((n-1) + -p)))
    _ _ _ (scalarLeftTower k A (Z.X (n + -p)))
    _ _ _ (scalarLeftTower k A (Z.X ((n+1) + -p))) _
    (Z.d ((n-1) + -p) (n + -p)).hom (Z.d (n + -p) ((n+1) + -p)).hom hex
  have hs := exact_units_smul (-p).negOnePow _ _ ht
  apply (HomologicalComplex.exactAt_iff' _ (n-1) n (n+1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ (z : term k A Q Z p (n + -p)),
    ((column k A Q Z p).d n (n+1)).hom z = 0 →
    ∃ w : term k A Q Z p ((n-1) + -p), ((column k A Q Z p).d (n-1) n).hom w = z
  simp only [column_d,map_id_left]
  exact fun z hz => (hs z).mp hz
end LittleFinitistic.ComplexTensor

end

end OAI
