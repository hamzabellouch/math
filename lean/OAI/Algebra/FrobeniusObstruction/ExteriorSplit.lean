import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

noncomputable section
open scoped TensorProduct
namespace BoundaryOnly.FormalObstruction.ExteriorSplit
variable {k ι κ : Type*} [CommRing k]

abbrev Ext (k ι : Type*) [CommRing k] := ExteriorAlgebra k (ι → k)

def leftVec : (ι → k) →ₗ[k] (ι ⊕ κ → k) where
  toFun v := Sum.elim v (fun _ => 0)
  map_add' x y := by funext i; cases i <;> simp
  map_smul' a x := by funext i; cases i <;> simp

def rightVec : (κ → k) →ₗ[k] (ι ⊕ κ → k) where
  toFun v := Sum.elim (fun _ => 0) v
  map_add' x y := by funext i; cases i <;> simp
  map_smul' a x := by funext i; cases i <;> simp

def splitIsometry : (0 : QuadraticForm k (ι ⊕ κ → k)).IsometryEquiv
    ((0 : QuadraticForm k (ι → k)).prod (0 : QuadraticForm k (κ → k))) :=
  { LinearEquiv.sumArrowLequivProdArrow ι κ k k with
    map_app' := fun x => by simp }

noncomputable def sumEquiv : Ext k (ι ⊕ κ) ≃ₗ[k] Ext k ι ⊗[k] Ext k κ :=
  ((CliffordAlgebra.equivOfIsometry (splitIsometry (k := k) (ι := ι) (κ := κ))).toLinearEquiv.trans
    (CliffordAlgebra.prodEquiv (0 : QuadraticForm k (ι → k))
      (0 : QuadraticForm k (κ → k))).toLinearEquiv).trans
        (GradedTensorProduct.of k _ _).symm

@[simp] theorem sumEquiv_symm_tmul (x : Ext k ι) (y : Ext k κ) :
    (sumEquiv (k := k) (ι := ι) (κ := κ)).symm (x ⊗ₜ[k] y) =
      ExteriorAlgebra.map leftVec x * ExteriorAlgebra.map rightVec y := by
  change (CliffordAlgebra.equivOfIsometry splitIsometry).symm
    (CliffordAlgebra.toProd _ _ (GradedTensorProduct.of k _ _ (x ⊗ₜ[k] y))) = _
  rw [CliffordAlgebra.toProd, GradedTensorProduct.lift_tmul, map_mul]
  congr 1
  · have h : ((CliffordAlgebra.equivOfIsometry
          (splitIsometry (k := k) (ι := ι) (κ := κ))).symm.toAlgHom).comp
          (CliffordAlgebra.map (QuadraticMap.Isometry.inl _ _)) =
        ExteriorAlgebra.map leftVec := by
      ext v
      simp [CliffordAlgebra.equivOfIsometry, splitIsometry, leftVec]; rfl
    exact AlgHom.congr_fun h x
  · have h : ((CliffordAlgebra.equivOfIsometry
          (splitIsometry (k := k) (ι := ι) (κ := κ))).symm.toAlgHom).comp
          (CliffordAlgebra.map (QuadraticMap.Isometry.inr _ _)) =
        ExteriorAlgebra.map rightVec := by
      ext v
      simp [CliffordAlgebra.equivOfIsometry, splitIsometry, rightVec]; rfl
    exact AlgHom.congr_fun h y

end BoundaryOnly.FormalObstruction.ExteriorSplit

end
end

end OAI
