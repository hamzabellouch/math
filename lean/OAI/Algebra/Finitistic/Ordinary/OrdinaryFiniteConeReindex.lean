import OAI.Algebra.Finitistic.Ordinary.OrdinaryConeCoordinates
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFiniteTotalMaps

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K L : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)
variable (δ : Differential K) (ε : Differential L)
variable (f : ∀ i, K i ⟶ L i)
variable (hc : ∀ n,
    (ε.d n).comp (componentMap K L f n) = (componentMap K L f (n+1)).comp (δ.d n))

abbrev coneColumn (i : Fin l) := CochainComplex.mappingCone (f i)
abbrev totalCone := CochainComplex.mappingCone (complexMap K L δ ε f hc)

/-- Distribution of a binary module product over the finite family of columns. -/
def pairEquiv (n : ℤ) : (term K (n+1) × term L n) ≃ₗ[R] (∀ i, (K i).X (n+1) × (L i).X n) where
  toFun z i := (z.1 i,z.2 i)
  invFun z := (fun i => (z i).1,fun i => (z i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reindex the actual cone of a total map into the actual cones of its column maps. -/
def coneEquiv (n : ℤ) : (totalCone K L δ ε f hc).X n ≃ₗ[R] term (coneColumn K L f) n :=
  (ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n).trans
    ((pairEquiv K L n).trans
      (LinearEquiv.piCongrRight (fun i => (ConeCoordinates.coordinateEquiv (f i) n).symm)))

@[simp] theorem coneEquiv_coordinate (n : ℤ) (z : (totalCone K L δ ε f hc).X n) (i : Fin l) :
    ConeCoordinates.coordinateEquiv (f i) n (coneEquiv K L δ ε f hc n z i) =
      ((ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n z).1 i,
       (ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n z).2 i) := by
  exact (ConeCoordinates.coordinateEquiv (f i) n).apply_symm_apply _

@[simp] theorem coneEquiv_symm_coordinate (n : ℤ) (z : term (coneColumn K L f) n) (i : Fin l) :
    ((ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n ((coneEquiv K L δ ε f hc n).symm z)).1 i,
     (ConeCoordinates.coordinateEquiv (complexMap K L δ ε f hc) n ((coneEquiv K L δ ε f hc n).symm z)).2 i) =
      ConeCoordinates.coordinateEquiv (f i) n (z i) := by
  have hh := coneEquiv_coordinate K L δ ε f hc n ((coneEquiv K L δ ε f hc n).symm z) i
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

/-- Transport the genuine cone differential through this coordinate equivalence. -/
def coneDifferential (n : ℤ) : term (coneColumn K L f) n →ₗ[R] term (coneColumn K L f) (n+1) :=
  (coneEquiv K L δ ε f hc (n+1)).toLinearMap.comp
    (((totalCone K L δ ε f hc).d n (n+1)).hom.comp (coneEquiv K L δ ε f hc n).symm.toLinearMap)

theorem coneDifferential_square (n : ℤ) :
    (coneDifferential K L δ ε f hc (n+1)).comp (coneDifferential K L δ ε f hc n) = 0 := by
  apply LinearMap.ext
  intro z
  change coneEquiv K L δ ε f hc ((n+1)+1)
    (((totalCone K L δ ε f hc).d (n+1) ((n+1)+1)).hom
      ((coneEquiv K L δ ε f hc (n+1)).symm
        (coneEquiv K L δ ε f hc (n+1)
          (((totalCone K L δ ε f hc).d n (n+1)).hom ((coneEquiv K L δ ε f hc n).symm z))))) = 0
  rw [LinearEquiv.symm_apply_apply]
  have hh := congrArg (fun g => g.hom ((coneEquiv K L δ ε f hc n).symm z))
    ((totalCone K L δ ε f hc).d_comp_d n (n+1) ((n+1)+1))
  change ((totalCone K L δ ε f hc).d (n+1) ((n+1)+1)).hom
    (((totalCone K L δ ε f hc).d n (n+1)).hom ((coneEquiv K L δ ε f hc n).symm z)) = 0 at hh
  rw [hh,map_zero]
end LittleFinitistic.FiniteColumnComplex

end

end OAI
