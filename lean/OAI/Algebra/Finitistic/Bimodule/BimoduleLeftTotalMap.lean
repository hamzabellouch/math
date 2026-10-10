import OAI.Algebra.Finitistic.Bimodule.BimoduleTensorAcross
import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalDifferential

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P P' P'' : BiComplex k B} (f : P ⟶ P')
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The actual tensor map induced by a bimodule-complex morphism in each bidegree. -/
def leftTermMap (a q : ℤ) : Term k B P Z a q →ₗ[B] Term k B P' Z a q :=
  tensorAcross (f.f a) (𝟙 (Z.X q))

theorem leftTermMap_horizontal (n m a b : ℤ) (h : n+1=m) (hab : a+1=b) :
    (leftTermMap f Z b (m + -b)).comp (horizontalBetween k B P Z n m a b h hab) =
      (horizontalBetween k B P' Z n m a b h hab).comp (leftTermMap f Z a (n + -a)) := by
  unfold horizontalBetween leftTermMap
  rw [← tensorAcross_eq_termMap, ← tensorAcross_eq_termMap,
    tensorAcross_comp,tensorAcross_comp]
  simp only [Category.comp_id,Category.id_comp]
  rw [f.comm]

theorem leftTermMap_entry (n m a b : ℤ) (h : n+1=m) :
    (leftTermMap f Z b (m + -b)).comp (entryBetween k B P Z n m a b h) =
      (entryBetween k B P' Z n m a b h).comp (leftTermMap f Z a (n + -a)) := by
  unfold entryBetween
  split_ifs with hab
  · exact leftTermMap_horizontal f Z n m a b h hab
  · simp

theorem leftTermMap_vertical (n m a : ℤ) (x : Term k B P Z a (n + -a)) :
    leftTermMap f Z a (m + -a)
      (((ComplexTensor.column k B (right k B P) Z a).d n m).hom x) =
      ((ComplexTensor.column k B (right k B P') Z a).d n m).hom
        (leftTermMap f Z a (n + -a) x) := by
  let L := (leftTermMap f Z a (m + -a)).toAddMonoidHom.comp
    ((ComplexTensor.column k B (right k B P) Z a).d n m).hom.toAddMonoidHom
  let R := ((ComplexTensor.column k B (right k B P') Z a).d n m).hom.toAddMonoidHom.comp
    (leftTermMap f Z a (n + -a)).toAddMonoidHom
  induction x using BalancedTensor.induction_on with
  | hz => exact L.map_zero.trans R.map_zero.symm
  | ht x y =>
    rw [ComplexTensor.column_d,ComplexTensor.column_d]
    change leftTermMap f Z a (m + -a)
      ((-a).negOnePow • BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P.X a))
        (ComplexTensor.leftTerm k B Z (m + -a)) x ((Z.d (n + -a) (m + -a)).hom y)) =
        (-a).negOnePow • BalancedTensor.mk k B (BimoduleBalancedTensor.Input k B (P'.X a))
        (ComplexTensor.leftTerm k B Z (m + -a)) ((f.f a).hom x) ((Z.d (n + -a) (m + -a)).hom y)
    simp only [Units.smul_def, map_zsmul]
    rfl
  | ha x y hx hy =>
    exact (L.map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

def leftTotalMapF (n : ℤ) : TotalTerm k B P p Z n →ₗ[B] TotalTerm k B P' p Z n where
  toFun x i := leftTermMap f Z (p i) (n + -(p i)) (x i)
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' b x := by
    funext i
    exact (leftTermMap f Z (p i) (n + -(p i))).map_smul b (x i)

/-- Tensoring an actual bimodule chain map gives an actual B-linear total chain map. -/
def leftTotalMap : total k B P p hp Z ⟶ total k B P' p hp Z where
  f n := ModuleCat.ofHom (leftTotalMapF f Z p n)
  comm' n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    change ((total k B P' p hp Z).d n m).hom (leftTotalMapF f Z p n x) j =
      leftTermMap f Z (p j) (m + -(p j)) (((total k B P p hp Z).d n m).hom x j)
    erw [total_d_apply k B P' Z p hp n m h, total_d_apply k B P Z p hp n m h,
      map_add, map_sum]
    congr 1
    · exact (leftTermMap_vertical f Z n m (p j) (x j)).symm
    · apply Finset.sum_congr rfl
      intro i _
      exact (LinearMap.congr_fun (leftTermMap_entry f Z n m (p i) (p j) h) (x i)).symm

@[simp] theorem leftTotalMap_apply (n : ℤ) (x : TotalTerm k B P p Z n) (i : Fin l) :
    ((leftTotalMap f Z p hp).f n).hom x i = leftTermMap f Z (p i) (n + -(p i)) (x i) := rfl
end LittleFinitistic.BimoduleTotal

end

end OAI
