import OAI.Algebra.AuslanderReiten.HomComplex.FiniteFullHomExt
import OAI.Algebra.AuslanderReiten.HomComplex.TensorFullHomZero
import OAI.Algebra.AuslanderReiten.Ext.NativeExtZero

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
open CompleteComparison
variable [HasDerivedCategory (ModuleCat.{u} (A k q))]

def simpleExtZeroEquiv (hq1 : 1+q ≠ 0) : k ≃ₗ[k] Ext (Simple q) (Simple q) 0 :=
  (simpleEndEquiv q hq1).symm.trans (nativeExtZeroEquiv (Simple q) (Simple q))

omit [CharP k 2] [HasDerivedCategory (ModuleCat.{u} (A k q))] in
@[simp]
theorem simpleExtZeroEquiv_one (hq1 : 1+q ≠ 0) :
    simpleExtZeroEquiv q hq1 1 = Ext.mk₀ (𝟙 (Simple q)) := by
  unfold simpleExtZeroEquiv
  rw [LinearEquiv.trans_apply, nativeExtZeroEquiv_apply]
  congr 1
  apply ModuleCat.hom_ext
  change (1:k) • (LinearMap.id : Simple q →ₗ[A k q] Simple q) = LinearMap.id
  exact one_smul k _

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
theorem fullHomZero_eq_scalar (hq1 : 1+q ≠ 0)
    (x : CohomologyClass (simpleComplete q) (simpleComplete q) 0) :
    x = fullHomZeroScalarEquiv q hq1 x • fullHomIdentity (simpleComplete q) := by
  apply (fullHomZeroScalarEquiv q hq1).injective
  rw [map_smul]
  change _ = _ • fullHomZeroScalarEquiv q hq1 (CohomologyClass.mk (Cocycle.ofHom (𝟙 _)))
  rw [fullHomZeroScalarEquiv_identity]
  exact (mul_one _).symm

def fullNonnegativeExtEquiv (hq1 : 1+q ≠ 0) : (n : ℕ) →
    CohomologyClass (simpleComplete q) (simpleComplete q) (n:ℤ) ≃ₗ[k] Ext (Simple q) (Simple q) n
  | 0 => (fullHomZeroScalarEquiv q hq1).trans (simpleExtZeroEquiv q hq1)
  | n+1 => FiniteLeftModule.fullPositiveModuleExtEquiv (AFrobeniusTrace k q) (simpleFiniteModule q) n

omit [HasDerivedCategory (ModuleCat.{u} (A k q))] in
@[simp]
theorem fullNonnegativeExtEquiv_identity (hq1 : 1+q ≠ 0) :
    fullNonnegativeExtEquiv q hq1 0 (fullHomIdentity (simpleComplete q)) = Ext.mk₀ (𝟙 (Simple q)) := by
  change simpleExtZeroEquiv q hq1 (fullHomZeroScalarEquiv q hq1
    (CohomologyClass.mk (Cocycle.ofHom (𝟙 _)))) = _
  rw [fullHomZeroScalarEquiv_identity, simpleExtZeroEquiv_one]

theorem fullNonnegativeExtEquiv_product_of_eq (hq1 : 1+q ≠ 0) (n m r : ℕ) (hr : n+m=r)
    (x : CohomologyClass (simpleComplete q) (simpleComplete q) (n:ℤ))
    (y : CohomologyClass (simpleComplete q) (simpleComplete q) (m:ℤ)) :
    fullNonnegativeExtEquiv q hq1 r
      (TateKoszul.degreeEquiv (k := k) (CohomologyClass (simpleComplete q) (simpleComplete q))
        (show (n:ℤ)+(m:ℤ)=(r:ℤ) by omega) (fullHomProduct x y)) =
      (fullNonnegativeExtEquiv q hq1 n x).comp (fullNonnegativeExtEquiv q hq1 m y) hr := by
  cases n with
  | zero =>
      obtain rfl : r=m := by omega
      rw [fullHomZero_eq_scalar q hq1 x]
      simp only [fullHomProduct_smul_left, map_smul,
        fullNonnegativeExtEquiv_identity, Ext.smul_comp, Ext.mk₀_id_comp]
      erw [fullHomProduct_identity_left]
  | succ n =>
      cases m with
      | zero =>
          obtain rfl : r=n+1 := by omega
          rw [fullHomZero_eq_scalar q hq1 y]
          simp only [fullHomProduct_smul_right, map_smul,
            fullNonnegativeExtEquiv_identity, Ext.comp_smul, Ext.comp_mk₀_id]
          erw [fullHomProduct_identity_right]
      | succ m =>
          obtain rfl : r=n+1+m+1 := by omega
          exact FiniteLeftModule.fullPositiveModuleExtEquiv_product (AFrobeniusTrace k q)
            (simpleFiniteModule q) n m x y

theorem fullNonnegativeExtEquiv_product (hq1 : 1+q ≠ 0) (n m : ℕ)
    (x : CohomologyClass (simpleComplete q) (simpleComplete q) (n:ℤ))
    (y : CohomologyClass (simpleComplete q) (simpleComplete q) (m:ℤ)) :
    fullNonnegativeExtEquiv q hq1 (n+m)
      (TateKoszul.degreeEquiv (k := k) (CohomologyClass (simpleComplete q) (simpleComplete q))
        (show (n:ℤ)+(m:ℤ)=((n+m:ℕ):ℤ) by omega) (fullHomProduct x y)) =
      (fullNonnegativeExtEquiv q hq1 n x).comp (fullNonnegativeExtEquiv q hq1 m y) rfl :=
  fullNonnegativeExtEquiv_product_of_eq q hq1 n m (n+m) rfl x y

end ArExplicit.A

end

end OAI
